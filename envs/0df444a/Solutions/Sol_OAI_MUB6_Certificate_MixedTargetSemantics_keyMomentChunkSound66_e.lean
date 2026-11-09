-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound66_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:01:17.925629+00:00
-- url     : https://prove2.me/submissions/7128929c-acb8-4572-8b0e-2f056dbbb5c2

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical324
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41536 raw41536Labels = mixedMoment B node0 node0Labels := by
  calc
    mixedMoment B raw41536 raw41536Labels = mixedMoment B raw41536step0 raw41536step0Labels := by
      have hz : ∀ j, raw41536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41536step0 = (fun i j => raw41536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41536step0 raw41536; decide +kernel
      have hl : raw41536step0Labels = raw41536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41536 raw41536Labels permutation346 hz
    mixedMoment B raw41536step0 raw41536step0Labels = mixedMoment B raw41536step1 raw41536step1Labels := by
      have hz : ∀ j, raw41536step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41536step1 = (fun i j => raw41536step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41536step1 raw41536step0; decide +kernel
      have hl : raw41536step1Labels = raw41536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41536step0 raw41536step0Labels permutation56 hz
    mixedMoment B raw41536step1 raw41536step1Labels = mixedMoment B raw41536step2 raw41536step2Labels := by
      have hz : ∀ i, raw41536step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw41536step2 = (fun i j => raw41536step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw41536step2 raw41536step1; decide +kernel
      have hl : raw41536step2Labels = (fun j => raw41536step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw41536step1 raw41536step1Labels permutation6 hz
    mixedMoment B raw41536step2 raw41536step2Labels = mixedMoment B raw41536step3 raw41536step3Labels := by
      have ha : raw41536step3 = raw41536step2 := by apply Matrix.ext; unfold raw41536step3 raw41536step2; decide +kernel
      have hl : raw41536step2Labels = labelEmbedding0 ∘ raw41536step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41536step2 raw41536step2Labels raw41536step3Labels labelEmbedding0 hl
    _ = mixedMoment B node0 node0Labels := by rfl

theorem canonical41537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41537 raw41537Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw41537 raw41537Labels = mixedMoment B raw41537step0 raw41537step0Labels := by
      have hz : ∀ j, raw41537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41537step0 = (fun i j => raw41537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41537step0 raw41537; decide +kernel
      have hl : raw41537step0Labels = raw41537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41537 raw41537Labels permutation346 hz
    mixedMoment B raw41537step0 raw41537step0Labels = mixedMoment B raw41537step1 raw41537step1Labels := by
      have hz : ∀ j, raw41537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41537step1 = (fun i j => raw41537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41537step1 raw41537step0; decide +kernel
      have hl : raw41537step1Labels = raw41537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41537step0 raw41537step0Labels permutation56 hz
    mixedMoment B raw41537step1 raw41537step1Labels = mixedMoment B raw41537step2 raw41537step2Labels := by
      have hz : ∀ i, raw41537step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw41537step2 = (fun i j => raw41537step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw41537step2 raw41537step1; decide +kernel
      have hl : raw41537step2Labels = (fun j => raw41537step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw41537step1 raw41537step1Labels permutation6 hz
    mixedMoment B raw41537step2 raw41537step2Labels = mixedMoment B raw41537step3 raw41537step3Labels := by
      have ha : raw41537step3 = raw41537step2 := by apply Matrix.ext; unfold raw41537step3 raw41537step2; decide +kernel
      have hl : raw41537step2Labels = labelEmbedding3 ∘ raw41537step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41537step2 raw41537step2Labels raw41537step3Labels labelEmbedding3 hl
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical41538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41538 raw41538Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw41538 raw41538Labels = mixedMoment B raw41538step0 raw41538step0Labels := by
      have hz : ∀ j, raw41538 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41538step0 = (fun i j => raw41538 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41538step0 raw41538; decide +kernel
      have hl : raw41538step0Labels = raw41538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41538 raw41538Labels permutation265 hz
    mixedMoment B raw41538step0 raw41538step0Labels = mixedMoment B raw41538step1 raw41538step1Labels := by
      have ha : raw41538step1 = (fun i j => raw41538step0 (permutation54 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41538step1 raw41538step0; decide +kernel
      have hl : raw41538step1Labels = raw41538step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41538step0 raw41538step0Labels permutation54 permutation4
    mixedMoment B raw41538step1 raw41538step1Labels = mixedMoment B raw41538step2 raw41538step2Labels := by
      have ha : raw41538step2 = -raw41538step1 := by apply Matrix.ext; change ∀ i j, raw41538step2 i j = -(raw41538step1 i j); unfold raw41538step2 raw41538step1; decide +kernel
      have hl : raw41538step2Labels = raw41538step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41538step2 raw41538step2Labels = mixedMoment B raw41538step3 raw41538step3Labels := by
      have ha : raw41538step3 = raw41538step2 := by apply Matrix.ext; unfold raw41538step3 raw41538step2; decide +kernel
      have hl : raw41538step2Labels = labelEmbedding1 ∘ raw41538step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41538step2 raw41538step2Labels raw41538step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

theorem canonical41539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41539 raw41539Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw41539 raw41539Labels = mixedMoment B raw41539step0 raw41539step0Labels := by
      have hz : ∀ j, raw41539 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41539step0 = (fun i j => raw41539 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41539step0 raw41539; decide +kernel
      have hl : raw41539step0Labels = raw41539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41539 raw41539Labels permutation265 hz
    mixedMoment B raw41539step0 raw41539step0Labels = mixedMoment B raw41539step1 raw41539step1Labels := by
      have ha : raw41539step1 = (fun i j => raw41539step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41539step1 raw41539step0; decide +kernel
      have hl : raw41539step1Labels = raw41539step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41539step0 raw41539step0Labels permutation32 permutation3
    mixedMoment B raw41539step1 raw41539step1Labels = mixedMoment B raw41539step2 raw41539step2Labels := by
      have ha : raw41539step2 = raw41539step1 := by apply Matrix.ext; unfold raw41539step2 raw41539step1; decide +kernel
      have hl : raw41539step1Labels = labelEmbedding7 ∘ raw41539step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41539step1 raw41539step1Labels raw41539step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical41540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41540 raw41540Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw41540 raw41540Labels = mixedMoment B raw41540step0 raw41540step0Labels := by
      have hz : ∀ j, raw41540 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41540step0 = (fun i j => raw41540 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41540step0 raw41540; decide +kernel
      have hl : raw41540step0Labels = raw41540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41540 raw41540Labels permutation265 hz
    mixedMoment B raw41540step0 raw41540step0Labels = mixedMoment B raw41540step1 raw41540step1Labels := by
      have ha : raw41540step1 = (fun i j => raw41540step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41540step1 raw41540step0; decide +kernel
      have hl : raw41540step1Labels = raw41540step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41540step0 raw41540step0Labels permutation40 permutation4
    mixedMoment B raw41540step1 raw41540step1Labels = mixedMoment B raw41540step2 raw41540step2Labels := by
      have ha : raw41540step2 = -raw41540step1 := by apply Matrix.ext; change ∀ i j, raw41540step2 i j = -(raw41540step1 i j); unfold raw41540step2 raw41540step1; decide +kernel
      have hl : raw41540step2Labels = raw41540step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41540step2 raw41540step2Labels = mixedMoment B raw41540step3 raw41540step3Labels := by
      have ha : raw41540step3 = raw41540step2 := by apply Matrix.ext; unfold raw41540step3 raw41540step2; decide +kernel
      have hl : raw41540step2Labels = labelEmbedding1 ∘ raw41540step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41540step2 raw41540step2Labels raw41540step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

theorem canonical41541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41541 raw41541Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw41541 raw41541Labels = mixedMoment B raw41541step0 raw41541step0Labels := by
      have hz : ∀ j, raw41541 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41541step0 = (fun i j => raw41541 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41541step0 raw41541; decide +kernel
      have hl : raw41541step0Labels = raw41541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41541 raw41541Labels permutation265 hz
    mixedMoment B raw41541step0 raw41541step0Labels = mixedMoment B raw41541step1 raw41541step1Labels := by
      have ha : raw41541step1 = (fun i j => raw41541step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41541step1 raw41541step0; decide +kernel
      have hl : raw41541step1Labels = raw41541step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41541step0 raw41541step0Labels permutation40 permutation5
    mixedMoment B raw41541step1 raw41541step1Labels = mixedMoment B raw41541step2 raw41541step2Labels := by
      have ha : raw41541step2 = -raw41541step1 := by apply Matrix.ext; change ∀ i j, raw41541step2 i j = -(raw41541step1 i j); unfold raw41541step2 raw41541step1; decide +kernel
      have hl : raw41541step2Labels = raw41541step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41541step2 raw41541step2Labels = mixedMoment B raw41541step3 raw41541step3Labels := by
      have ha : raw41541step3 = raw41541step2 := by apply Matrix.ext; unfold raw41541step3 raw41541step2; decide +kernel
      have hl : raw41541step2Labels = labelEmbedding9 ∘ raw41541step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41541step2 raw41541step2Labels raw41541step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical41542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41542 raw41542Labels = mixedMoment B node3228 node3228Labels := by
  calc
    mixedMoment B raw41542 raw41542Labels = mixedMoment B raw41542step0 raw41542step0Labels := by
      have hz : ∀ j, raw41542 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41542step0 = (fun i j => raw41542 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41542step0 raw41542; decide +kernel
      have hl : raw41542step0Labels = raw41542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41542 raw41542Labels permutation265 hz
    mixedMoment B raw41542step0 raw41542step0Labels = mixedMoment B raw41542step1 raw41542step1Labels := by
      have ha : raw41542step1 = (fun i j => raw41542step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41542step1 raw41542step0; decide +kernel
      have hl : raw41542step1Labels = raw41542step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41542step0 raw41542step0Labels permutation35 permutation2
    mixedMoment B raw41542step1 raw41542step1Labels = mixedMoment B raw41542step2 raw41542step2Labels := by
      have ha : raw41542step2 = raw41542step1 := by apply Matrix.ext; unfold raw41542step2 raw41542step1; decide +kernel
      have hl : raw41542step1Labels = labelEmbedding1 ∘ raw41542step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41542step1 raw41542step1Labels raw41542step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3228 node3228Labels := by rfl

theorem canonical41543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41543 raw41543Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw41543 raw41543Labels = mixedMoment B raw41543step0 raw41543step0Labels := by
      have hz : ∀ j, raw41543 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41543step0 = (fun i j => raw41543 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41543step0 raw41543; decide +kernel
      have hl : raw41543step0Labels = raw41543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41543 raw41543Labels permutation265 hz
    mixedMoment B raw41543step0 raw41543step0Labels = mixedMoment B raw41543step1 raw41543step1Labels := by
      have ha : raw41543step1 = (fun i j => raw41543step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41543step1 raw41543step0; decide +kernel
      have hl : raw41543step1Labels = raw41543step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41543step0 raw41543step0Labels permutation32 permutation3
    mixedMoment B raw41543step1 raw41543step1Labels = mixedMoment B raw41543step2 raw41543step2Labels := by
      have ha : raw41543step2 = raw41543step1 := by apply Matrix.ext; unfold raw41543step2 raw41543step1; decide +kernel
      have hl : raw41543step1Labels = labelEmbedding7 ∘ raw41543step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41543step1 raw41543step1Labels raw41543step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4893 node4893Labels := by rfl

theorem canonical41544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41544 raw41544Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw41544 raw41544Labels = mixedMoment B raw41544step0 raw41544step0Labels := by
      have hz : ∀ j, raw41544 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41544step0 = (fun i j => raw41544 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41544step0 raw41544; decide +kernel
      have hl : raw41544step0Labels = raw41544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41544 raw41544Labels permutation265 hz
    mixedMoment B raw41544step0 raw41544step0Labels = mixedMoment B raw41544step1 raw41544step1Labels := by
      have ha : raw41544step1 = (fun i j => raw41544step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41544step1 raw41544step0; decide +kernel
      have hl : raw41544step1Labels = raw41544step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41544step0 raw41544step0Labels permutation36 permutation2
    mixedMoment B raw41544step1 raw41544step1Labels = mixedMoment B raw41544step2 raw41544step2Labels := by
      have ha : raw41544step2 = raw41544step1 := by apply Matrix.ext; unfold raw41544step2 raw41544step1; decide +kernel
      have hl : raw41544step1Labels = labelEmbedding1 ∘ raw41544step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41544step1 raw41544step1Labels raw41544step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

theorem canonical41545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41545 raw41545Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw41545 raw41545Labels = mixedMoment B raw41545step0 raw41545step0Labels := by
      have hz : ∀ j, raw41545 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41545step0 = (fun i j => raw41545 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41545step0 raw41545; decide +kernel
      have hl : raw41545step0Labels = raw41545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41545 raw41545Labels permutation265 hz
    mixedMoment B raw41545step0 raw41545step0Labels = mixedMoment B raw41545step1 raw41545step1Labels := by
      have ha : raw41545step1 = (fun i j => raw41545step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41545step1 raw41545step0; decide +kernel
      have hl : raw41545step1Labels = raw41545step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41545step0 raw41545step0Labels permutation41 permutation5
    mixedMoment B raw41545step1 raw41545step1Labels = mixedMoment B raw41545step2 raw41545step2Labels := by
      have ha : raw41545step2 = -raw41545step1 := by apply Matrix.ext; change ∀ i j, raw41545step2 i j = -(raw41545step1 i j); unfold raw41545step2 raw41545step1; decide +kernel
      have hl : raw41545step2Labels = raw41545step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41545step2 raw41545step2Labels = mixedMoment B raw41545step3 raw41545step3Labels := by
      have ha : raw41545step3 = raw41545step2 := by apply Matrix.ext; unfold raw41545step3 raw41545step2; decide +kernel
      have hl : raw41545step2Labels = labelEmbedding9 ∘ raw41545step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41545step2 raw41545step2Labels raw41545step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical41546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41546 raw41546Labels = mixedMoment B node3226 node3226Labels := by
  calc
    mixedMoment B raw41546 raw41546Labels = mixedMoment B raw41546step0 raw41546step0Labels := by
      have ha : raw41546step0 = (fun i j => raw41546 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41546step0 raw41546; decide +kernel
      have hl : raw41546step0Labels = raw41546Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41546 raw41546Labels permutation156 permutation2
    mixedMoment B raw41546step0 raw41546step0Labels = mixedMoment B raw41546step1 raw41546step1Labels := by
      have ha : raw41546step1 = raw41546step0 := by apply Matrix.ext; unfold raw41546step1 raw41546step0; decide +kernel
      have hl : raw41546step0Labels = labelEmbedding1 ∘ raw41546step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41546step0 raw41546step0Labels raw41546step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3226 node3226Labels := by rfl

theorem canonical41547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41547 raw41547Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw41547 raw41547Labels = mixedMoment B raw41547step0 raw41547step0Labels := by
      have ha : raw41547step0 = (fun i j => raw41547 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41547step0 raw41547; decide +kernel
      have hl : raw41547step0Labels = raw41547Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41547 raw41547Labels permutation152 permutation3
    mixedMoment B raw41547step0 raw41547step0Labels = mixedMoment B raw41547step1 raw41547step1Labels := by
      have ha : raw41547step1 = raw41547step0 := by apply Matrix.ext; unfold raw41547step1 raw41547step0; decide +kernel
      have hl : raw41547step0Labels = labelEmbedding7 ∘ raw41547step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41547step0 raw41547step0Labels raw41547step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

theorem canonical41548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41548 raw41548Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw41548 raw41548Labels = mixedMoment B raw41548step0 raw41548step0Labels := by
      have hz : ∀ j, raw41548 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41548step0 = (fun i j => raw41548 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41548step0 raw41548; decide +kernel
      have hl : raw41548step0Labels = raw41548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41548 raw41548Labels permutation520 hz
    mixedMoment B raw41548step0 raw41548step0Labels = mixedMoment B raw41548step1 raw41548step1Labels := by
      have hz : ∀ j, raw41548step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41548step1 = (fun i j => raw41548step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41548step1 raw41548step0; decide +kernel
      have hl : raw41548step1Labels = raw41548step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41548step0 raw41548step0Labels permutation104 hz
    mixedMoment B raw41548step1 raw41548step1Labels = mixedMoment B raw41548step2 raw41548step2Labels := by
      have hz : ∀ j, raw41548step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41548step2 = (fun i j => raw41548step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41548step2 raw41548step1; decide +kernel
      have hl : raw41548step2Labels = raw41548step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41548step1 raw41548step1Labels permutation20 hz
    mixedMoment B raw41548step2 raw41548step2Labels = mixedMoment B raw41548step3 raw41548step3Labels := by
      have ha : raw41548step3 = raw41548step2 := by apply Matrix.ext; unfold raw41548step3 raw41548step2; decide +kernel
      have hl : raw41548step2Labels = labelEmbedding1 ∘ raw41548step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41548step2 raw41548step2Labels raw41548step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3114 node3114Labels := by rfl

theorem canonical41549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41549 raw41549Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw41549 raw41549Labels = mixedMoment B raw41549step0 raw41549step0Labels := by
      have hz : ∀ j, raw41549 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41549step0 = (fun i j => raw41549 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41549step0 raw41549; decide +kernel
      have hl : raw41549step0Labels = raw41549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41549 raw41549Labels permutation520 hz
    mixedMoment B raw41549step0 raw41549step0Labels = mixedMoment B raw41549step1 raw41549step1Labels := by
      have hz : ∀ j, raw41549step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41549step1 = (fun i j => raw41549step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41549step1 raw41549step0; decide +kernel
      have hl : raw41549step1Labels = raw41549step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41549step0 raw41549step0Labels permutation104 hz
    mixedMoment B raw41549step1 raw41549step1Labels = mixedMoment B raw41549step2 raw41549step2Labels := by
      have hz : ∀ j, raw41549step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41549step2 = (fun i j => raw41549step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41549step2 raw41549step1; decide +kernel
      have hl : raw41549step2Labels = raw41549step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41549step1 raw41549step1Labels permutation20 hz
    mixedMoment B raw41549step2 raw41549step2Labels = mixedMoment B raw41549step3 raw41549step3Labels := by
      have ha : raw41549step3 = (fun i j => raw41549step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41549step3 raw41549step2; decide +kernel
      have hl : raw41549step3Labels = raw41549step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41549step2 raw41549step2Labels permutation7 permutation3
    mixedMoment B raw41549step3 raw41549step3Labels = mixedMoment B raw41549step4 raw41549step4Labels := by
      have ha : raw41549step4 = -raw41549step3 := by apply Matrix.ext; change ∀ i j, raw41549step4 i j = -(raw41549step3 i j); unfold raw41549step4 raw41549step3; decide +kernel
      have hl : raw41549step4Labels = raw41549step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41549step4 raw41549step4Labels = mixedMoment B raw41549step5 raw41549step5Labels := by
      have ha : raw41549step5 = raw41549step4 := by apply Matrix.ext; unfold raw41549step5 raw41549step4; decide +kernel
      have hl : raw41549step4Labels = labelEmbedding7 ∘ raw41549step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41549step4 raw41549step4Labels raw41549step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

theorem canonical41550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41550 raw41550Labels = mixedMoment B node3113 node3113Labels := by
  calc
    mixedMoment B raw41550 raw41550Labels = mixedMoment B raw41550step0 raw41550step0Labels := by
      have hz : ∀ j, raw41550 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41550step0 = (fun i j => raw41550 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41550step0 raw41550; decide +kernel
      have hl : raw41550step0Labels = raw41550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41550 raw41550Labels permutation434 hz
    mixedMoment B raw41550step0 raw41550step0Labels = mixedMoment B raw41550step1 raw41550step1Labels := by
      have hz : ∀ j, raw41550step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41550step1 = (fun i j => raw41550step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41550step1 raw41550step0; decide +kernel
      have hl : raw41550step1Labels = raw41550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41550step0 raw41550step0Labels permutation80 hz
    mixedMoment B raw41550step1 raw41550step1Labels = mixedMoment B raw41550step2 raw41550step2Labels := by
      have ha : raw41550step2 = raw41550step1 := by apply Matrix.ext; unfold raw41550step2 raw41550step1; decide +kernel
      have hl : raw41550step1Labels = labelEmbedding1 ∘ raw41550step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41550step1 raw41550step1Labels raw41550step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3113 node3113Labels := by rfl

theorem canonical41551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41551 raw41551Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw41551 raw41551Labels = mixedMoment B raw41551step0 raw41551step0Labels := by
      have hz : ∀ j, raw41551 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41551step0 = (fun i j => raw41551 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41551step0 raw41551; decide +kernel
      have hl : raw41551step0Labels = raw41551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41551 raw41551Labels permutation434 hz
    mixedMoment B raw41551step0 raw41551step0Labels = mixedMoment B raw41551step1 raw41551step1Labels := by
      have hz : ∀ j, raw41551step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41551step1 = (fun i j => raw41551step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41551step1 raw41551step0; decide +kernel
      have hl : raw41551step1Labels = raw41551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41551step0 raw41551step0Labels permutation80 hz
    mixedMoment B raw41551step1 raw41551step1Labels = mixedMoment B raw41551step2 raw41551step2Labels := by
      have ha : raw41551step2 = (fun i j => raw41551step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41551step2 raw41551step1; decide +kernel
      have hl : raw41551step2Labels = raw41551step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41551step1 raw41551step1Labels permutation8 permutation3
    mixedMoment B raw41551step2 raw41551step2Labels = mixedMoment B raw41551step3 raw41551step3Labels := by
      have ha : raw41551step3 = raw41551step2 := by apply Matrix.ext; unfold raw41551step3 raw41551step2; decide +kernel
      have hl : raw41551step2Labels = labelEmbedding7 ∘ raw41551step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41551step2 raw41551step2Labels raw41551step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5272 node5272Labels := by rfl

theorem canonical41552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41552 raw41552Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw41552 raw41552Labels = mixedMoment B raw41552step0 raw41552step0Labels := by
      have hz : ∀ j, raw41552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41552step0 = (fun i j => raw41552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41552step0 raw41552; decide +kernel
      have hl : raw41552step0Labels = raw41552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41552 raw41552Labels permutation434 hz
    mixedMoment B raw41552step0 raw41552step0Labels = mixedMoment B raw41552step1 raw41552step1Labels := by
      have hz : ∀ j, raw41552step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41552step1 = (fun i j => raw41552step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41552step1 raw41552step0; decide +kernel
      have hl : raw41552step1Labels = raw41552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41552step0 raw41552step0Labels permutation80 hz
    mixedMoment B raw41552step1 raw41552step1Labels = mixedMoment B raw41552step2 raw41552step2Labels := by
      have ha : raw41552step2 = raw41552step1 := by apply Matrix.ext; unfold raw41552step2 raw41552step1; decide +kernel
      have hl : raw41552step1Labels = labelEmbedding1 ∘ raw41552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41552step1 raw41552step1Labels raw41552step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3112 node3112Labels := by rfl

theorem canonical41553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41553 raw41553Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw41553 raw41553Labels = mixedMoment B raw41553step0 raw41553step0Labels := by
      have hz : ∀ j, raw41553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41553step0 = (fun i j => raw41553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41553step0 raw41553; decide +kernel
      have hl : raw41553step0Labels = raw41553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41553 raw41553Labels permutation434 hz
    mixedMoment B raw41553step0 raw41553step0Labels = mixedMoment B raw41553step1 raw41553step1Labels := by
      have hz : ∀ j, raw41553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41553step1 = (fun i j => raw41553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41553step1 raw41553step0; decide +kernel
      have hl : raw41553step1Labels = raw41553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41553step0 raw41553step0Labels permutation80 hz
    mixedMoment B raw41553step1 raw41553step1Labels = mixedMoment B raw41553step2 raw41553step2Labels := by
      have ha : raw41553step2 = (fun i j => raw41553step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41553step2 raw41553step1; decide +kernel
      have hl : raw41553step2Labels = raw41553step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41553step1 raw41553step1Labels permutation8 permutation3
    mixedMoment B raw41553step2 raw41553step2Labels = mixedMoment B raw41553step3 raw41553step3Labels := by
      have ha : raw41553step3 = raw41553step2 := by apply Matrix.ext; unfold raw41553step3 raw41553step2; decide +kernel
      have hl : raw41553step2Labels = labelEmbedding7 ∘ raw41553step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41553step2 raw41553step2Labels raw41553step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

theorem canonical41554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41554 raw41554Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw41554 raw41554Labels = mixedMoment B raw41554step0 raw41554step0Labels := by
      have hz : ∀ j, raw41554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41554step0 = (fun i j => raw41554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41554step0 raw41554; decide +kernel
      have hl : raw41554step0Labels = raw41554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41554 raw41554Labels permutation434 hz
    mixedMoment B raw41554step0 raw41554step0Labels = mixedMoment B raw41554step1 raw41554step1Labels := by
      have hz : ∀ j, raw41554step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41554step1 = (fun i j => raw41554step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41554step1 raw41554step0; decide +kernel
      have hl : raw41554step1Labels = raw41554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41554step0 raw41554step0Labels permutation80 hz
    mixedMoment B raw41554step1 raw41554step1Labels = mixedMoment B raw41554step2 raw41554step2Labels := by
      have ha : raw41554step2 = raw41554step1 := by apply Matrix.ext; unfold raw41554step2 raw41554step1; decide +kernel
      have hl : raw41554step1Labels = labelEmbedding1 ∘ raw41554step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41554step1 raw41554step1Labels raw41554step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3110 node3110Labels := by rfl

theorem canonical41555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41555 raw41555Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw41555 raw41555Labels = mixedMoment B raw41555step0 raw41555step0Labels := by
      have hz : ∀ j, raw41555 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41555step0 = (fun i j => raw41555 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41555step0 raw41555; decide +kernel
      have hl : raw41555step0Labels = raw41555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41555 raw41555Labels permutation434 hz
    mixedMoment B raw41555step0 raw41555step0Labels = mixedMoment B raw41555step1 raw41555step1Labels := by
      have hz : ∀ j, raw41555step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41555step1 = (fun i j => raw41555step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41555step1 raw41555step0; decide +kernel
      have hl : raw41555step1Labels = raw41555step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41555step0 raw41555step0Labels permutation80 hz
    mixedMoment B raw41555step1 raw41555step1Labels = mixedMoment B raw41555step2 raw41555step2Labels := by
      have ha : raw41555step2 = (fun i j => raw41555step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41555step2 raw41555step1; decide +kernel
      have hl : raw41555step2Labels = raw41555step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41555step1 raw41555step1Labels permutation8 permutation3
    mixedMoment B raw41555step2 raw41555step2Labels = mixedMoment B raw41555step3 raw41555step3Labels := by
      have ha : raw41555step3 = raw41555step2 := by apply Matrix.ext; unfold raw41555step3 raw41555step2; decide +kernel
      have hl : raw41555step2Labels = labelEmbedding7 ∘ raw41555step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41555step2 raw41555step2Labels raw41555step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical41556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41556 raw41556Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw41556 raw41556Labels = mixedMoment B raw41556step0 raw41556step0Labels := by
      have hz : ∀ j, raw41556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41556step0 = (fun i j => raw41556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41556step0 raw41556; decide +kernel
      have hl : raw41556step0Labels = raw41556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41556 raw41556Labels permutation434 hz
    mixedMoment B raw41556step0 raw41556step0Labels = mixedMoment B raw41556step1 raw41556step1Labels := by
      have hz : ∀ j, raw41556step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41556step1 = (fun i j => raw41556step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41556step1 raw41556step0; decide +kernel
      have hl : raw41556step1Labels = raw41556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41556step0 raw41556step0Labels permutation80 hz
    mixedMoment B raw41556step1 raw41556step1Labels = mixedMoment B raw41556step2 raw41556step2Labels := by
      have ha : raw41556step2 = (fun i j => raw41556step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41556step2 raw41556step1; decide +kernel
      have hl : raw41556step2Labels = raw41556step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41556step1 raw41556step1Labels permutation25 permutation4
    mixedMoment B raw41556step2 raw41556step2Labels = mixedMoment B raw41556step3 raw41556step3Labels := by
      have ha : raw41556step3 = raw41556step2 := by apply Matrix.ext; unfold raw41556step3 raw41556step2; decide +kernel
      have hl : raw41556step2Labels = labelEmbedding1 ∘ raw41556step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41556step2 raw41556step2Labels raw41556step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2777 node2777Labels := by rfl

theorem canonical41557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41557 raw41557Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw41557 raw41557Labels = mixedMoment B raw41557step0 raw41557step0Labels := by
      have hz : ∀ j, raw41557 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41557step0 = (fun i j => raw41557 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41557step0 raw41557; decide +kernel
      have hl : raw41557step0Labels = raw41557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41557 raw41557Labels permutation434 hz
    mixedMoment B raw41557step0 raw41557step0Labels = mixedMoment B raw41557step1 raw41557step1Labels := by
      have hz : ∀ j, raw41557step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41557step1 = (fun i j => raw41557step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41557step1 raw41557step0; decide +kernel
      have hl : raw41557step1Labels = raw41557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41557step0 raw41557step0Labels permutation80 hz
    mixedMoment B raw41557step1 raw41557step1Labels = mixedMoment B raw41557step2 raw41557step2Labels := by
      have ha : raw41557step2 = (fun i j => raw41557step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41557step2 raw41557step1; decide +kernel
      have hl : raw41557step2Labels = raw41557step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41557step1 raw41557step1Labels permutation8 permutation3
    mixedMoment B raw41557step2 raw41557step2Labels = mixedMoment B raw41557step3 raw41557step3Labels := by
      have ha : raw41557step3 = raw41557step2 := by apply Matrix.ext; unfold raw41557step3 raw41557step2; decide +kernel
      have hl : raw41557step2Labels = labelEmbedding7 ∘ raw41557step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41557step2 raw41557step2Labels raw41557step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

theorem canonical41558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41558 raw41558Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw41558 raw41558Labels = mixedMoment B raw41558step0 raw41558step0Labels := by
      have hz : ∀ j, raw41558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41558step0 = (fun i j => raw41558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41558step0 raw41558; decide +kernel
      have hl : raw41558step0Labels = raw41558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41558 raw41558Labels permutation346 hz
    mixedMoment B raw41558step0 raw41558step0Labels = mixedMoment B raw41558step1 raw41558step1Labels := by
      have ha : raw41558step1 = (fun i j => raw41558step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41558step1 raw41558step0; decide +kernel
      have hl : raw41558step1Labels = raw41558step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41558step0 raw41558step0Labels permutation38 permutation2
    mixedMoment B raw41558step1 raw41558step1Labels = mixedMoment B raw41558step2 raw41558step2Labels := by
      have ha : raw41558step2 = raw41558step1 := by apply Matrix.ext; unfold raw41558step2 raw41558step1; decide +kernel
      have hl : raw41558step1Labels = labelEmbedding1 ∘ raw41558step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41558step1 raw41558step1Labels raw41558step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3089 node3089Labels := by rfl

theorem canonical41559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41559 raw41559Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw41559 raw41559Labels = mixedMoment B raw41559step0 raw41559step0Labels := by
      have hz : ∀ j, raw41559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41559step0 = (fun i j => raw41559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41559step0 raw41559; decide +kernel
      have hl : raw41559step0Labels = raw41559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41559 raw41559Labels permutation346 hz
    mixedMoment B raw41559step0 raw41559step0Labels = mixedMoment B raw41559step1 raw41559step1Labels := by
      have ha : raw41559step1 = (fun i j => raw41559step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41559step1 raw41559step0; decide +kernel
      have hl : raw41559step1Labels = raw41559step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41559step0 raw41559step0Labels permutation32 permutation3
    mixedMoment B raw41559step1 raw41559step1Labels = mixedMoment B raw41559step2 raw41559step2Labels := by
      have ha : raw41559step2 = raw41559step1 := by apply Matrix.ext; unfold raw41559step2 raw41559step1; decide +kernel
      have hl : raw41559step1Labels = labelEmbedding7 ∘ raw41559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41559step1 raw41559step1Labels raw41559step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical41560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41560 raw41560Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw41560 raw41560Labels = mixedMoment B raw41560step0 raw41560step0Labels := by
      have hz : ∀ j, raw41560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41560step0 = (fun i j => raw41560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41560step0 raw41560; decide +kernel
      have hl : raw41560step0Labels = raw41560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41560 raw41560Labels permutation346 hz
    mixedMoment B raw41560step0 raw41560step0Labels = mixedMoment B raw41560step1 raw41560step1Labels := by
      have ha : raw41560step1 = (fun i j => raw41560step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41560step1 raw41560step0; decide +kernel
      have hl : raw41560step1Labels = raw41560step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41560step0 raw41560step0Labels permutation38 permutation2
    mixedMoment B raw41560step1 raw41560step1Labels = mixedMoment B raw41560step2 raw41560step2Labels := by
      have ha : raw41560step2 = raw41560step1 := by apply Matrix.ext; unfold raw41560step2 raw41560step1; decide +kernel
      have hl : raw41560step1Labels = labelEmbedding1 ∘ raw41560step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41560step1 raw41560step1Labels raw41560step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3088 node3088Labels := by rfl

theorem canonical41561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41561 raw41561Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw41561 raw41561Labels = mixedMoment B raw41561step0 raw41561step0Labels := by
      have hz : ∀ j, raw41561 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41561step0 = (fun i j => raw41561 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41561step0 raw41561; decide +kernel
      have hl : raw41561step0Labels = raw41561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41561 raw41561Labels permutation346 hz
    mixedMoment B raw41561step0 raw41561step0Labels = mixedMoment B raw41561step1 raw41561step1Labels := by
      have ha : raw41561step1 = (fun i j => raw41561step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41561step1 raw41561step0; decide +kernel
      have hl : raw41561step1Labels = raw41561step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41561step0 raw41561step0Labels permutation32 permutation3
    mixedMoment B raw41561step1 raw41561step1Labels = mixedMoment B raw41561step2 raw41561step2Labels := by
      have ha : raw41561step2 = raw41561step1 := by apply Matrix.ext; unfold raw41561step2 raw41561step1; decide +kernel
      have hl : raw41561step1Labels = labelEmbedding7 ∘ raw41561step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41561step1 raw41561step1Labels raw41561step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical41562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41562 raw41562Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw41562 raw41562Labels = mixedMoment B raw41562step0 raw41562step0Labels := by
      have hz : ∀ j, raw41562 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41562step0 = (fun i j => raw41562 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41562step0 raw41562; decide +kernel
      have hl : raw41562step0Labels = raw41562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41562 raw41562Labels permutation346 hz
    mixedMoment B raw41562step0 raw41562step0Labels = mixedMoment B raw41562step1 raw41562step1Labels := by
      have ha : raw41562step1 = (fun i j => raw41562step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41562step1 raw41562step0; decide +kernel
      have hl : raw41562step1Labels = raw41562step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41562step0 raw41562step0Labels permutation38 permutation2
    mixedMoment B raw41562step1 raw41562step1Labels = mixedMoment B raw41562step2 raw41562step2Labels := by
      have ha : raw41562step2 = raw41562step1 := by apply Matrix.ext; unfold raw41562step2 raw41562step1; decide +kernel
      have hl : raw41562step1Labels = labelEmbedding1 ∘ raw41562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41562step1 raw41562step1Labels raw41562step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3086 node3086Labels := by rfl

theorem canonical41563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41563 raw41563Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw41563 raw41563Labels = mixedMoment B raw41563step0 raw41563step0Labels := by
      have hz : ∀ j, raw41563 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41563step0 = (fun i j => raw41563 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41563step0 raw41563; decide +kernel
      have hl : raw41563step0Labels = raw41563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41563 raw41563Labels permutation346 hz
    mixedMoment B raw41563step0 raw41563step0Labels = mixedMoment B raw41563step1 raw41563step1Labels := by
      have ha : raw41563step1 = (fun i j => raw41563step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41563step1 raw41563step0; decide +kernel
      have hl : raw41563step1Labels = raw41563step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41563step0 raw41563step0Labels permutation32 permutation3
    mixedMoment B raw41563step1 raw41563step1Labels = mixedMoment B raw41563step2 raw41563step2Labels := by
      have ha : raw41563step2 = raw41563step1 := by apply Matrix.ext; unfold raw41563step2 raw41563step1; decide +kernel
      have hl : raw41563step1Labels = labelEmbedding7 ∘ raw41563step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41563step1 raw41563step1Labels raw41563step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

theorem canonical41564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41564 raw41564Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw41564 raw41564Labels = mixedMoment B raw41564step0 raw41564step0Labels := by
      have hz : ∀ j, raw41564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41564step0 = (fun i j => raw41564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41564step0 raw41564; decide +kernel
      have hl : raw41564step0Labels = raw41564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41564 raw41564Labels permutation346 hz
    mixedMoment B raw41564step0 raw41564step0Labels = mixedMoment B raw41564step1 raw41564step1Labels := by
      have ha : raw41564step1 = (fun i j => raw41564step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41564step1 raw41564step0; decide +kernel
      have hl : raw41564step1Labels = raw41564step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41564step0 raw41564step0Labels permutation38 permutation2
    mixedMoment B raw41564step1 raw41564step1Labels = mixedMoment B raw41564step2 raw41564step2Labels := by
      have ha : raw41564step2 = raw41564step1 := by apply Matrix.ext; unfold raw41564step2 raw41564step1; decide +kernel
      have hl : raw41564step1Labels = labelEmbedding1 ∘ raw41564step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41564step1 raw41564step1Labels raw41564step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3038 node3038Labels := by rfl

theorem canonical41565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41565 raw41565Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw41565 raw41565Labels = mixedMoment B raw41565step0 raw41565step0Labels := by
      have hz : ∀ j, raw41565 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41565step0 = (fun i j => raw41565 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41565step0 raw41565; decide +kernel
      have hl : raw41565step0Labels = raw41565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41565 raw41565Labels permutation346 hz
    mixedMoment B raw41565step0 raw41565step0Labels = mixedMoment B raw41565step1 raw41565step1Labels := by
      have ha : raw41565step1 = (fun i j => raw41565step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41565step1 raw41565step0; decide +kernel
      have hl : raw41565step1Labels = raw41565step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41565step0 raw41565step0Labels permutation32 permutation3
    mixedMoment B raw41565step1 raw41565step1Labels = mixedMoment B raw41565step2 raw41565step2Labels := by
      have ha : raw41565step2 = raw41565step1 := by apply Matrix.ext; unfold raw41565step2 raw41565step1; decide +kernel
      have hl : raw41565step1Labels = labelEmbedding7 ∘ raw41565step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41565step1 raw41565step1Labels raw41565step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

theorem canonical41566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41566 raw41566Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw41566 raw41566Labels = mixedMoment B raw41566step0 raw41566step0Labels := by
      have hz : ∀ j, raw41566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41566step0 = (fun i j => raw41566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41566step0 raw41566; decide +kernel
      have hl : raw41566step0Labels = raw41566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41566 raw41566Labels permutation346 hz
    mixedMoment B raw41566step0 raw41566step0Labels = mixedMoment B raw41566step1 raw41566step1Labels := by
      have ha : raw41566step1 = (fun i j => raw41566step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41566step1 raw41566step0; decide +kernel
      have hl : raw41566step1Labels = raw41566step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41566step0 raw41566step0Labels permutation145 permutation4
    mixedMoment B raw41566step1 raw41566step1Labels = mixedMoment B raw41566step2 raw41566step2Labels := by
      have ha : raw41566step2 = raw41566step1 := by apply Matrix.ext; unfold raw41566step2 raw41566step1; decide +kernel
      have hl : raw41566step1Labels = labelEmbedding1 ∘ raw41566step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41566step1 raw41566step1Labels raw41566step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2754 node2754Labels := by rfl

theorem canonical41567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41567 raw41567Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw41567 raw41567Labels = mixedMoment B raw41567step0 raw41567step0Labels := by
      have hz : ∀ j, raw41567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41567step0 = (fun i j => raw41567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41567step0 raw41567; decide +kernel
      have hl : raw41567step0Labels = raw41567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41567 raw41567Labels permutation346 hz
    mixedMoment B raw41567step0 raw41567step0Labels = mixedMoment B raw41567step1 raw41567step1Labels := by
      have ha : raw41567step1 = (fun i j => raw41567step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41567step1 raw41567step0; decide +kernel
      have hl : raw41567step1Labels = raw41567step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41567step0 raw41567step0Labels permutation32 permutation3
    mixedMoment B raw41567step1 raw41567step1Labels = mixedMoment B raw41567step2 raw41567step2Labels := by
      have ha : raw41567step2 = raw41567step1 := by apply Matrix.ext; unfold raw41567step2 raw41567step1; decide +kernel
      have hl : raw41567step1Labels = labelEmbedding7 ∘ raw41567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41567step1 raw41567step1Labels raw41567step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

theorem canonical41568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41568 raw41568Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw41568 raw41568Labels = mixedMoment B raw41568step0 raw41568step0Labels := by
      have hz : ∀ j, raw41568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41568step0 = (fun i j => raw41568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41568step0 raw41568; decide +kernel
      have hl : raw41568step0Labels = raw41568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41568 raw41568Labels permutation346 hz
    mixedMoment B raw41568step0 raw41568step0Labels = mixedMoment B raw41568step1 raw41568step1Labels := by
      have ha : raw41568step1 = (fun i j => raw41568step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41568step1 raw41568step0; decide +kernel
      have hl : raw41568step1Labels = raw41568step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41568step0 raw41568step0Labels permutation37 permutation2
    mixedMoment B raw41568step1 raw41568step1Labels = mixedMoment B raw41568step2 raw41568step2Labels := by
      have ha : raw41568step2 = raw41568step1 := by apply Matrix.ext; unfold raw41568step2 raw41568step1; decide +kernel
      have hl : raw41568step1Labels = labelEmbedding1 ∘ raw41568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41568step1 raw41568step1Labels raw41568step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3109 node3109Labels := by rfl

theorem canonical41569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41569 raw41569Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw41569 raw41569Labels = mixedMoment B raw41569step0 raw41569step0Labels := by
      have hz : ∀ j, raw41569 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41569step0 = (fun i j => raw41569 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41569step0 raw41569; decide +kernel
      have hl : raw41569step0Labels = raw41569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41569 raw41569Labels permutation346 hz
    mixedMoment B raw41569step0 raw41569step0Labels = mixedMoment B raw41569step1 raw41569step1Labels := by
      have ha : raw41569step1 = (fun i j => raw41569step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41569step1 raw41569step0; decide +kernel
      have hl : raw41569step1Labels = raw41569step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41569step0 raw41569step0Labels permutation32 permutation3
    mixedMoment B raw41569step1 raw41569step1Labels = mixedMoment B raw41569step2 raw41569step2Labels := by
      have ha : raw41569step2 = raw41569step1 := by apply Matrix.ext; unfold raw41569step2 raw41569step1; decide +kernel
      have hl : raw41569step1Labels = labelEmbedding7 ∘ raw41569step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41569step1 raw41569step1Labels raw41569step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical41570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41570 raw41570Labels = mixedMoment B node3111 node3111Labels := by
  calc
    mixedMoment B raw41570 raw41570Labels = mixedMoment B raw41570step0 raw41570step0Labels := by
      have hz : ∀ j, raw41570 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41570step0 = (fun i j => raw41570 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41570step0 raw41570; decide +kernel
      have hl : raw41570step0Labels = raw41570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41570 raw41570Labels permutation346 hz
    mixedMoment B raw41570step0 raw41570step0Labels = mixedMoment B raw41570step1 raw41570step1Labels := by
      have ha : raw41570step1 = raw41570step0 := by apply Matrix.ext; unfold raw41570step1 raw41570step0; decide +kernel
      have hl : raw41570step0Labels = labelEmbedding1 ∘ raw41570step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41570step0 raw41570step0Labels raw41570step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3111 node3111Labels := by rfl

theorem canonical41571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41571 raw41571Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw41571 raw41571Labels = mixedMoment B raw41571step0 raw41571step0Labels := by
      have hz : ∀ j, raw41571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41571step0 = (fun i j => raw41571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41571step0 raw41571; decide +kernel
      have hl : raw41571step0Labels = raw41571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41571 raw41571Labels permutation346 hz
    mixedMoment B raw41571step0 raw41571step0Labels = mixedMoment B raw41571step1 raw41571step1Labels := by
      have ha : raw41571step1 = (fun i j => raw41571step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41571step1 raw41571step0; decide +kernel
      have hl : raw41571step1Labels = raw41571step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41571step0 raw41571step0Labels permutation32 permutation3
    mixedMoment B raw41571step1 raw41571step1Labels = mixedMoment B raw41571step2 raw41571step2Labels := by
      have ha : raw41571step2 = raw41571step1 := by apply Matrix.ext; unfold raw41571step2 raw41571step1; decide +kernel
      have hl : raw41571step1Labels = labelEmbedding7 ∘ raw41571step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41571step1 raw41571step1Labels raw41571step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

theorem canonical41572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41572 raw41572Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw41572 raw41572Labels = mixedMoment B raw41572step0 raw41572step0Labels := by
      have ha : raw41572step0 = (fun i j => raw41572 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41572step0 raw41572; decide +kernel
      have hl : raw41572step0Labels = raw41572Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41572 raw41572Labels permutation182 permutation2
    mixedMoment B raw41572step0 raw41572step0Labels = mixedMoment B raw41572step1 raw41572step1Labels := by
      have ha : raw41572step1 = raw41572step0 := by apply Matrix.ext; unfold raw41572step1 raw41572step0; decide +kernel
      have hl : raw41572step0Labels = labelEmbedding1 ∘ raw41572step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41572step0 raw41572step0Labels raw41572step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3064 node3064Labels := by rfl

theorem canonical41573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41573 raw41573Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw41573 raw41573Labels = mixedMoment B raw41573step0 raw41573step0Labels := by
      have ha : raw41573step0 = (fun i j => raw41573 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41573step0 raw41573; decide +kernel
      have hl : raw41573step0Labels = raw41573Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41573 raw41573Labels permutation152 permutation3
    mixedMoment B raw41573step0 raw41573step0Labels = mixedMoment B raw41573step1 raw41573step1Labels := by
      have ha : raw41573step1 = raw41573step0 := by apply Matrix.ext; unfold raw41573step1 raw41573step0; decide +kernel
      have hl : raw41573step0Labels = labelEmbedding7 ∘ raw41573step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41573step0 raw41573step0Labels raw41573step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical41574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41574 raw41574Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw41574 raw41574Labels = mixedMoment B raw41574step0 raw41574step0Labels := by
      have ha : raw41574step0 = (fun i j => raw41574 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41574step0 raw41574; decide +kernel
      have hl : raw41574step0Labels = raw41574Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41574 raw41574Labels permutation180 permutation2
    mixedMoment B raw41574step0 raw41574step0Labels = mixedMoment B raw41574step1 raw41574step1Labels := by
      have ha : raw41574step1 = raw41574step0 := by apply Matrix.ext; unfold raw41574step1 raw41574step0; decide +kernel
      have hl : raw41574step0Labels = labelEmbedding1 ∘ raw41574step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41574step0 raw41574step0Labels raw41574step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3085 node3085Labels := by rfl

theorem canonical41575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41575 raw41575Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw41575 raw41575Labels = mixedMoment B raw41575step0 raw41575step0Labels := by
      have ha : raw41575step0 = (fun i j => raw41575 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41575step0 raw41575; decide +kernel
      have hl : raw41575step0Labels = raw41575Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41575 raw41575Labels permutation152 permutation3
    mixedMoment B raw41575step0 raw41575step0Labels = mixedMoment B raw41575step1 raw41575step1Labels := by
      have ha : raw41575step1 = raw41575step0 := by apply Matrix.ext; unfold raw41575step1 raw41575step0; decide +kernel
      have hl : raw41575step0Labels = labelEmbedding7 ∘ raw41575step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41575step0 raw41575step0Labels raw41575step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

theorem canonical41576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41576 raw41576Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw41576 raw41576Labels = mixedMoment B raw41576step0 raw41576step0Labels := by
      have ha : raw41576step0 = (fun i j => raw41576 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41576step0 raw41576; decide +kernel
      have hl : raw41576step0Labels = raw41576Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41576 raw41576Labels permutation179 permutation2
    mixedMoment B raw41576step0 raw41576step0Labels = mixedMoment B raw41576step1 raw41576step1Labels := by
      have ha : raw41576step1 = raw41576step0 := by apply Matrix.ext; unfold raw41576step1 raw41576step0; decide +kernel
      have hl : raw41576step0Labels = labelEmbedding1 ∘ raw41576step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41576step0 raw41576step0Labels raw41576step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3087 node3087Labels := by rfl

theorem canonical41577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41577 raw41577Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw41577 raw41577Labels = mixedMoment B raw41577step0 raw41577step0Labels := by
      have ha : raw41577step0 = (fun i j => raw41577 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41577step0 raw41577; decide +kernel
      have hl : raw41577step0Labels = raw41577Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41577 raw41577Labels permutation152 permutation3
    mixedMoment B raw41577step0 raw41577step0Labels = mixedMoment B raw41577step1 raw41577step1Labels := by
      have ha : raw41577step1 = raw41577step0 := by apply Matrix.ext; unfold raw41577step1 raw41577step0; decide +kernel
      have hl : raw41577step0Labels = labelEmbedding7 ∘ raw41577step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41577step0 raw41577step0Labels raw41577step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical41578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41578 raw41578Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw41578 raw41578Labels = mixedMoment B raw41578step0 raw41578step0Labels := by
      have ha : raw41578step0 = (fun i j => raw41578 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41578step0 raw41578; decide +kernel
      have hl : raw41578step0Labels = raw41578Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41578 raw41578Labels permutation180 permutation2
    mixedMoment B raw41578step0 raw41578step0Labels = mixedMoment B raw41578step1 raw41578step1Labels := by
      have ha : raw41578step1 = raw41578step0 := by apply Matrix.ext; unfold raw41578step1 raw41578step0; decide +kernel
      have hl : raw41578step0Labels = labelEmbedding1 ∘ raw41578step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41578step0 raw41578step0Labels raw41578step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical41579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41579 raw41579Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw41579 raw41579Labels = mixedMoment B raw41579step0 raw41579step0Labels := by
      have ha : raw41579step0 = (fun i j => raw41579 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41579step0 raw41579; decide +kernel
      have hl : raw41579step0Labels = raw41579Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41579 raw41579Labels permutation152 permutation3
    mixedMoment B raw41579step0 raw41579step0Labels = mixedMoment B raw41579step1 raw41579step1Labels := by
      have ha : raw41579step1 = raw41579step0 := by apply Matrix.ext; unfold raw41579step1 raw41579step0; decide +kernel
      have hl : raw41579step0Labels = labelEmbedding7 ∘ raw41579step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41579step0 raw41579step0Labels raw41579step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical41580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41580 raw41580Labels = mixedMoment B node3125 node3125Labels := by
  calc
    mixedMoment B raw41580 raw41580Labels = mixedMoment B raw41580step0 raw41580step0Labels := by
      have hz : ∀ j, raw41580 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41580step0 = (fun i j => raw41580 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41580step0 raw41580; decide +kernel
      have hl : raw41580step0Labels = raw41580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41580 raw41580Labels permutation434 hz
    mixedMoment B raw41580step0 raw41580step0Labels = mixedMoment B raw41580step1 raw41580step1Labels := by
      have hz : ∀ j, raw41580step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41580step1 = (fun i j => raw41580step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41580step1 raw41580step0; decide +kernel
      have hl : raw41580step1Labels = raw41580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41580step0 raw41580step0Labels permutation80 hz
    mixedMoment B raw41580step1 raw41580step1Labels = mixedMoment B raw41580step2 raw41580step2Labels := by
      have hz : ∀ j, raw41580step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41580step2 = (fun i j => raw41580step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41580step2 raw41580step1; decide +kernel
      have hl : raw41580step2Labels = raw41580step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41580step1 raw41580step1Labels permutation14 hz
    mixedMoment B raw41580step2 raw41580step2Labels = mixedMoment B raw41580step3 raw41580step3Labels := by
      have ha : raw41580step3 = raw41580step2 := by apply Matrix.ext; unfold raw41580step3 raw41580step2; decide +kernel
      have hl : raw41580step2Labels = labelEmbedding1 ∘ raw41580step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41580step2 raw41580step2Labels raw41580step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3125 node3125Labels := by rfl

theorem canonical41581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41581 raw41581Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw41581 raw41581Labels = mixedMoment B raw41581step0 raw41581step0Labels := by
      have hz : ∀ j, raw41581 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41581step0 = (fun i j => raw41581 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41581step0 raw41581; decide +kernel
      have hl : raw41581step0Labels = raw41581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41581 raw41581Labels permutation434 hz
    mixedMoment B raw41581step0 raw41581step0Labels = mixedMoment B raw41581step1 raw41581step1Labels := by
      have hz : ∀ j, raw41581step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41581step1 = (fun i j => raw41581step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41581step1 raw41581step0; decide +kernel
      have hl : raw41581step1Labels = raw41581step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41581step0 raw41581step0Labels permutation80 hz
    mixedMoment B raw41581step1 raw41581step1Labels = mixedMoment B raw41581step2 raw41581step2Labels := by
      have hz : ∀ j, raw41581step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41581step2 = (fun i j => raw41581step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41581step2 raw41581step1; decide +kernel
      have hl : raw41581step2Labels = raw41581step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41581step1 raw41581step1Labels permutation14 hz
    mixedMoment B raw41581step2 raw41581step2Labels = mixedMoment B raw41581step3 raw41581step3Labels := by
      have ha : raw41581step3 = (fun i j => raw41581step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41581step3 raw41581step2; decide +kernel
      have hl : raw41581step3Labels = raw41581step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41581step2 raw41581step2Labels permutation2 permutation3
    mixedMoment B raw41581step3 raw41581step3Labels = mixedMoment B raw41581step4 raw41581step4Labels := by
      have ha : raw41581step4 = raw41581step3 := by apply Matrix.ext; unfold raw41581step4 raw41581step3; decide +kernel
      have hl : raw41581step3Labels = labelEmbedding7 ∘ raw41581step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41581step3 raw41581step3Labels raw41581step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5305 node5305Labels := by rfl

theorem canonical41582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41582 raw41582Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw41582 raw41582Labels = mixedMoment B raw41582step0 raw41582step0Labels := by
      have hz : ∀ j, raw41582 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41582step0 = (fun i j => raw41582 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41582step0 raw41582; decide +kernel
      have hl : raw41582step0Labels = raw41582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41582 raw41582Labels permutation434 hz
    mixedMoment B raw41582step0 raw41582step0Labels = mixedMoment B raw41582step1 raw41582step1Labels := by
      have hz : ∀ j, raw41582step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41582step1 = (fun i j => raw41582step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41582step1 raw41582step0; decide +kernel
      have hl : raw41582step1Labels = raw41582step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41582step0 raw41582step0Labels permutation80 hz
    mixedMoment B raw41582step1 raw41582step1Labels = mixedMoment B raw41582step2 raw41582step2Labels := by
      have hz : ∀ j, raw41582step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41582step2 = (fun i j => raw41582step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41582step2 raw41582step1; decide +kernel
      have hl : raw41582step2Labels = raw41582step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41582step1 raw41582step1Labels permutation14 hz
    mixedMoment B raw41582step2 raw41582step2Labels = mixedMoment B raw41582step3 raw41582step3Labels := by
      have ha : raw41582step3 = (fun i j => raw41582step2 (permutation5 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41582step3 raw41582step2; decide +kernel
      have hl : raw41582step3Labels = raw41582step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41582step2 raw41582step2Labels permutation5 permutation4
    mixedMoment B raw41582step3 raw41582step3Labels = mixedMoment B raw41582step4 raw41582step4Labels := by
      have ha : raw41582step4 = raw41582step3 := by apply Matrix.ext; unfold raw41582step4 raw41582step3; decide +kernel
      have hl : raw41582step3Labels = labelEmbedding1 ∘ raw41582step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41582step3 raw41582step3Labels raw41582step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2789 node2789Labels := by rfl

theorem canonical41583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41583 raw41583Labels = mixedMoment B node5311 node5311Labels := by
  calc
    mixedMoment B raw41583 raw41583Labels = mixedMoment B raw41583step0 raw41583step0Labels := by
      have hz : ∀ j, raw41583 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41583step0 = (fun i j => raw41583 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41583step0 raw41583; decide +kernel
      have hl : raw41583step0Labels = raw41583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41583 raw41583Labels permutation434 hz
    mixedMoment B raw41583step0 raw41583step0Labels = mixedMoment B raw41583step1 raw41583step1Labels := by
      have hz : ∀ j, raw41583step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41583step1 = (fun i j => raw41583step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41583step1 raw41583step0; decide +kernel
      have hl : raw41583step1Labels = raw41583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41583step0 raw41583step0Labels permutation80 hz
    mixedMoment B raw41583step1 raw41583step1Labels = mixedMoment B raw41583step2 raw41583step2Labels := by
      have hz : ∀ j, raw41583step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41583step2 = (fun i j => raw41583step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41583step2 raw41583step1; decide +kernel
      have hl : raw41583step2Labels = raw41583step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41583step1 raw41583step1Labels permutation14 hz
    mixedMoment B raw41583step2 raw41583step2Labels = mixedMoment B raw41583step3 raw41583step3Labels := by
      have ha : raw41583step3 = (fun i j => raw41583step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41583step3 raw41583step2; decide +kernel
      have hl : raw41583step3Labels = raw41583step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41583step2 raw41583step2Labels permutation2 permutation3
    mixedMoment B raw41583step3 raw41583step3Labels = mixedMoment B raw41583step4 raw41583step4Labels := by
      have ha : raw41583step4 = raw41583step3 := by apply Matrix.ext; unfold raw41583step4 raw41583step3; decide +kernel
      have hl : raw41583step3Labels = labelEmbedding7 ∘ raw41583step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41583step3 raw41583step3Labels raw41583step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5311 node5311Labels := by rfl

theorem canonical41584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41584 raw41584Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw41584 raw41584Labels = mixedMoment B raw41584step0 raw41584step0Labels := by
      have hz : ∀ j, raw41584 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41584step0 = (fun i j => raw41584 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41584step0 raw41584; decide +kernel
      have hl : raw41584step0Labels = raw41584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41584 raw41584Labels permutation346 hz
    mixedMoment B raw41584step0 raw41584step0Labels = mixedMoment B raw41584step1 raw41584step1Labels := by
      have hz : ∀ j, raw41584step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41584step1 = (fun i j => raw41584step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41584step1 raw41584step0; decide +kernel
      have hl : raw41584step1Labels = raw41584step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41584step0 raw41584step0Labels permutation56 hz
    mixedMoment B raw41584step1 raw41584step1Labels = mixedMoment B raw41584step2 raw41584step2Labels := by
      have ha : raw41584step2 = raw41584step1 := by apply Matrix.ext; unfold raw41584step2 raw41584step1; decide +kernel
      have hl : raw41584step1Labels = labelEmbedding1 ∘ raw41584step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41584step1 raw41584step1Labels raw41584step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3103 node3103Labels := by rfl

theorem canonical41585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41585 raw41585Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw41585 raw41585Labels = mixedMoment B raw41585step0 raw41585step0Labels := by
      have hz : ∀ j, raw41585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41585step0 = (fun i j => raw41585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41585step0 raw41585; decide +kernel
      have hl : raw41585step0Labels = raw41585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41585 raw41585Labels permutation346 hz
    mixedMoment B raw41585step0 raw41585step0Labels = mixedMoment B raw41585step1 raw41585step1Labels := by
      have hz : ∀ j, raw41585step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41585step1 = (fun i j => raw41585step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41585step1 raw41585step0; decide +kernel
      have hl : raw41585step1Labels = raw41585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41585step0 raw41585step0Labels permutation56 hz
    mixedMoment B raw41585step1 raw41585step1Labels = mixedMoment B raw41585step2 raw41585step2Labels := by
      have ha : raw41585step2 = (fun i j => raw41585step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41585step2 raw41585step1; decide +kernel
      have hl : raw41585step2Labels = raw41585step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41585step1 raw41585step1Labels permutation8 permutation3
    mixedMoment B raw41585step2 raw41585step2Labels = mixedMoment B raw41585step3 raw41585step3Labels := by
      have ha : raw41585step3 = raw41585step2 := by apply Matrix.ext; unfold raw41585step3 raw41585step2; decide +kernel
      have hl : raw41585step2Labels = labelEmbedding7 ∘ raw41585step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41585step2 raw41585step2Labels raw41585step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical41586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41586 raw41586Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw41586 raw41586Labels = mixedMoment B raw41586step0 raw41586step0Labels := by
      have hz : ∀ j, raw41586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41586step0 = (fun i j => raw41586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41586step0 raw41586; decide +kernel
      have hl : raw41586step0Labels = raw41586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41586 raw41586Labels permutation346 hz
    mixedMoment B raw41586step0 raw41586step0Labels = mixedMoment B raw41586step1 raw41586step1Labels := by
      have hz : ∀ j, raw41586step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41586step1 = (fun i j => raw41586step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41586step1 raw41586step0; decide +kernel
      have hl : raw41586step1Labels = raw41586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41586step0 raw41586step0Labels permutation56 hz
    mixedMoment B raw41586step1 raw41586step1Labels = mixedMoment B raw41586step2 raw41586step2Labels := by
      have ha : raw41586step2 = raw41586step1 := by apply Matrix.ext; unfold raw41586step2 raw41586step1; decide +kernel
      have hl : raw41586step1Labels = labelEmbedding1 ∘ raw41586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41586step1 raw41586step1Labels raw41586step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

theorem canonical41587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41587 raw41587Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw41587 raw41587Labels = mixedMoment B raw41587step0 raw41587step0Labels := by
      have hz : ∀ j, raw41587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41587step0 = (fun i j => raw41587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41587step0 raw41587; decide +kernel
      have hl : raw41587step0Labels = raw41587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41587 raw41587Labels permutation346 hz
    mixedMoment B raw41587step0 raw41587step0Labels = mixedMoment B raw41587step1 raw41587step1Labels := by
      have hz : ∀ j, raw41587step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41587step1 = (fun i j => raw41587step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41587step1 raw41587step0; decide +kernel
      have hl : raw41587step1Labels = raw41587step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41587step0 raw41587step0Labels permutation56 hz
    mixedMoment B raw41587step1 raw41587step1Labels = mixedMoment B raw41587step2 raw41587step2Labels := by
      have ha : raw41587step2 = (fun i j => raw41587step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41587step2 raw41587step1; decide +kernel
      have hl : raw41587step2Labels = raw41587step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41587step1 raw41587step1Labels permutation8 permutation3
    mixedMoment B raw41587step2 raw41587step2Labels = mixedMoment B raw41587step3 raw41587step3Labels := by
      have ha : raw41587step3 = raw41587step2 := by apply Matrix.ext; unfold raw41587step3 raw41587step2; decide +kernel
      have hl : raw41587step2Labels = labelEmbedding7 ∘ raw41587step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41587step2 raw41587step2Labels raw41587step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

theorem canonical41588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41588 raw41588Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw41588 raw41588Labels = mixedMoment B raw41588step0 raw41588step0Labels := by
      have hz : ∀ j, raw41588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41588step0 = (fun i j => raw41588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41588step0 raw41588; decide +kernel
      have hl : raw41588step0Labels = raw41588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41588 raw41588Labels permutation346 hz
    mixedMoment B raw41588step0 raw41588step0Labels = mixedMoment B raw41588step1 raw41588step1Labels := by
      have hz : ∀ j, raw41588step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41588step1 = (fun i j => raw41588step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41588step1 raw41588step0; decide +kernel
      have hl : raw41588step1Labels = raw41588step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41588step0 raw41588step0Labels permutation56 hz
    mixedMoment B raw41588step1 raw41588step1Labels = mixedMoment B raw41588step2 raw41588step2Labels := by
      have ha : raw41588step2 = raw41588step1 := by apply Matrix.ext; unfold raw41588step2 raw41588step1; decide +kernel
      have hl : raw41588step1Labels = labelEmbedding1 ∘ raw41588step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41588step1 raw41588step1Labels raw41588step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3052 node3052Labels := by rfl

theorem canonical41589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41589 raw41589Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw41589 raw41589Labels = mixedMoment B raw41589step0 raw41589step0Labels := by
      have hz : ∀ j, raw41589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41589step0 = (fun i j => raw41589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41589step0 raw41589; decide +kernel
      have hl : raw41589step0Labels = raw41589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41589 raw41589Labels permutation346 hz
    mixedMoment B raw41589step0 raw41589step0Labels = mixedMoment B raw41589step1 raw41589step1Labels := by
      have hz : ∀ j, raw41589step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41589step1 = (fun i j => raw41589step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41589step1 raw41589step0; decide +kernel
      have hl : raw41589step1Labels = raw41589step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41589step0 raw41589step0Labels permutation56 hz
    mixedMoment B raw41589step1 raw41589step1Labels = mixedMoment B raw41589step2 raw41589step2Labels := by
      have ha : raw41589step2 = (fun i j => raw41589step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41589step2 raw41589step1; decide +kernel
      have hl : raw41589step2Labels = raw41589step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41589step1 raw41589step1Labels permutation30 permutation7
    mixedMoment B raw41589step2 raw41589step2Labels = mixedMoment B raw41589step3 raw41589step3Labels := by
      have ha : raw41589step3 = raw41589step2 := by apply Matrix.ext; unfold raw41589step3 raw41589step2; decide +kernel
      have hl : raw41589step2Labels = labelEmbedding6 ∘ raw41589step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41589step2 raw41589step2Labels raw41589step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

theorem canonical41590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41590 raw41590Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw41590 raw41590Labels = mixedMoment B raw41590step0 raw41590step0Labels := by
      have hz : ∀ j, raw41590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41590step0 = (fun i j => raw41590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41590step0 raw41590; decide +kernel
      have hl : raw41590step0Labels = raw41590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41590 raw41590Labels permutation346 hz
    mixedMoment B raw41590step0 raw41590step0Labels = mixedMoment B raw41590step1 raw41590step1Labels := by
      have hz : ∀ j, raw41590step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41590step1 = (fun i j => raw41590step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41590step1 raw41590step0; decide +kernel
      have hl : raw41590step1Labels = raw41590step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41590step0 raw41590step0Labels permutation56 hz
    mixedMoment B raw41590step1 raw41590step1Labels = mixedMoment B raw41590step2 raw41590step2Labels := by
      have ha : raw41590step2 = (fun i j => raw41590step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41590step2 raw41590step1; decide +kernel
      have hl : raw41590step2Labels = raw41590step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41590step1 raw41590step1Labels permutation31 permutation4
    mixedMoment B raw41590step2 raw41590step2Labels = mixedMoment B raw41590step3 raw41590step3Labels := by
      have ha : raw41590step3 = raw41590step2 := by apply Matrix.ext; unfold raw41590step3 raw41590step2; decide +kernel
      have hl : raw41590step2Labels = labelEmbedding1 ∘ raw41590step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41590step2 raw41590step2Labels raw41590step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2769 node2769Labels := by rfl

theorem canonical41591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41591 raw41591Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw41591 raw41591Labels = mixedMoment B raw41591step0 raw41591step0Labels := by
      have hz : ∀ j, raw41591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41591step0 = (fun i j => raw41591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41591step0 raw41591; decide +kernel
      have hl : raw41591step0Labels = raw41591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41591 raw41591Labels permutation346 hz
    mixedMoment B raw41591step0 raw41591step0Labels = mixedMoment B raw41591step1 raw41591step1Labels := by
      have hz : ∀ j, raw41591step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41591step1 = (fun i j => raw41591step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41591step1 raw41591step0; decide +kernel
      have hl : raw41591step1Labels = raw41591step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41591step0 raw41591step0Labels permutation56 hz
    mixedMoment B raw41591step1 raw41591step1Labels = mixedMoment B raw41591step2 raw41591step2Labels := by
      have ha : raw41591step2 = (fun i j => raw41591step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41591step2 raw41591step1; decide +kernel
      have hl : raw41591step2Labels = raw41591step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41591step1 raw41591step1Labels permutation31 permutation4
    mixedMoment B raw41591step2 raw41591step2Labels = mixedMoment B raw41591step3 raw41591step3Labels := by
      have ha : raw41591step3 = raw41591step2 := by apply Matrix.ext; unfold raw41591step3 raw41591step2; decide +kernel
      have hl : raw41591step2Labels = labelEmbedding10 ∘ raw41591step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41591step2 raw41591step2Labels raw41591step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

theorem canonical41592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41592 raw41592Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw41592 raw41592Labels = mixedMoment B raw41592step0 raw41592step0Labels := by
      have hz : ∀ j, raw41592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41592step0 = (fun i j => raw41592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41592step0 raw41592; decide +kernel
      have hl : raw41592step0Labels = raw41592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41592 raw41592Labels permutation346 hz
    mixedMoment B raw41592step0 raw41592step0Labels = mixedMoment B raw41592step1 raw41592step1Labels := by
      have hz : ∀ j, raw41592step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41592step1 = (fun i j => raw41592step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41592step1 raw41592step0; decide +kernel
      have hl : raw41592step1Labels = raw41592step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41592step0 raw41592step0Labels permutation56 hz
    mixedMoment B raw41592step1 raw41592step1Labels = mixedMoment B raw41592step2 raw41592step2Labels := by
      have ha : raw41592step2 = (fun i j => raw41592step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41592step2 raw41592step1; decide +kernel
      have hl : raw41592step2Labels = raw41592step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41592step1 raw41592step1Labels permutation13 permutation2
    mixedMoment B raw41592step2 raw41592step2Labels = mixedMoment B raw41592step3 raw41592step3Labels := by
      have ha : raw41592step3 = raw41592step2 := by apply Matrix.ext; unfold raw41592step3 raw41592step2; decide +kernel
      have hl : raw41592step2Labels = labelEmbedding1 ∘ raw41592step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41592step2 raw41592step2Labels raw41592step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3119 node3119Labels := by rfl

theorem canonical41593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41593 raw41593Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw41593 raw41593Labels = mixedMoment B raw41593step0 raw41593step0Labels := by
      have hz : ∀ j, raw41593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41593step0 = (fun i j => raw41593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41593step0 raw41593; decide +kernel
      have hl : raw41593step0Labels = raw41593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41593 raw41593Labels permutation346 hz
    mixedMoment B raw41593step0 raw41593step0Labels = mixedMoment B raw41593step1 raw41593step1Labels := by
      have hz : ∀ j, raw41593step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41593step1 = (fun i j => raw41593step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41593step1 raw41593step0; decide +kernel
      have hl : raw41593step1Labels = raw41593step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41593step0 raw41593step0Labels permutation56 hz
    mixedMoment B raw41593step1 raw41593step1Labels = mixedMoment B raw41593step2 raw41593step2Labels := by
      have ha : raw41593step2 = (fun i j => raw41593step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41593step2 raw41593step1; decide +kernel
      have hl : raw41593step2Labels = raw41593step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41593step1 raw41593step1Labels permutation8 permutation3
    mixedMoment B raw41593step2 raw41593step2Labels = mixedMoment B raw41593step3 raw41593step3Labels := by
      have ha : raw41593step3 = raw41593step2 := by apply Matrix.ext; unfold raw41593step3 raw41593step2; decide +kernel
      have hl : raw41593step2Labels = labelEmbedding7 ∘ raw41593step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41593step2 raw41593step2Labels raw41593step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical41594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41594 raw41594Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw41594 raw41594Labels = mixedMoment B raw41594step0 raw41594step0Labels := by
      have hz : ∀ j, raw41594 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41594step0 = (fun i j => raw41594 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41594step0 raw41594; decide +kernel
      have hl : raw41594step0Labels = raw41594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41594 raw41594Labels permutation265 hz
    mixedMoment B raw41594step0 raw41594step0Labels = mixedMoment B raw41594step1 raw41594step1Labels := by
      have ha : raw41594step1 = raw41594step0 := by apply Matrix.ext; unfold raw41594step1 raw41594step0; decide +kernel
      have hl : raw41594step0Labels = labelEmbedding1 ∘ raw41594step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41594step0 raw41594step0Labels raw41594step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

theorem canonical41595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41595 raw41595Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw41595 raw41595Labels = mixedMoment B raw41595step0 raw41595step0Labels := by
      have hz : ∀ j, raw41595 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41595step0 = (fun i j => raw41595 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41595step0 raw41595; decide +kernel
      have hl : raw41595step0Labels = raw41595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41595 raw41595Labels permutation265 hz
    mixedMoment B raw41595step0 raw41595step0Labels = mixedMoment B raw41595step1 raw41595step1Labels := by
      have ha : raw41595step1 = (fun i j => raw41595step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41595step1 raw41595step0; decide +kernel
      have hl : raw41595step1Labels = raw41595step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41595step0 raw41595step0Labels permutation149 permutation7
    mixedMoment B raw41595step1 raw41595step1Labels = mixedMoment B raw41595step2 raw41595step2Labels := by
      have ha : raw41595step2 = raw41595step1 := by apply Matrix.ext; unfold raw41595step2 raw41595step1; decide +kernel
      have hl : raw41595step1Labels = labelEmbedding6 ∘ raw41595step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41595step1 raw41595step1Labels raw41595step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

theorem canonical41596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41596 raw41596Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw41596 raw41596Labels = mixedMoment B raw41596step0 raw41596step0Labels := by
      have hz : ∀ j, raw41596 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41596step0 = (fun i j => raw41596 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41596step0 raw41596; decide +kernel
      have hl : raw41596step0Labels = raw41596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41596 raw41596Labels permutation265 hz
    mixedMoment B raw41596step0 raw41596step0Labels = mixedMoment B raw41596step1 raw41596step1Labels := by
      have ha : raw41596step1 = (fun i j => raw41596step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41596step1 raw41596step0; decide +kernel
      have hl : raw41596step1Labels = raw41596step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41596step0 raw41596step0Labels permutation37 permutation2
    mixedMoment B raw41596step1 raw41596step1Labels = mixedMoment B raw41596step2 raw41596step2Labels := by
      have ha : raw41596step2 = raw41596step1 := by apply Matrix.ext; unfold raw41596step2 raw41596step1; decide +kernel
      have hl : raw41596step1Labels = labelEmbedding1 ∘ raw41596step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41596step1 raw41596step1Labels raw41596step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3097 node3097Labels := by rfl

theorem canonical41597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41597 raw41597Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw41597 raw41597Labels = mixedMoment B raw41597step0 raw41597step0Labels := by
      have hz : ∀ j, raw41597 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41597step0 = (fun i j => raw41597 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41597step0 raw41597; decide +kernel
      have hl : raw41597step0Labels = raw41597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41597 raw41597Labels permutation265 hz
    mixedMoment B raw41597step0 raw41597step0Labels = mixedMoment B raw41597step1 raw41597step1Labels := by
      have ha : raw41597step1 = (fun i j => raw41597step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41597step1 raw41597step0; decide +kernel
      have hl : raw41597step1Labels = raw41597step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41597step0 raw41597step0Labels permutation32 permutation3
    mixedMoment B raw41597step1 raw41597step1Labels = mixedMoment B raw41597step2 raw41597step2Labels := by
      have ha : raw41597step2 = raw41597step1 := by apply Matrix.ext; unfold raw41597step2 raw41597step1; decide +kernel
      have hl : raw41597step1Labels = labelEmbedding7 ∘ raw41597step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41597step1 raw41597step1Labels raw41597step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical41598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41598 raw41598Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw41598 raw41598Labels = mixedMoment B raw41598step0 raw41598step0Labels := by
      have hz : ∀ j, raw41598 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41598step0 = (fun i j => raw41598 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41598step0 raw41598; decide +kernel
      have hl : raw41598step0Labels = raw41598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41598 raw41598Labels permutation265 hz
    mixedMoment B raw41598step0 raw41598step0Labels = mixedMoment B raw41598step1 raw41598step1Labels := by
      have ha : raw41598step1 = (fun i j => raw41598step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41598step1 raw41598step0; decide +kernel
      have hl : raw41598step1Labels = raw41598step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41598step0 raw41598step0Labels permutation35 permutation2
    mixedMoment B raw41598step1 raw41598step1Labels = mixedMoment B raw41598step2 raw41598step2Labels := by
      have ha : raw41598step2 = raw41598step1 := by apply Matrix.ext; unfold raw41598step2 raw41598step1; decide +kernel
      have hl : raw41598step1Labels = labelEmbedding1 ∘ raw41598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41598step1 raw41598step1Labels raw41598step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3099 node3099Labels := by rfl

theorem canonical41599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41599 raw41599Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw41599 raw41599Labels = mixedMoment B raw41599step0 raw41599step0Labels := by
      have hz : ∀ j, raw41599 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41599step0 = (fun i j => raw41599 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41599step0 raw41599; decide +kernel
      have hl : raw41599step0Labels = raw41599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41599 raw41599Labels permutation265 hz
    mixedMoment B raw41599step0 raw41599step0Labels = mixedMoment B raw41599step1 raw41599step1Labels := by
      have ha : raw41599step1 = (fun i j => raw41599step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41599step1 raw41599step0; decide +kernel
      have hl : raw41599step1Labels = raw41599step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41599step0 raw41599step0Labels permutation32 permutation3
    mixedMoment B raw41599step1 raw41599step1Labels = mixedMoment B raw41599step2 raw41599step2Labels := by
      have ha : raw41599step2 = raw41599step1 := by apply Matrix.ext; unfold raw41599step2 raw41599step1; decide +kernel
      have hl : raw41599step1Labels = labelEmbedding7 ∘ raw41599step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41599step1 raw41599step1Labels raw41599step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2112 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2112) =
      Integer.Sparse.eval keyMomentRow2112 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2112).leftCharge (GramAssembly.key 2112).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 0) := by
    have ha : gramCharges (GramAssembly.key 2112).leftCharge (GramAssembly.key 2112).rightCharge = raw41536 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41536Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41536 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2112).leftCharge (GramAssembly.key 2112).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4083) := by
    have ha : gramCharges (GramAssembly.key 2112).leftCharge (GramAssembly.key 2112).rightCharge = raw41537 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41537Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41537 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2112).leftCharge (GramAssembly.key 2112).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2112).leftCharge (GramAssembly.key 2112).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2112, Integer.Sparse.eval]
  ring

theorem keyMoment2113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2113) =
      Integer.Sparse.eval keyMomentRow2113 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2113).leftCharge (GramAssembly.key 2113).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3223) := by
    have ha : gramCharges (GramAssembly.key 2113).leftCharge (GramAssembly.key 2113).rightCharge = raw41538 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41538Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41538 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2113).leftCharge (GramAssembly.key 2113).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4889) := by
    have ha : gramCharges (GramAssembly.key 2113).leftCharge (GramAssembly.key 2113).rightCharge = raw41539 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41539Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41539 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2113).leftCharge (GramAssembly.key 2113).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2113).leftCharge (GramAssembly.key 2113).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2113, Integer.Sparse.eval]
  ring

theorem keyMoment2114 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2114) =
      Integer.Sparse.eval keyMomentRow2114 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2114).leftCharge (GramAssembly.key 2114).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3227) := by
    have ha : gramCharges (GramAssembly.key 2114).leftCharge (GramAssembly.key 2114).rightCharge = raw41540 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41540Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41540 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2114).leftCharge (GramAssembly.key 2114).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4888) := by
    have ha : gramCharges (GramAssembly.key 2114).leftCharge (GramAssembly.key 2114).rightCharge = raw41541 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41541Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41541 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2114).leftCharge (GramAssembly.key 2114).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2114).leftCharge (GramAssembly.key 2114).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2114, Integer.Sparse.eval]
  ring

theorem keyMoment2115 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2115) =
      Integer.Sparse.eval keyMomentRow2115 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2115).leftCharge (GramAssembly.key 2115).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3228) := by
    have ha : gramCharges (GramAssembly.key 2115).leftCharge (GramAssembly.key 2115).rightCharge = raw41542 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41542Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41542 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2115).leftCharge (GramAssembly.key 2115).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4893) := by
    have ha : gramCharges (GramAssembly.key 2115).leftCharge (GramAssembly.key 2115).rightCharge = raw41543 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41543Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41543 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2115).leftCharge (GramAssembly.key 2115).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2115).leftCharge (GramAssembly.key 2115).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2115, Integer.Sparse.eval]
  ring

theorem keyMoment2116 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2116) =
      Integer.Sparse.eval keyMomentRow2116 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2116).leftCharge (GramAssembly.key 2116).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3223) := by
    have ha : gramCharges (GramAssembly.key 2116).leftCharge (GramAssembly.key 2116).rightCharge = raw41544 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41544Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41544 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2116).leftCharge (GramAssembly.key 2116).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4889) := by
    have ha : gramCharges (GramAssembly.key 2116).leftCharge (GramAssembly.key 2116).rightCharge = raw41545 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41545Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41545 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2116).leftCharge (GramAssembly.key 2116).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2116).leftCharge (GramAssembly.key 2116).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2116, Integer.Sparse.eval]
  ring

theorem keyMoment2117 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2117) =
      Integer.Sparse.eval keyMomentRow2117 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2117).leftCharge (GramAssembly.key 2117).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3226) := by
    have ha : gramCharges (GramAssembly.key 2117).leftCharge (GramAssembly.key 2117).rightCharge = raw41546 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41546Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41546 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2117).leftCharge (GramAssembly.key 2117).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4887) := by
    have ha : gramCharges (GramAssembly.key 2117).leftCharge (GramAssembly.key 2117).rightCharge = raw41547 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41547Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41547 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2117).leftCharge (GramAssembly.key 2117).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2117).leftCharge (GramAssembly.key 2117).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2117, Integer.Sparse.eval]
  ring

theorem keyMoment2118 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2118) =
      Integer.Sparse.eval keyMomentRow2118 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2118).leftCharge (GramAssembly.key 2118).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3114) := by
    have ha : gramCharges (GramAssembly.key 2118).leftCharge (GramAssembly.key 2118).rightCharge = raw41548 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41548Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41548 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2118).leftCharge (GramAssembly.key 2118).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4897) := by
    have ha : gramCharges (GramAssembly.key 2118).leftCharge (GramAssembly.key 2118).rightCharge = raw41549 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41549Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41549 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2118).leftCharge (GramAssembly.key 2118).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2118).leftCharge (GramAssembly.key 2118).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2118, Integer.Sparse.eval]
  ring

theorem keyMoment2119 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2119) =
      Integer.Sparse.eval keyMomentRow2119 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2119).leftCharge (GramAssembly.key 2119).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3113) := by
    have ha : gramCharges (GramAssembly.key 2119).leftCharge (GramAssembly.key 2119).rightCharge = raw41550 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41550Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41550 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2119).leftCharge (GramAssembly.key 2119).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5272) := by
    have ha : gramCharges (GramAssembly.key 2119).leftCharge (GramAssembly.key 2119).rightCharge = raw41551 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41551Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41551 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2119).leftCharge (GramAssembly.key 2119).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2119).leftCharge (GramAssembly.key 2119).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2119, Integer.Sparse.eval]
  ring

theorem keyMoment2120 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2120) =
      Integer.Sparse.eval keyMomentRow2120 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2120).leftCharge (GramAssembly.key 2120).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3112) := by
    have ha : gramCharges (GramAssembly.key 2120).leftCharge (GramAssembly.key 2120).rightCharge = raw41552 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41552Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41552 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2120).leftCharge (GramAssembly.key 2120).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5274) := by
    have ha : gramCharges (GramAssembly.key 2120).leftCharge (GramAssembly.key 2120).rightCharge = raw41553 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41553Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41553 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2120).leftCharge (GramAssembly.key 2120).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2120).leftCharge (GramAssembly.key 2120).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2120, Integer.Sparse.eval]
  ring

theorem keyMoment2121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2121) =
      Integer.Sparse.eval keyMomentRow2121 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2121).leftCharge (GramAssembly.key 2121).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3110) := by
    have ha : gramCharges (GramAssembly.key 2121).leftCharge (GramAssembly.key 2121).rightCharge = raw41554 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41554Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41554 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2121).leftCharge (GramAssembly.key 2121).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5275) := by
    have ha : gramCharges (GramAssembly.key 2121).leftCharge (GramAssembly.key 2121).rightCharge = raw41555 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41555Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41555 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2121).leftCharge (GramAssembly.key 2121).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2121).leftCharge (GramAssembly.key 2121).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2121, Integer.Sparse.eval]
  ring

theorem keyMoment2122 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2122) =
      Integer.Sparse.eval keyMomentRow2122 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2122).leftCharge (GramAssembly.key 2122).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2777) := by
    have ha : gramCharges (GramAssembly.key 2122).leftCharge (GramAssembly.key 2122).rightCharge = raw41556 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41556Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41556 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2122).leftCharge (GramAssembly.key 2122).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5276) := by
    have ha : gramCharges (GramAssembly.key 2122).leftCharge (GramAssembly.key 2122).rightCharge = raw41557 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41557Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41557 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2122).leftCharge (GramAssembly.key 2122).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2122).leftCharge (GramAssembly.key 2122).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2122, Integer.Sparse.eval]
  ring

theorem keyMoment2123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2123) =
      Integer.Sparse.eval keyMomentRow2123 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2123).leftCharge (GramAssembly.key 2123).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3089) := by
    have ha : gramCharges (GramAssembly.key 2123).leftCharge (GramAssembly.key 2123).rightCharge = raw41558 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41558Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41558 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2123).leftCharge (GramAssembly.key 2123).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5258) := by
    have ha : gramCharges (GramAssembly.key 2123).leftCharge (GramAssembly.key 2123).rightCharge = raw41559 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41559Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41559 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2123).leftCharge (GramAssembly.key 2123).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2123).leftCharge (GramAssembly.key 2123).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2123, Integer.Sparse.eval]
  ring

theorem keyMoment2124 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2124) =
      Integer.Sparse.eval keyMomentRow2124 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2124).leftCharge (GramAssembly.key 2124).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3088) := by
    have ha : gramCharges (GramAssembly.key 2124).leftCharge (GramAssembly.key 2124).rightCharge = raw41560 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41560Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41560 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2124).leftCharge (GramAssembly.key 2124).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5259) := by
    have ha : gramCharges (GramAssembly.key 2124).leftCharge (GramAssembly.key 2124).rightCharge = raw41561 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41561Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41561 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2124).leftCharge (GramAssembly.key 2124).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2124).leftCharge (GramAssembly.key 2124).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2124, Integer.Sparse.eval]
  ring

theorem keyMoment2125 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2125) =
      Integer.Sparse.eval keyMomentRow2125 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2125).leftCharge (GramAssembly.key 2125).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3086) := by
    have ha : gramCharges (GramAssembly.key 2125).leftCharge (GramAssembly.key 2125).rightCharge = raw41562 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41562Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41562 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2125).leftCharge (GramAssembly.key 2125).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2125).leftCharge (GramAssembly.key 2125).rightCharge = raw41563 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41563Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41563 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2125).leftCharge (GramAssembly.key 2125).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2125).leftCharge (GramAssembly.key 2125).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2125, Integer.Sparse.eval]
  ring

theorem keyMoment2126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2126) =
      Integer.Sparse.eval keyMomentRow2126 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2126).leftCharge (GramAssembly.key 2126).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3038) := by
    have ha : gramCharges (GramAssembly.key 2126).leftCharge (GramAssembly.key 2126).rightCharge = raw41564 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41564Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41564 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2126).leftCharge (GramAssembly.key 2126).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2126).leftCharge (GramAssembly.key 2126).rightCharge = raw41565 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41565Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41565 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2126).leftCharge (GramAssembly.key 2126).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2126).leftCharge (GramAssembly.key 2126).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2126, Integer.Sparse.eval]
  ring

theorem keyMoment2127 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2127) =
      Integer.Sparse.eval keyMomentRow2127 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2127).leftCharge (GramAssembly.key 2127).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2754) := by
    have ha : gramCharges (GramAssembly.key 2127).leftCharge (GramAssembly.key 2127).rightCharge = raw41566 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41566Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41566 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2127).leftCharge (GramAssembly.key 2127).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5270) := by
    have ha : gramCharges (GramAssembly.key 2127).leftCharge (GramAssembly.key 2127).rightCharge = raw41567 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41567Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41567 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2127).leftCharge (GramAssembly.key 2127).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2127).leftCharge (GramAssembly.key 2127).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2127, Integer.Sparse.eval]
  ring

theorem keyMoment2128 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2128) =
      Integer.Sparse.eval keyMomentRow2128 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2128).leftCharge (GramAssembly.key 2128).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3109) := by
    have ha : gramCharges (GramAssembly.key 2128).leftCharge (GramAssembly.key 2128).rightCharge = raw41568 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41568Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41568 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2128).leftCharge (GramAssembly.key 2128).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5271) := by
    have ha : gramCharges (GramAssembly.key 2128).leftCharge (GramAssembly.key 2128).rightCharge = raw41569 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41569Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41569 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2128).leftCharge (GramAssembly.key 2128).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2128).leftCharge (GramAssembly.key 2128).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2128, Integer.Sparse.eval]
  ring

theorem keyMoment2129 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2129) =
      Integer.Sparse.eval keyMomentRow2129 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2129).leftCharge (GramAssembly.key 2129).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3111) := by
    have ha : gramCharges (GramAssembly.key 2129).leftCharge (GramAssembly.key 2129).rightCharge = raw41570 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41570Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41570 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2129).leftCharge (GramAssembly.key 2129).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5273) := by
    have ha : gramCharges (GramAssembly.key 2129).leftCharge (GramAssembly.key 2129).rightCharge = raw41571 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41571Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41571 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2129).leftCharge (GramAssembly.key 2129).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2129).leftCharge (GramAssembly.key 2129).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2129, Integer.Sparse.eval]
  ring

theorem keyMoment2130 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2130) =
      Integer.Sparse.eval keyMomentRow2130 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2130).leftCharge (GramAssembly.key 2130).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3064) := by
    have ha : gramCharges (GramAssembly.key 2130).leftCharge (GramAssembly.key 2130).rightCharge = raw41572 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41572Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41572 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2130).leftCharge (GramAssembly.key 2130).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2130).leftCharge (GramAssembly.key 2130).rightCharge = raw41573 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41573Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41573 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2130).leftCharge (GramAssembly.key 2130).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2130).leftCharge (GramAssembly.key 2130).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2130, Integer.Sparse.eval]
  ring

theorem keyMoment2131 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2131) =
      Integer.Sparse.eval keyMomentRow2131 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2131).leftCharge (GramAssembly.key 2131).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3085) := by
    have ha : gramCharges (GramAssembly.key 2131).leftCharge (GramAssembly.key 2131).rightCharge = raw41574 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41574Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41574 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2131).leftCharge (GramAssembly.key 2131).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5256) := by
    have ha : gramCharges (GramAssembly.key 2131).leftCharge (GramAssembly.key 2131).rightCharge = raw41575 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41575Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41575 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2131).leftCharge (GramAssembly.key 2131).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2131).leftCharge (GramAssembly.key 2131).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2131, Integer.Sparse.eval]
  ring

theorem keyMoment2132 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2132) =
      Integer.Sparse.eval keyMomentRow2132 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2132).leftCharge (GramAssembly.key 2132).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3087) := by
    have ha : gramCharges (GramAssembly.key 2132).leftCharge (GramAssembly.key 2132).rightCharge = raw41576 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41576Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41576 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2132).leftCharge (GramAssembly.key 2132).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5257) := by
    have ha : gramCharges (GramAssembly.key 2132).leftCharge (GramAssembly.key 2132).rightCharge = raw41577 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41577Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41577 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2132).leftCharge (GramAssembly.key 2132).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2132).leftCharge (GramAssembly.key 2132).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2132, Integer.Sparse.eval]
  ring

theorem keyMoment2133 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2133) =
      Integer.Sparse.eval keyMomentRow2133 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2133).leftCharge (GramAssembly.key 2133).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3037) := by
    have ha : gramCharges (GramAssembly.key 2133).leftCharge (GramAssembly.key 2133).rightCharge = raw41578 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41578Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41578 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2133).leftCharge (GramAssembly.key 2133).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2133).leftCharge (GramAssembly.key 2133).rightCharge = raw41579 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41579Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41579 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2133).leftCharge (GramAssembly.key 2133).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2133).leftCharge (GramAssembly.key 2133).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2133, Integer.Sparse.eval]
  ring

theorem keyMoment2134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2134) =
      Integer.Sparse.eval keyMomentRow2134 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2134).leftCharge (GramAssembly.key 2134).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3125) := by
    have ha : gramCharges (GramAssembly.key 2134).leftCharge (GramAssembly.key 2134).rightCharge = raw41580 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41580Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41580 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2134).leftCharge (GramAssembly.key 2134).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5305) := by
    have ha : gramCharges (GramAssembly.key 2134).leftCharge (GramAssembly.key 2134).rightCharge = raw41581 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41581Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41581 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2134).leftCharge (GramAssembly.key 2134).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2134).leftCharge (GramAssembly.key 2134).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2134, Integer.Sparse.eval]
  ring

theorem keyMoment2135 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2135) =
      Integer.Sparse.eval keyMomentRow2135 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2135).leftCharge (GramAssembly.key 2135).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2789) := by
    have ha : gramCharges (GramAssembly.key 2135).leftCharge (GramAssembly.key 2135).rightCharge = raw41582 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41582Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41582 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2135).leftCharge (GramAssembly.key 2135).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5311) := by
    have ha : gramCharges (GramAssembly.key 2135).leftCharge (GramAssembly.key 2135).rightCharge = raw41583 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41583Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41583 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2135).leftCharge (GramAssembly.key 2135).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2135).leftCharge (GramAssembly.key 2135).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2135, Integer.Sparse.eval]
  ring

theorem keyMoment2136 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2136) =
      Integer.Sparse.eval keyMomentRow2136 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2136).leftCharge (GramAssembly.key 2136).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3103) := by
    have ha : gramCharges (GramAssembly.key 2136).leftCharge (GramAssembly.key 2136).rightCharge = raw41584 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41584Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41584 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2136).leftCharge (GramAssembly.key 2136).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5291) := by
    have ha : gramCharges (GramAssembly.key 2136).leftCharge (GramAssembly.key 2136).rightCharge = raw41585 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41585Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41585 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2136).leftCharge (GramAssembly.key 2136).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2136).leftCharge (GramAssembly.key 2136).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2136, Integer.Sparse.eval]
  ring

theorem keyMoment2137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2137) =
      Integer.Sparse.eval keyMomentRow2137 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2137).leftCharge (GramAssembly.key 2137).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3098) := by
    have ha : gramCharges (GramAssembly.key 2137).leftCharge (GramAssembly.key 2137).rightCharge = raw41586 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41586Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41586 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2137).leftCharge (GramAssembly.key 2137).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5295) := by
    have ha : gramCharges (GramAssembly.key 2137).leftCharge (GramAssembly.key 2137).rightCharge = raw41587 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41587Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41587 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2137).leftCharge (GramAssembly.key 2137).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2137).leftCharge (GramAssembly.key 2137).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2137, Integer.Sparse.eval]
  ring

theorem keyMoment2138 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2138) =
      Integer.Sparse.eval keyMomentRow2138 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2138).leftCharge (GramAssembly.key 2138).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3052) := by
    have ha : gramCharges (GramAssembly.key 2138).leftCharge (GramAssembly.key 2138).rightCharge = raw41588 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41588Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41588 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2138).leftCharge (GramAssembly.key 2138).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5276) := by
    have ha : gramCharges (GramAssembly.key 2138).leftCharge (GramAssembly.key 2138).rightCharge = raw41589 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41589Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41589 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2138).leftCharge (GramAssembly.key 2138).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2138).leftCharge (GramAssembly.key 2138).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2138, Integer.Sparse.eval]
  ring

theorem keyMoment2139 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2139) =
      Integer.Sparse.eval keyMomentRow2139 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2139).leftCharge (GramAssembly.key 2139).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2769) := by
    have ha : gramCharges (GramAssembly.key 2139).leftCharge (GramAssembly.key 2139).rightCharge = raw41590 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41590Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41590 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2139).leftCharge (GramAssembly.key 2139).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5295) := by
    have ha : gramCharges (GramAssembly.key 2139).leftCharge (GramAssembly.key 2139).rightCharge = raw41591 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41591Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41591 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2139).leftCharge (GramAssembly.key 2139).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2139).leftCharge (GramAssembly.key 2139).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2139, Integer.Sparse.eval]
  ring

theorem keyMoment2140 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2140) =
      Integer.Sparse.eval keyMomentRow2140 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2140).leftCharge (GramAssembly.key 2140).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3119) := by
    have ha : gramCharges (GramAssembly.key 2140).leftCharge (GramAssembly.key 2140).rightCharge = raw41592 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41592Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41592 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2140).leftCharge (GramAssembly.key 2140).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5304) := by
    have ha : gramCharges (GramAssembly.key 2140).leftCharge (GramAssembly.key 2140).rightCharge = raw41593 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41593Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41593 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2140).leftCharge (GramAssembly.key 2140).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2140).leftCharge (GramAssembly.key 2140).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2140, Integer.Sparse.eval]
  ring

theorem keyMoment2141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2141) =
      Integer.Sparse.eval keyMomentRow2141 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2141).leftCharge (GramAssembly.key 2141).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3075) := by
    have ha : gramCharges (GramAssembly.key 2141).leftCharge (GramAssembly.key 2141).rightCharge = raw41594 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41594Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41594 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2141).leftCharge (GramAssembly.key 2141).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5270) := by
    have ha : gramCharges (GramAssembly.key 2141).leftCharge (GramAssembly.key 2141).rightCharge = raw41595 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41595Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41595 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2141).leftCharge (GramAssembly.key 2141).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2141).leftCharge (GramAssembly.key 2141).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2141, Integer.Sparse.eval]
  ring

theorem keyMoment2142 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2142) =
      Integer.Sparse.eval keyMomentRow2142 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2142).leftCharge (GramAssembly.key 2142).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3097) := by
    have ha : gramCharges (GramAssembly.key 2142).leftCharge (GramAssembly.key 2142).rightCharge = raw41596 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41596Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41596 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2142).leftCharge (GramAssembly.key 2142).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5289) := by
    have ha : gramCharges (GramAssembly.key 2142).leftCharge (GramAssembly.key 2142).rightCharge = raw41597 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41597Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41597 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2142).leftCharge (GramAssembly.key 2142).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2142).leftCharge (GramAssembly.key 2142).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2142, Integer.Sparse.eval]
  ring

theorem keyMoment2143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2143) =
      Integer.Sparse.eval keyMomentRow2143 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2143).leftCharge (GramAssembly.key 2143).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3099) := by
    have ha : gramCharges (GramAssembly.key 2143).leftCharge (GramAssembly.key 2143).rightCharge = raw41598 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41598Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41598 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2143).leftCharge (GramAssembly.key 2143).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5290) := by
    have ha : gramCharges (GramAssembly.key 2143).leftCharge (GramAssembly.key 2143).rightCharge = raw41599 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41599Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41599 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2143).leftCharge (GramAssembly.key 2143).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2143).leftCharge (GramAssembly.key 2143).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2143, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2112 : keyMomentRows (2112 : Fin 2886) =
    keyMomentRow2112 := by decide +kernel

theorem keyMomentRowsAt2113 : keyMomentRows (2113 : Fin 2886) =
    keyMomentRow2113 := by decide +kernel

theorem keyMomentRowsAt2114 : keyMomentRows (2114 : Fin 2886) =
    keyMomentRow2114 := by decide +kernel

theorem keyMomentRowsAt2115 : keyMomentRows (2115 : Fin 2886) =
    keyMomentRow2115 := by decide +kernel

theorem keyMomentRowsAt2116 : keyMomentRows (2116 : Fin 2886) =
    keyMomentRow2116 := by decide +kernel

theorem keyMomentRowsAt2117 : keyMomentRows (2117 : Fin 2886) =
    keyMomentRow2117 := by decide +kernel

theorem keyMomentRowsAt2118 : keyMomentRows (2118 : Fin 2886) =
    keyMomentRow2118 := by decide +kernel

theorem keyMomentRowsAt2119 : keyMomentRows (2119 : Fin 2886) =
    keyMomentRow2119 := by decide +kernel

theorem keyMomentRowsAt2120 : keyMomentRows (2120 : Fin 2886) =
    keyMomentRow2120 := by decide +kernel

theorem keyMomentRowsAt2121 : keyMomentRows (2121 : Fin 2886) =
    keyMomentRow2121 := by decide +kernel

theorem keyMomentRowsAt2122 : keyMomentRows (2122 : Fin 2886) =
    keyMomentRow2122 := by decide +kernel

theorem keyMomentRowsAt2123 : keyMomentRows (2123 : Fin 2886) =
    keyMomentRow2123 := by decide +kernel

theorem keyMomentRowsAt2124 : keyMomentRows (2124 : Fin 2886) =
    keyMomentRow2124 := by decide +kernel

theorem keyMomentRowsAt2125 : keyMomentRows (2125 : Fin 2886) =
    keyMomentRow2125 := by decide +kernel

theorem keyMomentRowsAt2126 : keyMomentRows (2126 : Fin 2886) =
    keyMomentRow2126 := by decide +kernel

theorem keyMomentRowsAt2127 : keyMomentRows (2127 : Fin 2886) =
    keyMomentRow2127 := by decide +kernel

theorem keyMomentRowsAt2128 : keyMomentRows (2128 : Fin 2886) =
    keyMomentRow2128 := by decide +kernel

theorem keyMomentRowsAt2129 : keyMomentRows (2129 : Fin 2886) =
    keyMomentRow2129 := by decide +kernel

theorem keyMomentRowsAt2130 : keyMomentRows (2130 : Fin 2886) =
    keyMomentRow2130 := by decide +kernel

theorem keyMomentRowsAt2131 : keyMomentRows (2131 : Fin 2886) =
    keyMomentRow2131 := by decide +kernel

theorem keyMomentRowsAt2132 : keyMomentRows (2132 : Fin 2886) =
    keyMomentRow2132 := by decide +kernel

theorem keyMomentRowsAt2133 : keyMomentRows (2133 : Fin 2886) =
    keyMomentRow2133 := by decide +kernel

theorem keyMomentRowsAt2134 : keyMomentRows (2134 : Fin 2886) =
    keyMomentRow2134 := by decide +kernel

theorem keyMomentRowsAt2135 : keyMomentRows (2135 : Fin 2886) =
    keyMomentRow2135 := by decide +kernel

theorem keyMomentRowsAt2136 : keyMomentRows (2136 : Fin 2886) =
    keyMomentRow2136 := by decide +kernel

theorem keyMomentRowsAt2137 : keyMomentRows (2137 : Fin 2886) =
    keyMomentRow2137 := by decide +kernel

theorem keyMomentRowsAt2138 : keyMomentRows (2138 : Fin 2886) =
    keyMomentRow2138 := by decide +kernel

theorem keyMomentRowsAt2139 : keyMomentRows (2139 : Fin 2886) =
    keyMomentRow2139 := by decide +kernel

theorem keyMomentRowsAt2140 : keyMomentRows (2140 : Fin 2886) =
    keyMomentRow2140 := by decide +kernel

theorem keyMomentRowsAt2141 : keyMomentRows (2141 : Fin 2886) =
    keyMomentRow2141 := by decide +kernel

theorem keyMomentRowsAt2142 : keyMomentRows (2142 : Fin 2886) =
    keyMomentRow2142 := by decide +kernel

theorem keyMomentRowsAt2143 : keyMomentRows (2143 : Fin 2886) =
    keyMomentRow2143 := by decide +kernel

theorem keyMomentChunkSound66_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 66) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2112 ∨ k.val = 2113 ∨ k.val = 2114 ∨ k.val = 2115 ∨ k.val = 2116 ∨ k.val = 2117 ∨ k.val = 2118 ∨ k.val = 2119 ∨ k.val = 2120 ∨ k.val = 2121 ∨ k.val = 2122 ∨ k.val = 2123 ∨ k.val = 2124 ∨ k.val = 2125 ∨ k.val = 2126 ∨ k.val = 2127 ∨ k.val = 2128 ∨ k.val = 2129 ∨ k.val = 2130 ∨ k.val = 2131 ∨ k.val = 2132 ∨ k.val = 2133 ∨ k.val = 2134 ∨ k.val = 2135 ∨ k.val = 2136 ∨ k.val = 2137 ∨ k.val = 2138 ∨ k.val = 2139 ∨ k.val = 2140 ∨ k.val = 2141 ∨ k.val = 2142 ∨ k.val = 2143 := by omega
  rcases heq with h2112 | h2113 | h2114 | h2115 | h2116 | h2117 | h2118 | h2119 | h2120 | h2121 | h2122 | h2123 | h2124 | h2125 | h2126 | h2127 | h2128 | h2129 | h2130 | h2131 | h2132 | h2133 | h2134 | h2135 | h2136 | h2137 | h2138 | h2139 | h2140 | h2141 | h2142 | h2143
  · have he : k = (2112 : Fin 2886) := Fin.ext h2112
    subst k
    rw [keyMomentRowsAt2112]
    exact keyMoment2112 B hB
  · have he : k = (2113 : Fin 2886) := Fin.ext h2113
    subst k
    rw [keyMomentRowsAt2113]
    exact keyMoment2113 B hB
  · have he : k = (2114 : Fin 2886) := Fin.ext h2114
    subst k
    rw [keyMomentRowsAt2114]
    exact keyMoment2114 B hB
  · have he : k = (2115 : Fin 2886) := Fin.ext h2115
    subst k
    rw [keyMomentRowsAt2115]
    exact keyMoment2115 B hB
  · have he : k = (2116 : Fin 2886) := Fin.ext h2116
    subst k
    rw [keyMomentRowsAt2116]
    exact keyMoment2116 B hB
  · have he : k = (2117 : Fin 2886) := Fin.ext h2117
    subst k
    rw [keyMomentRowsAt2117]
    exact keyMoment2117 B hB
  · have he : k = (2118 : Fin 2886) := Fin.ext h2118
    subst k
    rw [keyMomentRowsAt2118]
    exact keyMoment2118 B hB
  · have he : k = (2119 : Fin 2886) := Fin.ext h2119
    subst k
    rw [keyMomentRowsAt2119]
    exact keyMoment2119 B hB
  · have he : k = (2120 : Fin 2886) := Fin.ext h2120
    subst k
    rw [keyMomentRowsAt2120]
    exact keyMoment2120 B hB
  · have he : k = (2121 : Fin 2886) := Fin.ext h2121
    subst k
    rw [keyMomentRowsAt2121]
    exact keyMoment2121 B hB
  · have he : k = (2122 : Fin 2886) := Fin.ext h2122
    subst k
    rw [keyMomentRowsAt2122]
    exact keyMoment2122 B hB
  · have he : k = (2123 : Fin 2886) := Fin.ext h2123
    subst k
    rw [keyMomentRowsAt2123]
    exact keyMoment2123 B hB
  · have he : k = (2124 : Fin 2886) := Fin.ext h2124
    subst k
    rw [keyMomentRowsAt2124]
    exact keyMoment2124 B hB
  · have he : k = (2125 : Fin 2886) := Fin.ext h2125
    subst k
    rw [keyMomentRowsAt2125]
    exact keyMoment2125 B hB
  · have he : k = (2126 : Fin 2886) := Fin.ext h2126
    subst k
    rw [keyMomentRowsAt2126]
    exact keyMoment2126 B hB
  · have he : k = (2127 : Fin 2886) := Fin.ext h2127
    subst k
    rw [keyMomentRowsAt2127]
    exact keyMoment2127 B hB
  · have he : k = (2128 : Fin 2886) := Fin.ext h2128
    subst k
    rw [keyMomentRowsAt2128]
    exact keyMoment2128 B hB
  · have he : k = (2129 : Fin 2886) := Fin.ext h2129
    subst k
    rw [keyMomentRowsAt2129]
    exact keyMoment2129 B hB
  · have he : k = (2130 : Fin 2886) := Fin.ext h2130
    subst k
    rw [keyMomentRowsAt2130]
    exact keyMoment2130 B hB
  · have he : k = (2131 : Fin 2886) := Fin.ext h2131
    subst k
    rw [keyMomentRowsAt2131]
    exact keyMoment2131 B hB
  · have he : k = (2132 : Fin 2886) := Fin.ext h2132
    subst k
    rw [keyMomentRowsAt2132]
    exact keyMoment2132 B hB
  · have he : k = (2133 : Fin 2886) := Fin.ext h2133
    subst k
    rw [keyMomentRowsAt2133]
    exact keyMoment2133 B hB
  · have he : k = (2134 : Fin 2886) := Fin.ext h2134
    subst k
    rw [keyMomentRowsAt2134]
    exact keyMoment2134 B hB
  · have he : k = (2135 : Fin 2886) := Fin.ext h2135
    subst k
    rw [keyMomentRowsAt2135]
    exact keyMoment2135 B hB
  · have he : k = (2136 : Fin 2886) := Fin.ext h2136
    subst k
    rw [keyMomentRowsAt2136]
    exact keyMoment2136 B hB
  · have he : k = (2137 : Fin 2886) := Fin.ext h2137
    subst k
    rw [keyMomentRowsAt2137]
    exact keyMoment2137 B hB
  · have he : k = (2138 : Fin 2886) := Fin.ext h2138
    subst k
    rw [keyMomentRowsAt2138]
    exact keyMoment2138 B hB
  · have he : k = (2139 : Fin 2886) := Fin.ext h2139
    subst k
    rw [keyMomentRowsAt2139]
    exact keyMoment2139 B hB
  · have he : k = (2140 : Fin 2886) := Fin.ext h2140
    subst k
    rw [keyMomentRowsAt2140]
    exact keyMoment2140 B hB
  · have he : k = (2141 : Fin 2886) := Fin.ext h2141
    subst k
    rw [keyMomentRowsAt2141]
    exact keyMoment2141 B hB
  · have he : k = (2142 : Fin 2886) := Fin.ext h2142
    subst k
    rw [keyMomentRowsAt2142]
    exact keyMoment2142 B hB
  · have he : k = (2143 : Fin 2886) := Fin.ext h2143
    subst k
    rw [keyMomentRowsAt2143]
    exact keyMoment2143 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound66_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound66_e_oai
