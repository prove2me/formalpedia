-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound50_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:57:36.2585+00:00
-- url     : https://prove2.me/submissions/b819f517-7cee-4af7-afb8-c1efd3ae0fc0

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E106
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

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical247
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31649 raw31649Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw31649 raw31649Labels = mixedMoment B raw31649step0 raw31649step0Labels := by
      have hz : ∀ j, raw31649 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31649step0 = (fun i j => raw31649 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31649step0 raw31649; decide +kernel
      have hl : raw31649step0Labels = raw31649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31649 raw31649Labels permutation434 hz
    mixedMoment B raw31649step0 raw31649step0Labels = mixedMoment B raw31649step1 raw31649step1Labels := by
      have hz : ∀ j, raw31649step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31649step1 = (fun i j => raw31649step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31649step1 raw31649step0; decide +kernel
      have hl : raw31649step1Labels = raw31649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31649step0 raw31649step0Labels permutation80 hz
    mixedMoment B raw31649step1 raw31649step1Labels = mixedMoment B raw31649step2 raw31649step2Labels := by
      have ha : raw31649step2 = (fun i j => raw31649step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31649step2 raw31649step1; decide +kernel
      have hl : raw31649step2Labels = raw31649step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31649step1 raw31649step1Labels permutation23 permutation6
    _ = mixedMoment B node2734 node2734Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical41015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41015 raw41015Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw41015 raw41015Labels = mixedMoment B raw41015step0 raw41015step0Labels := by
      have hz : ∀ j, raw41015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41015step0 = (fun i j => raw41015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41015step0 raw41015; decide +kernel
      have hl : raw41015step0Labels = raw41015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41015 raw41015Labels permutation346 hz
    mixedMoment B raw41015step0 raw41015step0Labels = mixedMoment B raw41015step1 raw41015step1Labels := by
      have ha : raw41015step1 = (fun i j => raw41015step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41015step1 raw41015step0; decide +kernel
      have hl : raw41015step1Labels = raw41015step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41015step0 raw41015step0Labels permutation48 permutation6
    mixedMoment B raw41015step1 raw41015step1Labels = mixedMoment B raw41015step2 raw41015step2Labels := by
      have ha : raw41015step2 = -raw41015step1 := by apply Matrix.ext; change ∀ i j, raw41015step2 i j = -(raw41015step1 i j); unfold raw41015step2 raw41015step1; decide +kernel
      have hl : raw41015step2Labels = raw41015step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3078 node3078Labels := by rfl

theorem canonical41016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41016 raw41016Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw41016 raw41016Labels = mixedMoment B raw41016step0 raw41016step0Labels := by
      have hz : ∀ j, raw41016 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41016step0 = (fun i j => raw41016 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41016step0 raw41016; decide +kernel
      have hl : raw41016step0Labels = raw41016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41016 raw41016Labels permutation520 hz
    mixedMoment B raw41016step0 raw41016step0Labels = mixedMoment B raw41016step1 raw41016step1Labels := by
      have hz : ∀ j, raw41016step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41016step1 = (fun i j => raw41016step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41016step1 raw41016step0; decide +kernel
      have hl : raw41016step1Labels = raw41016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41016step0 raw41016step0Labels permutation104 hz
    mixedMoment B raw41016step1 raw41016step1Labels = mixedMoment B raw41016step2 raw41016step2Labels := by
      have ha : raw41016step2 = (fun i j => raw41016step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41016step2 raw41016step1; decide +kernel
      have hl : raw41016step2Labels = raw41016step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41016step1 raw41016step1Labels permutation31 permutation3
    mixedMoment B raw41016step2 raw41016step2Labels = mixedMoment B raw41016step3 raw41016step3Labels := by
      have ha : raw41016step3 = -raw41016step2 := by apply Matrix.ext; change ∀ i j, raw41016step3 i j = -(raw41016step2 i j); unfold raw41016step3 raw41016step2; decide +kernel
      have hl : raw41016step3Labels = raw41016step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2777 node2777Labels := by rfl

theorem canonical41017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41017 raw41017Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw41017 raw41017Labels = mixedMoment B raw41017step0 raw41017step0Labels := by
      have hz : ∀ j, raw41017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41017step0 = (fun i j => raw41017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41017step0 raw41017; decide +kernel
      have hl : raw41017step0Labels = raw41017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41017 raw41017Labels permutation434 hz
    mixedMoment B raw41017step0 raw41017step0Labels = mixedMoment B raw41017step1 raw41017step1Labels := by
      have ha : raw41017step1 = (fun i j => raw41017step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41017step1 raw41017step0; decide +kernel
      have hl : raw41017step1Labels = raw41017step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41017step0 raw41017step0Labels permutation45 permutation6
    mixedMoment B raw41017step1 raw41017step1Labels = mixedMoment B raw41017step2 raw41017step2Labels := by
      have ha : raw41017step2 = -raw41017step1 := by apply Matrix.ext; change ∀ i j, raw41017step2 i j = -(raw41017step1 i j); unfold raw41017step2 raw41017step1; decide +kernel
      have hl : raw41017step2Labels = raw41017step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2942 node2942Labels := by rfl

theorem canonical41018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41018 raw41018Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw41018 raw41018Labels = mixedMoment B raw41018step0 raw41018step0Labels := by
      have hz : ∀ j, raw41018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41018step0 = (fun i j => raw41018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41018step0 raw41018; decide +kernel
      have hl : raw41018step0Labels = raw41018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41018 raw41018Labels permutation434 hz
    mixedMoment B raw41018step0 raw41018step0Labels = mixedMoment B raw41018step1 raw41018step1Labels := by
      have ha : raw41018step1 = (fun i j => raw41018step0 (permutation51 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41018step1 raw41018step0; decide +kernel
      have hl : raw41018step1Labels = raw41018step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41018step0 raw41018step0Labels permutation51 permutation6
    mixedMoment B raw41018step1 raw41018step1Labels = mixedMoment B raw41018step2 raw41018step2Labels := by
      have ha : raw41018step2 = -raw41018step1 := by apply Matrix.ext; change ∀ i j, raw41018step2 i j = -(raw41018step1 i j); unfold raw41018step2 raw41018step1; decide +kernel
      have hl : raw41018step2Labels = raw41018step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3038 node3038Labels := by rfl

theorem canonical41019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41019 raw41019Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw41019 raw41019Labels = mixedMoment B raw41019step0 raw41019step0Labels := by
      have hz : ∀ j, raw41019 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41019step0 = (fun i j => raw41019 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41019step0 raw41019; decide +kernel
      have hl : raw41019step0Labels = raw41019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41019 raw41019Labels permutation434 hz
    mixedMoment B raw41019step0 raw41019step0Labels = mixedMoment B raw41019step1 raw41019step1Labels := by
      have ha : raw41019step1 = (fun i j => raw41019step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41019step1 raw41019step0; decide +kernel
      have hl : raw41019step1Labels = raw41019step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41019step0 raw41019step0Labels permutation45 permutation6
    mixedMoment B raw41019step1 raw41019step1Labels = mixedMoment B raw41019step2 raw41019step2Labels := by
      have ha : raw41019step2 = -raw41019step1 := by apply Matrix.ext; change ∀ i j, raw41019step2 i j = -(raw41019step1 i j); unfold raw41019step2 raw41019step1; decide +kernel
      have hl : raw41019step2Labels = raw41019step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3086 node3086Labels := by rfl

theorem canonical41020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41020 raw41020Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw41020 raw41020Labels = mixedMoment B raw41020step0 raw41020step0Labels := by
      have hz : ∀ j, raw41020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41020step0 = (fun i j => raw41020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41020step0 raw41020; decide +kernel
      have hl : raw41020step0Labels = raw41020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41020 raw41020Labels permutation434 hz
    mixedMoment B raw41020step0 raw41020step0Labels = mixedMoment B raw41020step1 raw41020step1Labels := by
      have ha : raw41020step1 = (fun i j => raw41020step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41020step1 raw41020step0; decide +kernel
      have hl : raw41020step1Labels = raw41020step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41020step0 raw41020step0Labels permutation45 permutation6
    mixedMoment B raw41020step1 raw41020step1Labels = mixedMoment B raw41020step2 raw41020step2Labels := by
      have ha : raw41020step2 = -raw41020step1 := by apply Matrix.ext; change ∀ i j, raw41020step2 i j = -(raw41020step1 i j); unfold raw41020step2 raw41020step1; decide +kernel
      have hl : raw41020step2Labels = raw41020step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2867 node2867Labels := by rfl

theorem canonical41021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41021 raw41021Labels = mixedMoment B node2933 node2933Labels := by
  calc
    mixedMoment B raw41021 raw41021Labels = mixedMoment B raw41021step0 raw41021step0Labels := by
      have ha : raw41021step0 = (fun i j => raw41021 (permutation205 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41021step0 raw41021; decide +kernel
      have hl : raw41021step0Labels = raw41021Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41021 raw41021Labels permutation205 permutation6
    mixedMoment B raw41021step0 raw41021step0Labels = mixedMoment B raw41021step1 raw41021step1Labels := by
      have ha : raw41021step1 = -raw41021step0 := by apply Matrix.ext; change ∀ i j, raw41021step1 i j = -(raw41021step0 i j); unfold raw41021step1 raw41021step0; decide +kernel
      have hl : raw41021step1Labels = raw41021step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2933 node2933Labels := by rfl

theorem canonical41022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41022 raw41022Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw41022 raw41022Labels = mixedMoment B raw41022step0 raw41022step0Labels := by
      have ha : raw41022step0 = (fun i j => raw41022 (permutation213 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41022step0 raw41022; decide +kernel
      have hl : raw41022step0Labels = raw41022Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41022 raw41022Labels permutation213 permutation6
    mixedMoment B raw41022step0 raw41022step0Labels = mixedMoment B raw41022step1 raw41022step1Labels := by
      have ha : raw41022step1 = -raw41022step0 := by apply Matrix.ext; change ∀ i j, raw41022step1 i j = -(raw41022step0 i j); unfold raw41022step1 raw41022step0; decide +kernel
      have hl : raw41022step1Labels = raw41022step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2916 node2916Labels := by rfl

theorem canonical41023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41023 raw41023Labels = mixedMoment B node2861 node2861Labels := by
  calc
    mixedMoment B raw41023 raw41023Labels = mixedMoment B raw41023step0 raw41023step0Labels := by
      have ha : raw41023step0 = (fun i j => raw41023 (permutation249 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41023step0 raw41023; decide +kernel
      have hl : raw41023step0Labels = raw41023Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41023 raw41023Labels permutation249 permutation6
    mixedMoment B raw41023step0 raw41023step0Labels = mixedMoment B raw41023step1 raw41023step1Labels := by
      have ha : raw41023step1 = -raw41023step0 := by apply Matrix.ext; change ∀ i j, raw41023step1 i j = -(raw41023step0 i j); unfold raw41023step1 raw41023step0; decide +kernel
      have hl : raw41023step1Labels = raw41023step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2861 node2861Labels := by rfl

theorem canonical41024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41024 raw41024Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw41024 raw41024Labels = mixedMoment B raw41024step0 raw41024step0Labels := by
      have ha : raw41024step0 = (fun i j => raw41024 (permutation241 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41024step0 raw41024; decide +kernel
      have hl : raw41024step0Labels = raw41024Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41024 raw41024Labels permutation241 permutation6
    mixedMoment B raw41024step0 raw41024step0Labels = mixedMoment B raw41024step1 raw41024step1Labels := by
      have ha : raw41024step1 = -raw41024step0 := by apply Matrix.ext; change ∀ i j, raw41024step1 i j = -(raw41024step0 i j); unfold raw41024step1 raw41024step0; decide +kernel
      have hl : raw41024step1Labels = raw41024step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3064 node3064Labels := by rfl

theorem canonical41025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41025 raw41025Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw41025 raw41025Labels = mixedMoment B raw41025step0 raw41025step0Labels := by
      have hz : ∀ j, raw41025 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41025step0 = (fun i j => raw41025 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41025step0 raw41025; decide +kernel
      have hl : raw41025step0Labels = raw41025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41025 raw41025Labels permutation520 hz
    mixedMoment B raw41025step0 raw41025step0Labels = mixedMoment B raw41025step1 raw41025step1Labels := by
      have ha : raw41025step1 = (fun i j => raw41025step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41025step1 raw41025step0; decide +kernel
      have hl : raw41025step1Labels = raw41025step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41025step0 raw41025step0Labels permutation145 permutation3
    mixedMoment B raw41025step1 raw41025step1Labels = mixedMoment B raw41025step2 raw41025step2Labels := by
      have ha : raw41025step2 = -raw41025step1 := by apply Matrix.ext; change ∀ i j, raw41025step2 i j = -(raw41025step1 i j); unfold raw41025step2 raw41025step1; decide +kernel
      have hl : raw41025step2Labels = raw41025step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2754 node2754Labels := by rfl

theorem canonical41026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41026 raw41026Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw41026 raw41026Labels = mixedMoment B raw41026step0 raw41026step0Labels := by
      have hz : ∀ j, raw41026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41026step0 = (fun i j => raw41026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41026step0 raw41026; decide +kernel
      have hl : raw41026step0Labels = raw41026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41026 raw41026Labels permutation434 hz
    mixedMoment B raw41026step0 raw41026step0Labels = mixedMoment B raw41026step1 raw41026step1Labels := by
      have ha : raw41026step1 = (fun i j => raw41026step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41026step1 raw41026step0; decide +kernel
      have hl : raw41026step1Labels = raw41026step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41026step0 raw41026step0Labels permutation44 permutation6
    mixedMoment B raw41026step1 raw41026step1Labels = mixedMoment B raw41026step2 raw41026step2Labels := by
      have ha : raw41026step2 = -raw41026step1 := by apply Matrix.ext; change ∀ i j, raw41026step2 i j = -(raw41026step1 i j); unfold raw41026step2 raw41026step1; decide +kernel
      have hl : raw41026step2Labels = raw41026step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2865 node2865Labels := by rfl

theorem canonical41027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41027 raw41027Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw41027 raw41027Labels = mixedMoment B raw41027step0 raw41027step0Labels := by
      have hz : ∀ j, raw41027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41027step0 = (fun i j => raw41027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41027step0 raw41027; decide +kernel
      have hl : raw41027step0Labels = raw41027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41027 raw41027Labels permutation434 hz
    mixedMoment B raw41027step0 raw41027step0Labels = mixedMoment B raw41027step1 raw41027step1Labels := by
      have hz : ∀ j, raw41027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41027step1 = (fun i j => raw41027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41027step1 raw41027step0; decide +kernel
      have hl : raw41027step1Labels = raw41027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41027step0 raw41027step0Labels permutation80 hz
    mixedMoment B raw41027step1 raw41027step1Labels = mixedMoment B raw41027step2 raw41027step2Labels := by
      have ha : raw41027step2 = (fun i j => raw41027step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41027step2 raw41027step1; decide +kernel
      have hl : raw41027step2Labels = raw41027step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41027step1 raw41027step1Labels permutation29 permutation6
    _ = mixedMoment B node1243 node1243Labels := by rfl

theorem canonical41028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41028 raw41028Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw41028 raw41028Labels = mixedMoment B raw41028step0 raw41028step0Labels := by
      have hz : ∀ j, raw41028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41028step0 = (fun i j => raw41028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41028step0 raw41028; decide +kernel
      have hl : raw41028step0Labels = raw41028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41028 raw41028Labels permutation346 hz
    mixedMoment B raw41028step0 raw41028step0Labels = mixedMoment B raw41028step1 raw41028step1Labels := by
      have ha : raw41028step1 = (fun i j => raw41028step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41028step1 raw41028step0; decide +kernel
      have hl : raw41028step1Labels = raw41028step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41028step0 raw41028step0Labels permutation125 permutation6
    _ = mixedMoment B node2618 node2618Labels := by rfl

theorem canonical41029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41029 raw41029Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw41029 raw41029Labels = mixedMoment B raw41029step0 raw41029step0Labels := by
      have hz : ∀ j, raw41029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41029step0 = (fun i j => raw41029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41029step0 raw41029; decide +kernel
      have hl : raw41029step0Labels = raw41029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41029 raw41029Labels permutation346 hz
    mixedMoment B raw41029step0 raw41029step0Labels = mixedMoment B raw41029step1 raw41029step1Labels := by
      have ha : raw41029step1 = (fun i j => raw41029step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41029step1 raw41029step0; decide +kernel
      have hl : raw41029step1Labels = raw41029step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41029step0 raw41029step0Labels permutation139 permutation6
    _ = mixedMoment B node1217 node1217Labels := by rfl

theorem canonical41030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41030 raw41030Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw41030 raw41030Labels = mixedMoment B raw41030step0 raw41030step0Labels := by
      have hz : ∀ j, raw41030 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41030step0 = (fun i j => raw41030 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41030step0 raw41030; decide +kernel
      have hl : raw41030step0Labels = raw41030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41030 raw41030Labels permutation346 hz
    mixedMoment B raw41030step0 raw41030step0Labels = mixedMoment B raw41030step1 raw41030step1Labels := by
      have ha : raw41030step1 = (fun i j => raw41030step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41030step1 raw41030step0; decide +kernel
      have hl : raw41030step1Labels = raw41030step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41030step0 raw41030step0Labels permutation95 permutation6
    _ = mixedMoment B node2558 node2558Labels := by rfl

theorem canonical41031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41031 raw41031Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw41031 raw41031Labels = mixedMoment B raw41031step0 raw41031step0Labels := by
      have hz : ∀ j, raw41031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41031step0 = (fun i j => raw41031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41031step0 raw41031; decide +kernel
      have hl : raw41031step0Labels = raw41031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41031 raw41031Labels permutation346 hz
    mixedMoment B raw41031step0 raw41031step0Labels = mixedMoment B raw41031step1 raw41031step1Labels := by
      have ha : raw41031step1 = (fun i j => raw41031step0 (permutation89 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41031step1 raw41031step0; decide +kernel
      have hl : raw41031step1Labels = raw41031step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41031step0 raw41031step0Labels permutation89 permutation6
    _ = mixedMoment B node2712 node2712Labels := by rfl

theorem canonical41032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41032 raw41032Labels = mixedMoment B node2134 node2134Labels := by
  calc
    mixedMoment B raw41032 raw41032Labels = mixedMoment B raw41032step0 raw41032step0Labels := by
      have hz : ∀ j, raw41032 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41032step0 = (fun i j => raw41032 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41032step0 raw41032; decide +kernel
      have hl : raw41032step0Labels = raw41032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41032 raw41032Labels permutation520 hz
    mixedMoment B raw41032step0 raw41032step0Labels = mixedMoment B raw41032step1 raw41032step1Labels := by
      have hz : ∀ j, raw41032step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41032step1 = (fun i j => raw41032step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41032step1 raw41032step0; decide +kernel
      have hl : raw41032step1Labels = raw41032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41032step0 raw41032step0Labels permutation104 hz
    mixedMoment B raw41032step1 raw41032step1Labels = mixedMoment B raw41032step2 raw41032step2Labels := by
      have ha : raw41032step2 = (fun i j => raw41032step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41032step2 raw41032step1; decide +kernel
      have hl : raw41032step2Labels = raw41032step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41032step1 raw41032step1Labels permutation25 permutation6
    _ = mixedMoment B node2134 node2134Labels := by rfl

theorem canonical41033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41033 raw41033Labels = mixedMoment B node1825 node1825Labels := by
  calc
    mixedMoment B raw41033 raw41033Labels = mixedMoment B raw41033step0 raw41033step0Labels := by
      have hz : ∀ j, raw41033 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41033step0 = (fun i j => raw41033 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41033step0 raw41033; decide +kernel
      have hl : raw41033step0Labels = raw41033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41033 raw41033Labels permutation434 hz
    mixedMoment B raw41033step0 raw41033step0Labels = mixedMoment B raw41033step1 raw41033step1Labels := by
      have ha : raw41033step1 = (fun i j => raw41033step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41033step1 raw41033step0; decide +kernel
      have hl : raw41033step1Labels = raw41033step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41033step0 raw41033step0Labels permutation101 permutation6
    _ = mixedMoment B node1825 node1825Labels := by rfl

theorem canonical41034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41034 raw41034Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw41034 raw41034Labels = mixedMoment B raw41034step0 raw41034step0Labels := by
      have hz : ∀ j, raw41034 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41034step0 = (fun i j => raw41034 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41034step0 raw41034; decide +kernel
      have hl : raw41034step0Labels = raw41034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41034 raw41034Labels permutation434 hz
    mixedMoment B raw41034step0 raw41034step0Labels = mixedMoment B raw41034step1 raw41034step1Labels := by
      have ha : raw41034step1 = (fun i j => raw41034step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41034step1 raw41034step0; decide +kernel
      have hl : raw41034step1Labels = raw41034step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41034step0 raw41034step0Labels permutation103 permutation6
    _ = mixedMoment B node2090 node2090Labels := by rfl

theorem canonical41035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41035 raw41035Labels = mixedMoment B node1808 node1808Labels := by
  calc
    mixedMoment B raw41035 raw41035Labels = mixedMoment B raw41035step0 raw41035step0Labels := by
      have hz : ∀ j, raw41035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41035step0 = (fun i j => raw41035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41035step0 raw41035; decide +kernel
      have hl : raw41035step0Labels = raw41035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41035 raw41035Labels permutation434 hz
    mixedMoment B raw41035step0 raw41035step0Labels = mixedMoment B raw41035step1 raw41035step1Labels := by
      have ha : raw41035step1 = (fun i j => raw41035step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41035step1 raw41035step0; decide +kernel
      have hl : raw41035step1Labels = raw41035step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41035step0 raw41035step0Labels permutation101 permutation6
    _ = mixedMoment B node1808 node1808Labels := by rfl

theorem canonical41036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41036 raw41036Labels = mixedMoment B node1973 node1973Labels := by
  calc
    mixedMoment B raw41036 raw41036Labels = mixedMoment B raw41036step0 raw41036step0Labels := by
      have ha : raw41036step0 = (fun i j => raw41036 (permutation412 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41036step0 raw41036; decide +kernel
      have hl : raw41036step0Labels = raw41036Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41036 raw41036Labels permutation412 permutation6
    _ = mixedMoment B node1973 node1973Labels := by rfl

theorem canonical41037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41037 raw41037Labels = mixedMoment B node1790 node1790Labels := by
  calc
    mixedMoment B raw41037 raw41037Labels = mixedMoment B raw41037step0 raw41037step0Labels := by
      have ha : raw41037step0 = (fun i j => raw41037 (permutation431 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41037step0 raw41037; decide +kernel
      have hl : raw41037step0Labels = raw41037Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41037 raw41037Labels permutation431 permutation6
    _ = mixedMoment B node1790 node1790Labels := by rfl

theorem canonical41038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41038 raw41038Labels = mixedMoment B node2759 node2759Labels := by
  calc
    mixedMoment B raw41038 raw41038Labels = mixedMoment B raw41038step0 raw41038step0Labels := by
      have hz : ∀ j, raw41038 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41038step0 = (fun i j => raw41038 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41038step0 raw41038; decide +kernel
      have hl : raw41038step0Labels = raw41038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41038 raw41038Labels permutation520 hz
    mixedMoment B raw41038step0 raw41038step0Labels = mixedMoment B raw41038step1 raw41038step1Labels := by
      have ha : raw41038step1 = (fun i j => raw41038step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41038step1 raw41038step0; decide +kernel
      have hl : raw41038step1Labels = raw41038step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41038step0 raw41038step0Labels permutation151 permutation3
    mixedMoment B raw41038step1 raw41038step1Labels = mixedMoment B raw41038step2 raw41038step2Labels := by
      have ha : raw41038step2 = -raw41038step1 := by apply Matrix.ext; change ∀ i j, raw41038step2 i j = -(raw41038step1 i j); unfold raw41038step2 raw41038step1; decide +kernel
      have hl : raw41038step2Labels = raw41038step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2759 node2759Labels := by rfl

theorem canonical41039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41039 raw41039Labels = mixedMoment B node2902 node2902Labels := by
  calc
    mixedMoment B raw41039 raw41039Labels = mixedMoment B raw41039step0 raw41039step0Labels := by
      have ha : raw41039step0 = (fun i j => raw41039 (permutation227 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41039step0 raw41039; decide +kernel
      have hl : raw41039step0Labels = raw41039Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41039 raw41039Labels permutation227 permutation6
    mixedMoment B raw41039step0 raw41039step0Labels = mixedMoment B raw41039step1 raw41039step1Labels := by
      have ha : raw41039step1 = -raw41039step0 := by apply Matrix.ext; change ∀ i j, raw41039step1 i j = -(raw41039step0 i j); unfold raw41039step1 raw41039step0; decide +kernel
      have hl : raw41039step1Labels = raw41039step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2902 node2902Labels := by rfl

theorem canonical41040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41040 raw41040Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw41040 raw41040Labels = mixedMoment B raw41040step0 raw41040step0Labels := by
      have ha : raw41040step0 = (fun i j => raw41040 (permutation169 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41040step0 raw41040; decide +kernel
      have hl : raw41040step0Labels = raw41040Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41040 raw41040Labels permutation169 permutation6
    mixedMoment B raw41040step0 raw41040step0Labels = mixedMoment B raw41040step1 raw41040step1Labels := by
      have ha : raw41040step1 = -raw41040step0 := by apply Matrix.ext; change ∀ i j, raw41040step1 i j = -(raw41040step0 i j); unfold raw41040step1 raw41040step0; decide +kernel
      have hl : raw41040step1Labels = raw41040step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2984 node2984Labels := by rfl

theorem canonical41041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41041 raw41041Labels = mixedMoment B node2848 node2848Labels := by
  calc
    mixedMoment B raw41041 raw41041Labels = mixedMoment B raw41041step0 raw41041step0Labels := by
      have ha : raw41041step0 = (fun i j => raw41041 (permutation227 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41041step0 raw41041; decide +kernel
      have hl : raw41041step0Labels = raw41041Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41041 raw41041Labels permutation227 permutation6
    mixedMoment B raw41041step0 raw41041step0Labels = mixedMoment B raw41041step1 raw41041step1Labels := by
      have ha : raw41041step1 = -raw41041step0 := by apply Matrix.ext; change ∀ i j, raw41041step1 i j = -(raw41041step0 i j); unfold raw41041step1 raw41041step0; decide +kernel
      have hl : raw41041step1Labels = raw41041step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2848 node2848Labels := by rfl

theorem canonical41042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41042 raw41042Labels = mixedMoment B node2979 node2979Labels := by
  calc
    mixedMoment B raw41042 raw41042Labels = mixedMoment B raw41042step0 raw41042step0Labels := by
      have hz : ∀ j, raw41042 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41042step0 = (fun i j => raw41042 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41042step0 raw41042; decide +kernel
      have hl : raw41042step0Labels = raw41042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41042 raw41042Labels permutation434 hz
    mixedMoment B raw41042step0 raw41042step0Labels = mixedMoment B raw41042step1 raw41042step1Labels := by
      have ha : raw41042step1 = (fun i j => raw41042step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41042step1 raw41042step0; decide +kernel
      have hl : raw41042step1Labels = raw41042step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41042step0 raw41042step0Labels permutation37 permutation6
    mixedMoment B raw41042step1 raw41042step1Labels = mixedMoment B raw41042step2 raw41042step2Labels := by
      have ha : raw41042step2 = -raw41042step1 := by apply Matrix.ext; change ∀ i j, raw41042step2 i j = -(raw41042step1 i j); unfold raw41042step2 raw41042step1; decide +kernel
      have hl : raw41042step2Labels = raw41042step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2979 node2979Labels := by rfl

theorem canonical41043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41043 raw41043Labels = mixedMoment B node2811 node2811Labels := by
  calc
    mixedMoment B raw41043 raw41043Labels = mixedMoment B raw41043step0 raw41043step0Labels := by
      have hz : ∀ j, raw41043 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41043step0 = (fun i j => raw41043 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41043step0 raw41043; decide +kernel
      have hl : raw41043step0Labels = raw41043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41043 raw41043Labels permutation434 hz
    mixedMoment B raw41043step0 raw41043step0Labels = mixedMoment B raw41043step1 raw41043step1Labels := by
      have ha : raw41043step1 = (fun i j => raw41043step0 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41043step1 raw41043step0; decide +kernel
      have hl : raw41043step1Labels = raw41043step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41043step0 raw41043step0Labels permutation143 permutation6
    _ = mixedMoment B node2811 node2811Labels := by rfl

theorem canonical41044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41044 raw41044Labels = mixedMoment B node2900 node2900Labels := by
  calc
    mixedMoment B raw41044 raw41044Labels = mixedMoment B raw41044step0 raw41044step0Labels := by
      have ha : raw41044step0 = (fun i j => raw41044 (permutation205 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41044step0 raw41044; decide +kernel
      have hl : raw41044step0Labels = raw41044Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41044 raw41044Labels permutation205 permutation6
    mixedMoment B raw41044step0 raw41044step0Labels = mixedMoment B raw41044step1 raw41044step1Labels := by
      have ha : raw41044step1 = -raw41044step0 := by apply Matrix.ext; change ∀ i j, raw41044step1 i j = -(raw41044step0 i j); unfold raw41044step1 raw41044step0; decide +kernel
      have hl : raw41044step1Labels = raw41044step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2900 node2900Labels := by rfl

theorem canonical41045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41045 raw41045Labels = mixedMoment B node2797 node2797Labels := by
  calc
    mixedMoment B raw41045 raw41045Labels = mixedMoment B raw41045step0 raw41045step0Labels := by
      have ha : raw41045step0 = (fun i j => raw41045 (permutation644 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41045step0 raw41045; decide +kernel
      have hl : raw41045step0Labels = raw41045Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41045 raw41045Labels permutation644 permutation6
    _ = mixedMoment B node2797 node2797Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1600 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1600) =
      Integer.Sparse.eval keyMomentRow1600 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1600).leftCharge (GramAssembly.key 1600).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3078) := by
    have ha : gramCharges (GramAssembly.key 1600).leftCharge (GramAssembly.key 1600).rightCharge = raw41015 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41015Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41015 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1600).leftCharge (GramAssembly.key 1600).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1600, Integer.Sparse.eval]

theorem keyMoment1601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1601) =
      Integer.Sparse.eval keyMomentRow1601 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1601).leftCharge (GramAssembly.key 1601).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2777) := by
    have ha : gramCharges (GramAssembly.key 1601).leftCharge (GramAssembly.key 1601).rightCharge = raw41016 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41016Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41016 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1601).leftCharge (GramAssembly.key 1601).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1601, Integer.Sparse.eval]

theorem keyMoment1602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1602) =
      Integer.Sparse.eval keyMomentRow1602 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1602).leftCharge (GramAssembly.key 1602).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2942) := by
    have ha : gramCharges (GramAssembly.key 1602).leftCharge (GramAssembly.key 1602).rightCharge = raw41017 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41017Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41017 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1602).leftCharge (GramAssembly.key 1602).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1602, Integer.Sparse.eval]

theorem keyMoment1603 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1603) =
      Integer.Sparse.eval keyMomentRow1603 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1603).leftCharge (GramAssembly.key 1603).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3038) := by
    have ha : gramCharges (GramAssembly.key 1603).leftCharge (GramAssembly.key 1603).rightCharge = raw41018 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41018Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41018 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1603).leftCharge (GramAssembly.key 1603).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1603, Integer.Sparse.eval]

theorem keyMoment1604 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1604) =
      Integer.Sparse.eval keyMomentRow1604 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1604).leftCharge (GramAssembly.key 1604).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3086) := by
    have ha : gramCharges (GramAssembly.key 1604).leftCharge (GramAssembly.key 1604).rightCharge = raw41019 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41019Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41019 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1604).leftCharge (GramAssembly.key 1604).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1604, Integer.Sparse.eval]

theorem keyMoment1605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1605) =
      Integer.Sparse.eval keyMomentRow1605 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1605).leftCharge (GramAssembly.key 1605).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2867) := by
    have ha : gramCharges (GramAssembly.key 1605).leftCharge (GramAssembly.key 1605).rightCharge = raw41020 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41020Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41020 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1605).leftCharge (GramAssembly.key 1605).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1605, Integer.Sparse.eval]

theorem keyMoment1606 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1606) =
      Integer.Sparse.eval keyMomentRow1606 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1606).leftCharge (GramAssembly.key 1606).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2933) := by
    have ha : gramCharges (GramAssembly.key 1606).leftCharge (GramAssembly.key 1606).rightCharge = raw41021 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41021Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41021 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1606).leftCharge (GramAssembly.key 1606).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1606, Integer.Sparse.eval]

theorem keyMoment1607 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1607) =
      Integer.Sparse.eval keyMomentRow1607 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1607).leftCharge (GramAssembly.key 1607).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2916) := by
    have ha : gramCharges (GramAssembly.key 1607).leftCharge (GramAssembly.key 1607).rightCharge = raw41022 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41022Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41022 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1607).leftCharge (GramAssembly.key 1607).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1607, Integer.Sparse.eval]

theorem keyMoment1608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1608) =
      Integer.Sparse.eval keyMomentRow1608 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1608).leftCharge (GramAssembly.key 1608).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2861) := by
    have ha : gramCharges (GramAssembly.key 1608).leftCharge (GramAssembly.key 1608).rightCharge = raw41023 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41023Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41023 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1608).leftCharge (GramAssembly.key 1608).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1608, Integer.Sparse.eval]

theorem keyMoment1609 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1609) =
      Integer.Sparse.eval keyMomentRow1609 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1609).leftCharge (GramAssembly.key 1609).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3064) := by
    have ha : gramCharges (GramAssembly.key 1609).leftCharge (GramAssembly.key 1609).rightCharge = raw41024 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41024Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41024 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1609).leftCharge (GramAssembly.key 1609).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1609, Integer.Sparse.eval]

theorem keyMoment1610 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1610) =
      Integer.Sparse.eval keyMomentRow1610 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1610).leftCharge (GramAssembly.key 1610).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2754) := by
    have ha : gramCharges (GramAssembly.key 1610).leftCharge (GramAssembly.key 1610).rightCharge = raw41025 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41025Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41025 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1610).leftCharge (GramAssembly.key 1610).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1610, Integer.Sparse.eval]

theorem keyMoment1611 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1611) =
      Integer.Sparse.eval keyMomentRow1611 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1611).leftCharge (GramAssembly.key 1611).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2865) := by
    have ha : gramCharges (GramAssembly.key 1611).leftCharge (GramAssembly.key 1611).rightCharge = raw41026 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41026Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41026 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1611).leftCharge (GramAssembly.key 1611).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1611, Integer.Sparse.eval]

theorem keyMoment1612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1612) =
      Integer.Sparse.eval keyMomentRow1612 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1612).leftCharge (GramAssembly.key 1612).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2734) := by
    have ha : gramCharges (GramAssembly.key 1612).leftCharge (GramAssembly.key 1612).rightCharge = raw31649 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw31649Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical31649 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1612).leftCharge (GramAssembly.key 1612).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1612, Integer.Sparse.eval]

theorem keyMoment1613 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1613) =
      Integer.Sparse.eval keyMomentRow1613 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1613).leftCharge (GramAssembly.key 1613).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1243) := by
    have ha : gramCharges (GramAssembly.key 1613).leftCharge (GramAssembly.key 1613).rightCharge = raw41027 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41027Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41027 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1613).leftCharge (GramAssembly.key 1613).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1613, Integer.Sparse.eval]

theorem keyMoment1614 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1614) =
      Integer.Sparse.eval keyMomentRow1614 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1614).leftCharge (GramAssembly.key 1614).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2618) := by
    have ha : gramCharges (GramAssembly.key 1614).leftCharge (GramAssembly.key 1614).rightCharge = raw41028 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41028Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41028 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1614).leftCharge (GramAssembly.key 1614).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1614, Integer.Sparse.eval]

theorem keyMoment1615 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1615) =
      Integer.Sparse.eval keyMomentRow1615 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1615).leftCharge (GramAssembly.key 1615).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1217) := by
    have ha : gramCharges (GramAssembly.key 1615).leftCharge (GramAssembly.key 1615).rightCharge = raw41029 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41029Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41029 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1615).leftCharge (GramAssembly.key 1615).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1615, Integer.Sparse.eval]

theorem keyMoment1616 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1616) =
      Integer.Sparse.eval keyMomentRow1616 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1616).leftCharge (GramAssembly.key 1616).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2558) := by
    have ha : gramCharges (GramAssembly.key 1616).leftCharge (GramAssembly.key 1616).rightCharge = raw41030 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41030Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41030 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1616).leftCharge (GramAssembly.key 1616).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1616, Integer.Sparse.eval]

theorem keyMoment1617 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1617) =
      Integer.Sparse.eval keyMomentRow1617 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1617).leftCharge (GramAssembly.key 1617).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2712) := by
    have ha : gramCharges (GramAssembly.key 1617).leftCharge (GramAssembly.key 1617).rightCharge = raw41031 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41031Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41031 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1617).leftCharge (GramAssembly.key 1617).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1617, Integer.Sparse.eval]

theorem keyMoment1618 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1618) =
      Integer.Sparse.eval keyMomentRow1618 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1618).leftCharge (GramAssembly.key 1618).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2134) := by
    have ha : gramCharges (GramAssembly.key 1618).leftCharge (GramAssembly.key 1618).rightCharge = raw41032 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41032Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41032 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1618).leftCharge (GramAssembly.key 1618).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1618, Integer.Sparse.eval]

theorem keyMoment1619 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1619) =
      Integer.Sparse.eval keyMomentRow1619 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1619).leftCharge (GramAssembly.key 1619).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1825) := by
    have ha : gramCharges (GramAssembly.key 1619).leftCharge (GramAssembly.key 1619).rightCharge = raw41033 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41033Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41033 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1619).leftCharge (GramAssembly.key 1619).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1619, Integer.Sparse.eval]

theorem keyMoment1620 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1620) =
      Integer.Sparse.eval keyMomentRow1620 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1620).leftCharge (GramAssembly.key 1620).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2090) := by
    have ha : gramCharges (GramAssembly.key 1620).leftCharge (GramAssembly.key 1620).rightCharge = raw41034 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41034Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41034 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1620).leftCharge (GramAssembly.key 1620).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1620, Integer.Sparse.eval]

theorem keyMoment1621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1621) =
      Integer.Sparse.eval keyMomentRow1621 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1621).leftCharge (GramAssembly.key 1621).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1808) := by
    have ha : gramCharges (GramAssembly.key 1621).leftCharge (GramAssembly.key 1621).rightCharge = raw41035 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41035Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41035 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1621).leftCharge (GramAssembly.key 1621).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1621, Integer.Sparse.eval]

theorem keyMoment1622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1622) =
      Integer.Sparse.eval keyMomentRow1622 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1622).leftCharge (GramAssembly.key 1622).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1973) := by
    have ha : gramCharges (GramAssembly.key 1622).leftCharge (GramAssembly.key 1622).rightCharge = raw41036 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41036Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41036 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1622).leftCharge (GramAssembly.key 1622).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1622, Integer.Sparse.eval]

theorem keyMoment1623 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1623) =
      Integer.Sparse.eval keyMomentRow1623 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1623).leftCharge (GramAssembly.key 1623).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1790) := by
    have ha : gramCharges (GramAssembly.key 1623).leftCharge (GramAssembly.key 1623).rightCharge = raw41037 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41037Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41037 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1623).leftCharge (GramAssembly.key 1623).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1623, Integer.Sparse.eval]

theorem keyMoment1624 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1624) =
      Integer.Sparse.eval keyMomentRow1624 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1624).leftCharge (GramAssembly.key 1624).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2759) := by
    have ha : gramCharges (GramAssembly.key 1624).leftCharge (GramAssembly.key 1624).rightCharge = raw41038 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41038Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41038 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1624).leftCharge (GramAssembly.key 1624).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1624, Integer.Sparse.eval]

theorem keyMoment1625 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1625) =
      Integer.Sparse.eval keyMomentRow1625 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1625).leftCharge (GramAssembly.key 1625).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2902) := by
    have ha : gramCharges (GramAssembly.key 1625).leftCharge (GramAssembly.key 1625).rightCharge = raw41039 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41039Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41039 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1625).leftCharge (GramAssembly.key 1625).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1625, Integer.Sparse.eval]

theorem keyMoment1626 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1626) =
      Integer.Sparse.eval keyMomentRow1626 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1626).leftCharge (GramAssembly.key 1626).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2984) := by
    have ha : gramCharges (GramAssembly.key 1626).leftCharge (GramAssembly.key 1626).rightCharge = raw41040 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41040Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41040 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1626).leftCharge (GramAssembly.key 1626).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1626, Integer.Sparse.eval]

theorem keyMoment1627 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1627) =
      Integer.Sparse.eval keyMomentRow1627 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1627).leftCharge (GramAssembly.key 1627).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2848) := by
    have ha : gramCharges (GramAssembly.key 1627).leftCharge (GramAssembly.key 1627).rightCharge = raw41041 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41041Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41041 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1627).leftCharge (GramAssembly.key 1627).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1627, Integer.Sparse.eval]

theorem keyMoment1628 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1628) =
      Integer.Sparse.eval keyMomentRow1628 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1628).leftCharge (GramAssembly.key 1628).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2979) := by
    have ha : gramCharges (GramAssembly.key 1628).leftCharge (GramAssembly.key 1628).rightCharge = raw41042 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41042Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41042 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1628).leftCharge (GramAssembly.key 1628).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1628, Integer.Sparse.eval]

theorem keyMoment1629 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1629) =
      Integer.Sparse.eval keyMomentRow1629 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1629).leftCharge (GramAssembly.key 1629).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2811) := by
    have ha : gramCharges (GramAssembly.key 1629).leftCharge (GramAssembly.key 1629).rightCharge = raw41043 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41043Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41043 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1629).leftCharge (GramAssembly.key 1629).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1629, Integer.Sparse.eval]

theorem keyMoment1630 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1630) =
      Integer.Sparse.eval keyMomentRow1630 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1630).leftCharge (GramAssembly.key 1630).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2900) := by
    have ha : gramCharges (GramAssembly.key 1630).leftCharge (GramAssembly.key 1630).rightCharge = raw41044 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41044Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41044 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1630).leftCharge (GramAssembly.key 1630).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1630, Integer.Sparse.eval]

theorem keyMoment1631 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1631) =
      Integer.Sparse.eval keyMomentRow1631 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1631).leftCharge (GramAssembly.key 1631).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2797) := by
    have ha : gramCharges (GramAssembly.key 1631).leftCharge (GramAssembly.key 1631).rightCharge = raw41045 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41045Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41045 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1631).leftCharge (GramAssembly.key 1631).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1631, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1600 : keyMomentRows (1600 : Fin 2886) =
    keyMomentRow1600 := by decide +kernel

theorem keyMomentRowsAt1601 : keyMomentRows (1601 : Fin 2886) =
    keyMomentRow1601 := by decide +kernel

theorem keyMomentRowsAt1602 : keyMomentRows (1602 : Fin 2886) =
    keyMomentRow1602 := by decide +kernel

theorem keyMomentRowsAt1603 : keyMomentRows (1603 : Fin 2886) =
    keyMomentRow1603 := by decide +kernel

theorem keyMomentRowsAt1604 : keyMomentRows (1604 : Fin 2886) =
    keyMomentRow1604 := by decide +kernel

theorem keyMomentRowsAt1605 : keyMomentRows (1605 : Fin 2886) =
    keyMomentRow1605 := by decide +kernel

theorem keyMomentRowsAt1606 : keyMomentRows (1606 : Fin 2886) =
    keyMomentRow1606 := by decide +kernel

theorem keyMomentRowsAt1607 : keyMomentRows (1607 : Fin 2886) =
    keyMomentRow1607 := by decide +kernel

theorem keyMomentRowsAt1608 : keyMomentRows (1608 : Fin 2886) =
    keyMomentRow1608 := by decide +kernel

theorem keyMomentRowsAt1609 : keyMomentRows (1609 : Fin 2886) =
    keyMomentRow1609 := by decide +kernel

theorem keyMomentRowsAt1610 : keyMomentRows (1610 : Fin 2886) =
    keyMomentRow1610 := by decide +kernel

theorem keyMomentRowsAt1611 : keyMomentRows (1611 : Fin 2886) =
    keyMomentRow1611 := by decide +kernel

theorem keyMomentRowsAt1612 : keyMomentRows (1612 : Fin 2886) =
    keyMomentRow1612 := by decide +kernel

theorem keyMomentRowsAt1613 : keyMomentRows (1613 : Fin 2886) =
    keyMomentRow1613 := by decide +kernel

theorem keyMomentRowsAt1614 : keyMomentRows (1614 : Fin 2886) =
    keyMomentRow1614 := by decide +kernel

theorem keyMomentRowsAt1615 : keyMomentRows (1615 : Fin 2886) =
    keyMomentRow1615 := by decide +kernel

theorem keyMomentRowsAt1616 : keyMomentRows (1616 : Fin 2886) =
    keyMomentRow1616 := by decide +kernel

theorem keyMomentRowsAt1617 : keyMomentRows (1617 : Fin 2886) =
    keyMomentRow1617 := by decide +kernel

theorem keyMomentRowsAt1618 : keyMomentRows (1618 : Fin 2886) =
    keyMomentRow1618 := by decide +kernel

theorem keyMomentRowsAt1619 : keyMomentRows (1619 : Fin 2886) =
    keyMomentRow1619 := by decide +kernel

theorem keyMomentRowsAt1620 : keyMomentRows (1620 : Fin 2886) =
    keyMomentRow1620 := by decide +kernel

theorem keyMomentRowsAt1621 : keyMomentRows (1621 : Fin 2886) =
    keyMomentRow1621 := by decide +kernel

theorem keyMomentRowsAt1622 : keyMomentRows (1622 : Fin 2886) =
    keyMomentRow1622 := by decide +kernel

theorem keyMomentRowsAt1623 : keyMomentRows (1623 : Fin 2886) =
    keyMomentRow1623 := by decide +kernel

theorem keyMomentRowsAt1624 : keyMomentRows (1624 : Fin 2886) =
    keyMomentRow1624 := by decide +kernel

theorem keyMomentRowsAt1625 : keyMomentRows (1625 : Fin 2886) =
    keyMomentRow1625 := by decide +kernel

theorem keyMomentRowsAt1626 : keyMomentRows (1626 : Fin 2886) =
    keyMomentRow1626 := by decide +kernel

theorem keyMomentRowsAt1627 : keyMomentRows (1627 : Fin 2886) =
    keyMomentRow1627 := by decide +kernel

theorem keyMomentRowsAt1628 : keyMomentRows (1628 : Fin 2886) =
    keyMomentRow1628 := by decide +kernel

theorem keyMomentRowsAt1629 : keyMomentRows (1629 : Fin 2886) =
    keyMomentRow1629 := by decide +kernel

theorem keyMomentRowsAt1630 : keyMomentRows (1630 : Fin 2886) =
    keyMomentRow1630 := by decide +kernel

theorem keyMomentRowsAt1631 : keyMomentRows (1631 : Fin 2886) =
    keyMomentRow1631 := by decide +kernel

theorem keyMomentChunkSound50_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 50) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1600 ∨ k.val = 1601 ∨ k.val = 1602 ∨ k.val = 1603 ∨ k.val = 1604 ∨ k.val = 1605 ∨ k.val = 1606 ∨ k.val = 1607 ∨ k.val = 1608 ∨ k.val = 1609 ∨ k.val = 1610 ∨ k.val = 1611 ∨ k.val = 1612 ∨ k.val = 1613 ∨ k.val = 1614 ∨ k.val = 1615 ∨ k.val = 1616 ∨ k.val = 1617 ∨ k.val = 1618 ∨ k.val = 1619 ∨ k.val = 1620 ∨ k.val = 1621 ∨ k.val = 1622 ∨ k.val = 1623 ∨ k.val = 1624 ∨ k.val = 1625 ∨ k.val = 1626 ∨ k.val = 1627 ∨ k.val = 1628 ∨ k.val = 1629 ∨ k.val = 1630 ∨ k.val = 1631 := by omega
  rcases heq with h1600 | h1601 | h1602 | h1603 | h1604 | h1605 | h1606 | h1607 | h1608 | h1609 | h1610 | h1611 | h1612 | h1613 | h1614 | h1615 | h1616 | h1617 | h1618 | h1619 | h1620 | h1621 | h1622 | h1623 | h1624 | h1625 | h1626 | h1627 | h1628 | h1629 | h1630 | h1631
  · have he : k = (1600 : Fin 2886) := Fin.ext h1600
    subst k
    rw [keyMomentRowsAt1600]
    exact keyMoment1600 B hB
  · have he : k = (1601 : Fin 2886) := Fin.ext h1601
    subst k
    rw [keyMomentRowsAt1601]
    exact keyMoment1601 B hB
  · have he : k = (1602 : Fin 2886) := Fin.ext h1602
    subst k
    rw [keyMomentRowsAt1602]
    exact keyMoment1602 B hB
  · have he : k = (1603 : Fin 2886) := Fin.ext h1603
    subst k
    rw [keyMomentRowsAt1603]
    exact keyMoment1603 B hB
  · have he : k = (1604 : Fin 2886) := Fin.ext h1604
    subst k
    rw [keyMomentRowsAt1604]
    exact keyMoment1604 B hB
  · have he : k = (1605 : Fin 2886) := Fin.ext h1605
    subst k
    rw [keyMomentRowsAt1605]
    exact keyMoment1605 B hB
  · have he : k = (1606 : Fin 2886) := Fin.ext h1606
    subst k
    rw [keyMomentRowsAt1606]
    exact keyMoment1606 B hB
  · have he : k = (1607 : Fin 2886) := Fin.ext h1607
    subst k
    rw [keyMomentRowsAt1607]
    exact keyMoment1607 B hB
  · have he : k = (1608 : Fin 2886) := Fin.ext h1608
    subst k
    rw [keyMomentRowsAt1608]
    exact keyMoment1608 B hB
  · have he : k = (1609 : Fin 2886) := Fin.ext h1609
    subst k
    rw [keyMomentRowsAt1609]
    exact keyMoment1609 B hB
  · have he : k = (1610 : Fin 2886) := Fin.ext h1610
    subst k
    rw [keyMomentRowsAt1610]
    exact keyMoment1610 B hB
  · have he : k = (1611 : Fin 2886) := Fin.ext h1611
    subst k
    rw [keyMomentRowsAt1611]
    exact keyMoment1611 B hB
  · have he : k = (1612 : Fin 2886) := Fin.ext h1612
    subst k
    rw [keyMomentRowsAt1612]
    exact keyMoment1612 B hB
  · have he : k = (1613 : Fin 2886) := Fin.ext h1613
    subst k
    rw [keyMomentRowsAt1613]
    exact keyMoment1613 B hB
  · have he : k = (1614 : Fin 2886) := Fin.ext h1614
    subst k
    rw [keyMomentRowsAt1614]
    exact keyMoment1614 B hB
  · have he : k = (1615 : Fin 2886) := Fin.ext h1615
    subst k
    rw [keyMomentRowsAt1615]
    exact keyMoment1615 B hB
  · have he : k = (1616 : Fin 2886) := Fin.ext h1616
    subst k
    rw [keyMomentRowsAt1616]
    exact keyMoment1616 B hB
  · have he : k = (1617 : Fin 2886) := Fin.ext h1617
    subst k
    rw [keyMomentRowsAt1617]
    exact keyMoment1617 B hB
  · have he : k = (1618 : Fin 2886) := Fin.ext h1618
    subst k
    rw [keyMomentRowsAt1618]
    exact keyMoment1618 B hB
  · have he : k = (1619 : Fin 2886) := Fin.ext h1619
    subst k
    rw [keyMomentRowsAt1619]
    exact keyMoment1619 B hB
  · have he : k = (1620 : Fin 2886) := Fin.ext h1620
    subst k
    rw [keyMomentRowsAt1620]
    exact keyMoment1620 B hB
  · have he : k = (1621 : Fin 2886) := Fin.ext h1621
    subst k
    rw [keyMomentRowsAt1621]
    exact keyMoment1621 B hB
  · have he : k = (1622 : Fin 2886) := Fin.ext h1622
    subst k
    rw [keyMomentRowsAt1622]
    exact keyMoment1622 B hB
  · have he : k = (1623 : Fin 2886) := Fin.ext h1623
    subst k
    rw [keyMomentRowsAt1623]
    exact keyMoment1623 B hB
  · have he : k = (1624 : Fin 2886) := Fin.ext h1624
    subst k
    rw [keyMomentRowsAt1624]
    exact keyMoment1624 B hB
  · have he : k = (1625 : Fin 2886) := Fin.ext h1625
    subst k
    rw [keyMomentRowsAt1625]
    exact keyMoment1625 B hB
  · have he : k = (1626 : Fin 2886) := Fin.ext h1626
    subst k
    rw [keyMomentRowsAt1626]
    exact keyMoment1626 B hB
  · have he : k = (1627 : Fin 2886) := Fin.ext h1627
    subst k
    rw [keyMomentRowsAt1627]
    exact keyMoment1627 B hB
  · have he : k = (1628 : Fin 2886) := Fin.ext h1628
    subst k
    rw [keyMomentRowsAt1628]
    exact keyMoment1628 B hB
  · have he : k = (1629 : Fin 2886) := Fin.ext h1629
    subst k
    rw [keyMomentRowsAt1629]
    exact keyMoment1629 B hB
  · have he : k = (1630 : Fin 2886) := Fin.ext h1630
    subst k
    rw [keyMomentRowsAt1630]
    exact keyMoment1630 B hB
  · have he : k = (1631 : Fin 2886) := Fin.ext h1631
    subst k
    rw [keyMomentRowsAt1631]
    exact keyMoment1631 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound50_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound50_e_oai
