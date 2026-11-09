-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound27_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:50:04.378646+00:00
-- url     : https://prove2.me/submissions/25ce7a5d-fa4f-4efe-91de-ef1c3072d290

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E111
import Definitions.Def_OAIQ106E114
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical314
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40307 raw40307Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw40307 raw40307Labels = mixedMoment B raw40307step0 raw40307step0Labels := by
      have hz : ∀ j, raw40307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40307step0 = (fun i j => raw40307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40307step0 raw40307; decide +kernel
      have hl : raw40307step0Labels = raw40307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40307 raw40307Labels permutation434 hz
    mixedMoment B raw40307step0 raw40307step0Labels = mixedMoment B raw40307step1 raw40307step1Labels := by
      have hz : ∀ j, raw40307step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40307step1 = (fun i j => raw40307step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40307step1 raw40307step0; decide +kernel
      have hl : raw40307step1Labels = raw40307step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40307step0 raw40307step0Labels permutation80 hz
    mixedMoment B raw40307step1 raw40307step1Labels = mixedMoment B raw40307step2 raw40307step2Labels := by
      have ha : raw40307step2 = (fun i j => raw40307step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40307step2 raw40307step1; decide +kernel
      have hl : raw40307step2Labels = raw40307step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40307step1 raw40307step1Labels permutation8 permutation3
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical40308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40308 raw40308Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw40308 raw40308Labels = mixedMoment B raw40308step0 raw40308step0Labels := by
      have hz : ∀ j, raw40308 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40308step0 = (fun i j => raw40308 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40308step0 raw40308; decide +kernel
      have hl : raw40308step0Labels = raw40308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40308 raw40308Labels permutation434 hz
    mixedMoment B raw40308step0 raw40308step0Labels = mixedMoment B raw40308step1 raw40308step1Labels := by
      have hz : ∀ j, raw40308step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40308step1 = (fun i j => raw40308step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40308step1 raw40308step0; decide +kernel
      have hl : raw40308step1Labels = raw40308step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40308step0 raw40308step0Labels permutation80 hz
    mixedMoment B raw40308step1 raw40308step1Labels = mixedMoment B raw40308step2 raw40308step2Labels := by
      have ha : raw40308step2 = (fun i j => raw40308step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40308step2 raw40308step1; decide +kernel
      have hl : raw40308step2Labels = raw40308step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40308step1 raw40308step1Labels permutation8 permutation3
    _ = mixedMoment B node2744 node2744Labels := by rfl

theorem canonical40309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40309 raw40309Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw40309 raw40309Labels = mixedMoment B raw40309step0 raw40309step0Labels := by
      have hz : ∀ j, raw40309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40309step0 = (fun i j => raw40309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40309step0 raw40309; decide +kernel
      have hl : raw40309step0Labels = raw40309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40309 raw40309Labels permutation346 hz
    mixedMoment B raw40309step0 raw40309step0Labels = mixedMoment B raw40309step1 raw40309step1Labels := by
      have ha : raw40309step1 = (fun i j => raw40309step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40309step1 raw40309step0; decide +kernel
      have hl : raw40309step1Labels = raw40309step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40309step0 raw40309step0Labels permutation32 permutation3
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical40310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40310 raw40310Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw40310 raw40310Labels = mixedMoment B raw40310step0 raw40310step0Labels := by
      have hz : ∀ j, raw40310 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40310step0 = (fun i j => raw40310 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40310step0 raw40310; decide +kernel
      have hl : raw40310step0Labels = raw40310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40310 raw40310Labels permutation346 hz
    mixedMoment B raw40310step0 raw40310step0Labels = mixedMoment B raw40310step1 raw40310step1Labels := by
      have ha : raw40310step1 = (fun i j => raw40310step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40310step1 raw40310step0; decide +kernel
      have hl : raw40310step1Labels = raw40310step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40310step0 raw40310step0Labels permutation32 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical40311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40311 raw40311Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw40311 raw40311Labels = mixedMoment B raw40311step0 raw40311step0Labels := by
      have hz : ∀ j, raw40311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40311step0 = (fun i j => raw40311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40311step0 raw40311; decide +kernel
      have hl : raw40311step0Labels = raw40311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40311 raw40311Labels permutation346 hz
    mixedMoment B raw40311step0 raw40311step0Labels = mixedMoment B raw40311step1 raw40311step1Labels := by
      have ha : raw40311step1 = (fun i j => raw40311step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40311step1 raw40311step0; decide +kernel
      have hl : raw40311step1Labels = raw40311step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40311step0 raw40311step0Labels permutation32 permutation3
    _ = mixedMoment B node2724 node2724Labels := by rfl

theorem canonical40312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40312 raw40312Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw40312 raw40312Labels = mixedMoment B raw40312step0 raw40312step0Labels := by
      have hz : ∀ j, raw40312 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40312step0 = (fun i j => raw40312 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40312step0 raw40312; decide +kernel
      have hl : raw40312step0Labels = raw40312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40312 raw40312Labels permutation346 hz
    mixedMoment B raw40312step0 raw40312step0Labels = mixedMoment B raw40312step1 raw40312step1Labels := by
      have ha : raw40312step1 = (fun i j => raw40312step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40312step1 raw40312step0; decide +kernel
      have hl : raw40312step1Labels = raw40312step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40312step0 raw40312step0Labels permutation32 permutation3
    _ = mixedMoment B node2731 node2731Labels := by rfl

theorem canonical40313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40313 raw40313Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw40313 raw40313Labels = mixedMoment B raw40313step0 raw40313step0Labels := by
      have hz : ∀ j, raw40313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40313step0 = (fun i j => raw40313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40313step0 raw40313; decide +kernel
      have hl : raw40313step0Labels = raw40313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40313 raw40313Labels permutation346 hz
    mixedMoment B raw40313step0 raw40313step0Labels = mixedMoment B raw40313step1 raw40313step1Labels := by
      have ha : raw40313step1 = (fun i j => raw40313step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40313step1 raw40313step0; decide +kernel
      have hl : raw40313step1Labels = raw40313step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40313step0 raw40313step0Labels permutation32 permutation3
    _ = mixedMoment B node2732 node2732Labels := by rfl

theorem canonical40314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40314 raw40314Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw40314 raw40314Labels = mixedMoment B raw40314step0 raw40314step0Labels := by
      have hz : ∀ j, raw40314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40314step0 = (fun i j => raw40314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40314step0 raw40314; decide +kernel
      have hl : raw40314step0Labels = raw40314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40314 raw40314Labels permutation346 hz
    mixedMoment B raw40314step0 raw40314step0Labels = mixedMoment B raw40314step1 raw40314step1Labels := by
      have ha : raw40314step1 = (fun i j => raw40314step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40314step1 raw40314step0; decide +kernel
      have hl : raw40314step1Labels = raw40314step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40314step0 raw40314step0Labels permutation32 permutation3
    _ = mixedMoment B node2738 node2738Labels := by rfl

theorem canonical40315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40315 raw40315Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw40315 raw40315Labels = mixedMoment B raw40315step0 raw40315step0Labels := by
      have hz : ∀ j, raw40315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40315step0 = (fun i j => raw40315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40315step0 raw40315; decide +kernel
      have hl : raw40315step0Labels = raw40315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40315 raw40315Labels permutation346 hz
    mixedMoment B raw40315step0 raw40315step0Labels = mixedMoment B raw40315step1 raw40315step1Labels := by
      have ha : raw40315step1 = (fun i j => raw40315step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40315step1 raw40315step0; decide +kernel
      have hl : raw40315step1Labels = raw40315step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40315step0 raw40315step0Labels permutation32 permutation3
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical40316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40316 raw40316Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw40316 raw40316Labels = mixedMoment B raw40316step0 raw40316step0Labels := by
      have hz : ∀ j, raw40316 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40316step0 = (fun i j => raw40316 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40316step0 raw40316; decide +kernel
      have hl : raw40316step0Labels = raw40316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40316 raw40316Labels permutation346 hz
    mixedMoment B raw40316step0 raw40316step0Labels = mixedMoment B raw40316step1 raw40316step1Labels := by
      have ha : raw40316step1 = (fun i j => raw40316step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40316step1 raw40316step0; decide +kernel
      have hl : raw40316step1Labels = raw40316step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40316step0 raw40316step0Labels permutation32 permutation3
    _ = mixedMoment B node2741 node2741Labels := by rfl

theorem canonical40317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40317 raw40317Labels = mixedMoment B node2709 node2709Labels := by
  calc
    mixedMoment B raw40317 raw40317Labels = mixedMoment B raw40317step0 raw40317step0Labels := by
      have ha : raw40317step0 = (fun i j => raw40317 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40317step0 raw40317; decide +kernel
      have hl : raw40317step0Labels = raw40317Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40317 raw40317Labels permutation152 permutation3
    _ = mixedMoment B node2709 node2709Labels := by rfl

theorem canonical40318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40318 raw40318Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw40318 raw40318Labels = mixedMoment B raw40318step0 raw40318step0Labels := by
      have ha : raw40318step0 = (fun i j => raw40318 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40318step0 raw40318; decide +kernel
      have hl : raw40318step0Labels = raw40318Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40318 raw40318Labels permutation152 permutation3
    _ = mixedMoment B node2710 node2710Labels := by rfl

theorem canonical40319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40319 raw40319Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw40319 raw40319Labels = mixedMoment B raw40319step0 raw40319step0Labels := by
      have ha : raw40319step0 = (fun i j => raw40319 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40319step0 raw40319; decide +kernel
      have hl : raw40319step0Labels = raw40319Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40319 raw40319Labels permutation152 permutation3
    _ = mixedMoment B node2720 node2720Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical315
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40320 raw40320Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw40320 raw40320Labels = mixedMoment B raw40320step0 raw40320step0Labels := by
      have ha : raw40320step0 = (fun i j => raw40320 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40320step0 raw40320; decide +kernel
      have hl : raw40320step0Labels = raw40320Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40320 raw40320Labels permutation152 permutation3
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical40321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40321 raw40321Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw40321 raw40321Labels = mixedMoment B raw40321step0 raw40321step0Labels := by
      have ha : raw40321step0 = (fun i j => raw40321 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40321step0 raw40321; decide +kernel
      have hl : raw40321step0Labels = raw40321Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40321 raw40321Labels permutation152 permutation3
    _ = mixedMoment B node2730 node2730Labels := by rfl

theorem canonical40322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40322 raw40322Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw40322 raw40322Labels = mixedMoment B raw40322step0 raw40322step0Labels := by
      have hz : ∀ j, raw40322 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40322step0 = (fun i j => raw40322 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40322step0 raw40322; decide +kernel
      have hl : raw40322step0Labels = raw40322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40322 raw40322Labels permutation434 hz
    mixedMoment B raw40322step0 raw40322step0Labels = mixedMoment B raw40322step1 raw40322step1Labels := by
      have hz : ∀ j, raw40322step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40322step1 = (fun i j => raw40322step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40322step1 raw40322step0; decide +kernel
      have hl : raw40322step1Labels = raw40322step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40322step0 raw40322step0Labels permutation80 hz
    mixedMoment B raw40322step1 raw40322step1Labels = mixedMoment B raw40322step2 raw40322step2Labels := by
      have hz : ∀ j, raw40322step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40322step2 = (fun i j => raw40322step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40322step2 raw40322step1; decide +kernel
      have hl : raw40322step2Labels = raw40322step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40322step1 raw40322step1Labels permutation14 hz
    mixedMoment B raw40322step2 raw40322step2Labels = mixedMoment B raw40322step3 raw40322step3Labels := by
      have ha : raw40322step3 = (fun i j => raw40322step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40322step3 raw40322step2; decide +kernel
      have hl : raw40322step3Labels = raw40322step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40322step2 raw40322step2Labels permutation2 permutation3
    _ = mixedMoment B node2783 node2783Labels := by rfl

theorem canonical40323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40323 raw40323Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw40323 raw40323Labels = mixedMoment B raw40323step0 raw40323step0Labels := by
      have hz : ∀ j, raw40323 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40323step0 = (fun i j => raw40323 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40323step0 raw40323; decide +kernel
      have hl : raw40323step0Labels = raw40323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40323 raw40323Labels permutation346 hz
    mixedMoment B raw40323step0 raw40323step0Labels = mixedMoment B raw40323step1 raw40323step1Labels := by
      have hz : ∀ j, raw40323step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40323step1 = (fun i j => raw40323step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40323step1 raw40323step0; decide +kernel
      have hl : raw40323step1Labels = raw40323step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40323step0 raw40323step0Labels permutation56 hz
    mixedMoment B raw40323step1 raw40323step1Labels = mixedMoment B raw40323step2 raw40323step2Labels := by
      have ha : raw40323step2 = (fun i j => raw40323step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40323step2 raw40323step1; decide +kernel
      have hl : raw40323step2Labels = raw40323step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40323step1 raw40323step1Labels permutation8 permutation3
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical40324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40324 raw40324Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw40324 raw40324Labels = mixedMoment B raw40324step0 raw40324step0Labels := by
      have hz : ∀ j, raw40324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40324step0 = (fun i j => raw40324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40324step0 raw40324; decide +kernel
      have hl : raw40324step0Labels = raw40324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40324 raw40324Labels permutation346 hz
    mixedMoment B raw40324step0 raw40324step0Labels = mixedMoment B raw40324step1 raw40324step1Labels := by
      have hz : ∀ j, raw40324step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40324step1 = (fun i j => raw40324step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40324step1 raw40324step0; decide +kernel
      have hl : raw40324step1Labels = raw40324step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40324step0 raw40324step0Labels permutation56 hz
    mixedMoment B raw40324step1 raw40324step1Labels = mixedMoment B raw40324step2 raw40324step2Labels := by
      have ha : raw40324step2 = (fun i j => raw40324step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40324step2 raw40324step1; decide +kernel
      have hl : raw40324step2Labels = raw40324step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40324step1 raw40324step1Labels permutation8 permutation3
    _ = mixedMoment B node2774 node2774Labels := by rfl

theorem canonical40325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40325 raw40325Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw40325 raw40325Labels = mixedMoment B raw40325step0 raw40325step0Labels := by
      have hz : ∀ j, raw40325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40325step0 = (fun i j => raw40325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40325step0 raw40325; decide +kernel
      have hl : raw40325step0Labels = raw40325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40325 raw40325Labels permutation346 hz
    mixedMoment B raw40325step0 raw40325step0Labels = mixedMoment B raw40325step1 raw40325step1Labels := by
      have hz : ∀ j, raw40325step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40325step1 = (fun i j => raw40325step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40325step1 raw40325step0; decide +kernel
      have hl : raw40325step1Labels = raw40325step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40325step0 raw40325step0Labels permutation56 hz
    mixedMoment B raw40325step1 raw40325step1Labels = mixedMoment B raw40325step2 raw40325step2Labels := by
      have ha : raw40325step2 = (fun i j => raw40325step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40325step2 raw40325step1; decide +kernel
      have hl : raw40325step2Labels = raw40325step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40325step1 raw40325step1Labels permutation8 permutation3
    _ = mixedMoment B node2777 node2777Labels := by rfl

theorem canonical40326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40326 raw40326Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw40326 raw40326Labels = mixedMoment B raw40326step0 raw40326step0Labels := by
      have hz : ∀ j, raw40326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40326step0 = (fun i j => raw40326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40326step0 raw40326; decide +kernel
      have hl : raw40326step0Labels = raw40326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40326 raw40326Labels permutation346 hz
    mixedMoment B raw40326step0 raw40326step0Labels = mixedMoment B raw40326step1 raw40326step1Labels := by
      have hz : ∀ j, raw40326step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40326step1 = (fun i j => raw40326step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40326step1 raw40326step0; decide +kernel
      have hl : raw40326step1Labels = raw40326step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40326step0 raw40326step0Labels permutation56 hz
    mixedMoment B raw40326step1 raw40326step1Labels = mixedMoment B raw40326step2 raw40326step2Labels := by
      have ha : raw40326step2 = (fun i j => raw40326step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40326step2 raw40326step1; decide +kernel
      have hl : raw40326step2Labels = raw40326step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40326step1 raw40326step1Labels permutation8 permutation3
    _ = mixedMoment B node2781 node2781Labels := by rfl

theorem canonical40327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40327 raw40327Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw40327 raw40327Labels = mixedMoment B raw40327step0 raw40327step0Labels := by
      have hz : ∀ j, raw40327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40327step0 = (fun i j => raw40327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40327step0 raw40327; decide +kernel
      have hl : raw40327step0Labels = raw40327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40327 raw40327Labels permutation346 hz
    mixedMoment B raw40327step0 raw40327step0Labels = mixedMoment B raw40327step1 raw40327step1Labels := by
      have hz : ∀ j, raw40327step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40327step1 = (fun i j => raw40327step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40327step1 raw40327step0; decide +kernel
      have hl : raw40327step1Labels = raw40327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40327step0 raw40327step0Labels permutation56 hz
    mixedMoment B raw40327step1 raw40327step1Labels = mixedMoment B raw40327step2 raw40327step2Labels := by
      have ha : raw40327step2 = (fun i j => raw40327step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40327step2 raw40327step1; decide +kernel
      have hl : raw40327step2Labels = raw40327step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40327step1 raw40327step1Labels permutation8 permutation3
    _ = mixedMoment B node2782 node2782Labels := by rfl

theorem canonical40328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40328 raw40328Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw40328 raw40328Labels = mixedMoment B raw40328step0 raw40328step0Labels := by
      have hz : ∀ j, raw40328 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40328step0 = (fun i j => raw40328 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40328step0 raw40328; decide +kernel
      have hl : raw40328step0Labels = raw40328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40328 raw40328Labels permutation265 hz
    mixedMoment B raw40328step0 raw40328step0Labels = mixedMoment B raw40328step1 raw40328step1Labels := by
      have ha : raw40328step1 = (fun i j => raw40328step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40328step1 raw40328step0; decide +kernel
      have hl : raw40328step1Labels = raw40328step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40328step0 raw40328step0Labels permutation32 permutation3
    _ = mixedMoment B node2751 node2751Labels := by rfl

theorem canonical40329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40329 raw40329Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw40329 raw40329Labels = mixedMoment B raw40329step0 raw40329step0Labels := by
      have hz : ∀ j, raw40329 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40329step0 = (fun i j => raw40329 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40329step0 raw40329; decide +kernel
      have hl : raw40329step0Labels = raw40329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40329 raw40329Labels permutation265 hz
    mixedMoment B raw40329step0 raw40329step0Labels = mixedMoment B raw40329step1 raw40329step1Labels := by
      have ha : raw40329step1 = (fun i j => raw40329step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40329step1 raw40329step0; decide +kernel
      have hl : raw40329step1Labels = raw40329step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40329step0 raw40329step0Labels permutation32 permutation3
    _ = mixedMoment B node2754 node2754Labels := by rfl

theorem canonical40330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40330 raw40330Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw40330 raw40330Labels = mixedMoment B raw40330step0 raw40330step0Labels := by
      have hz : ∀ j, raw40330 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40330step0 = (fun i j => raw40330 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40330step0 raw40330; decide +kernel
      have hl : raw40330step0Labels = raw40330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40330 raw40330Labels permutation265 hz
    mixedMoment B raw40330step0 raw40330step0Labels = mixedMoment B raw40330step1 raw40330step1Labels := by
      have ha : raw40330step1 = (fun i j => raw40330step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40330step1 raw40330step0; decide +kernel
      have hl : raw40330step1Labels = raw40330step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40330step0 raw40330step0Labels permutation32 permutation3
    _ = mixedMoment B node2763 node2763Labels := by rfl

theorem canonical40331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40331 raw40331Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw40331 raw40331Labels = mixedMoment B raw40331step0 raw40331step0Labels := by
      have hz : ∀ j, raw40331 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40331step0 = (fun i j => raw40331 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40331step0 raw40331; decide +kernel
      have hl : raw40331step0Labels = raw40331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40331 raw40331Labels permutation265 hz
    mixedMoment B raw40331step0 raw40331step0Labels = mixedMoment B raw40331step1 raw40331step1Labels := by
      have ha : raw40331step1 = (fun i j => raw40331step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40331step1 raw40331step0; decide +kernel
      have hl : raw40331step1Labels = raw40331step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40331step0 raw40331step0Labels permutation32 permutation3
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical40332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40332 raw40332Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw40332 raw40332Labels = mixedMoment B raw40332step0 raw40332step0Labels := by
      have hz : ∀ j, raw40332 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40332step0 = (fun i j => raw40332 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40332step0 raw40332; decide +kernel
      have hl : raw40332step0Labels = raw40332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40332 raw40332Labels permutation265 hz
    mixedMoment B raw40332step0 raw40332step0Labels = mixedMoment B raw40332step1 raw40332step1Labels := by
      have ha : raw40332step1 = (fun i j => raw40332step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40332step1 raw40332step0; decide +kernel
      have hl : raw40332step1Labels = raw40332step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40332step0 raw40332step0Labels permutation32 permutation3
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical40333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40333 raw40333Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw40333 raw40333Labels = mixedMoment B raw40333step0 raw40333step0Labels := by
      have ha : raw40333step0 = (fun i j => raw40333 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40333step0 raw40333; decide +kernel
      have hl : raw40333step0Labels = raw40333Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40333 raw40333Labels permutation152 permutation3
    _ = mixedMoment B node2750 node2750Labels := by rfl

theorem canonical40334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40334 raw40334Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw40334 raw40334Labels = mixedMoment B raw40334step0 raw40334step0Labels := by
      have hz : ∀ j, raw40334 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40334step0 = (fun i j => raw40334 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40334step0 raw40334; decide +kernel
      have hl : raw40334step0Labels = raw40334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40334 raw40334Labels permutation520 hz
    mixedMoment B raw40334step0 raw40334step0Labels = mixedMoment B raw40334step1 raw40334step1Labels := by
      have hz : ∀ j, raw40334step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40334step1 = (fun i j => raw40334step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40334step1 raw40334step0; decide +kernel
      have hl : raw40334step1Labels = raw40334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40334step0 raw40334step0Labels permutation104 hz
    mixedMoment B raw40334step1 raw40334step1Labels = mixedMoment B raw40334step2 raw40334step2Labels := by
      have hz : ∀ j, raw40334step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40334step2 = (fun i j => raw40334step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40334step2 raw40334step1; decide +kernel
      have hl : raw40334step2Labels = raw40334step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40334step1 raw40334step1Labels permutation20 hz
    mixedMoment B raw40334step2 raw40334step2Labels = mixedMoment B raw40334step3 raw40334step3Labels := by
      have ha : raw40334step3 = (fun i j => raw40334step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40334step3 raw40334step2; decide +kernel
      have hl : raw40334step3Labels = raw40334step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40334step2 raw40334step2Labels permutation7 permutation3
    mixedMoment B raw40334step3 raw40334step3Labels = mixedMoment B raw40334step4 raw40334step4Labels := by
      have ha : raw40334step4 = -raw40334step3 := by apply Matrix.ext; change ∀ i j, raw40334step4 i j = -(raw40334step3 i j); unfold raw40334step4 raw40334step3; decide +kernel
      have hl : raw40334step4Labels = raw40334step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2281 node2281Labels := by rfl

theorem canonical40335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40335 raw40335Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw40335 raw40335Labels = mixedMoment B raw40335step0 raw40335step0Labels := by
      have hz : ∀ j, raw40335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40335step0 = (fun i j => raw40335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40335step0 raw40335; decide +kernel
      have hl : raw40335step0Labels = raw40335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40335 raw40335Labels permutation434 hz
    mixedMoment B raw40335step0 raw40335step0Labels = mixedMoment B raw40335step1 raw40335step1Labels := by
      have hz : ∀ j, raw40335step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40335step1 = (fun i j => raw40335step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40335step1 raw40335step0; decide +kernel
      have hl : raw40335step1Labels = raw40335step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40335step0 raw40335step0Labels permutation80 hz
    mixedMoment B raw40335step1 raw40335step1Labels = mixedMoment B raw40335step2 raw40335step2Labels := by
      have ha : raw40335step2 = (fun i j => raw40335step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40335step2 raw40335step1; decide +kernel
      have hl : raw40335step2Labels = raw40335step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40335step1 raw40335step1Labels permutation31 permutation3
    mixedMoment B raw40335step2 raw40335step2Labels = mixedMoment B raw40335step3 raw40335step3Labels := by
      have ha : raw40335step3 = -raw40335step2 := by apply Matrix.ext; change ∀ i j, raw40335step3 i j = -(raw40335step2 i j); unfold raw40335step3 raw40335step2; decide +kernel
      have hl : raw40335step3Labels = raw40335step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2734 node2734Labels := by rfl

theorem canonical40336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40336 raw40336Labels = mixedMoment B node3046 node3046Labels := by
  calc
    mixedMoment B raw40336 raw40336Labels = mixedMoment B raw40336step0 raw40336step0Labels := by
      have hz : ∀ j, raw40336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40336step0 = (fun i j => raw40336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40336step0 raw40336; decide +kernel
      have hl : raw40336step0Labels = raw40336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40336 raw40336Labels permutation434 hz
    mixedMoment B raw40336step0 raw40336step0Labels = mixedMoment B raw40336step1 raw40336step1Labels := by
      have hz : ∀ j, raw40336step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40336step1 = (fun i j => raw40336step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40336step1 raw40336step0; decide +kernel
      have hl : raw40336step1Labels = raw40336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40336step0 raw40336step0Labels permutation80 hz
    mixedMoment B raw40336step1 raw40336step1Labels = mixedMoment B raw40336step2 raw40336step2Labels := by
      have ha : raw40336step2 = (fun i j => raw40336step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40336step2 raw40336step1; decide +kernel
      have hl : raw40336step2Labels = raw40336step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40336step1 raw40336step1Labels permutation8 permutation3
    _ = mixedMoment B node3046 node3046Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4485 raw4485Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw4485 raw4485Labels = mixedMoment B raw4485step0 raw4485step0Labels := by
      have hz : ∀ j, raw4485 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4485step0 = (fun i j => raw4485 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4485step0 raw4485; decide +kernel
      have hl : raw4485step0Labels = raw4485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4485 raw4485Labels permutation434 hz
    mixedMoment B raw4485step0 raw4485step0Labels = mixedMoment B raw4485step1 raw4485step1Labels := by
      have hz : ∀ j, raw4485step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4485step1 = (fun i j => raw4485step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4485step1 raw4485step0; decide +kernel
      have hl : raw4485step1Labels = raw4485step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4485step0 raw4485step0Labels permutation80 hz
    mixedMoment B raw4485step1 raw4485step1Labels = mixedMoment B raw4485step2 raw4485step2Labels := by
      have hz : ∀ j, raw4485step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4485step2 = (fun i j => raw4485step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4485step2 raw4485step1; decide +kernel
      have hl : raw4485step2Labels = raw4485step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4485step1 raw4485step1Labels permutation14 hz
    mixedMoment B raw4485step2 raw4485step2Labels = mixedMoment B raw4485step3 raw4485step3Labels := by
      have ha : raw4485step3 = (fun i j => raw4485step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4485step3 raw4485step2; decide +kernel
      have hl : raw4485step3Labels = raw4485step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4485step2 raw4485step2Labels permutation2 permutation3
    _ = mixedMoment B node2789 node2789Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4702 raw4702Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw4702 raw4702Labels = mixedMoment B raw4702step0 raw4702step0Labels := by
      have hz : ∀ j, raw4702 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4702step0 = (fun i j => raw4702 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4702step0 raw4702; decide +kernel
      have hl : raw4702step0Labels = raw4702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4702 raw4702Labels permutation346 hz
    mixedMoment B raw4702step0 raw4702step0Labels = mixedMoment B raw4702step1 raw4702step1Labels := by
      have hz : ∀ j, raw4702step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4702step1 = (fun i j => raw4702step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4702step1 raw4702step0; decide +kernel
      have hl : raw4702step1Labels = raw4702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4702step0 raw4702step0Labels permutation56 hz
    mixedMoment B raw4702step1 raw4702step1Labels = mixedMoment B raw4702step2 raw4702step2Labels := by
      have ha : raw4702step2 = (fun i j => raw4702step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4702step2 raw4702step1; decide +kernel
      have hl : raw4702step2Labels = raw4702step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4702step1 raw4702step1Labels permutation8 permutation3
    _ = mixedMoment B node2769 node2769Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment864 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 864) =
      Integer.Sparse.eval keyMomentRow864 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 864).leftCharge (GramAssembly.key 864).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2743) := by
    have ha : gramCharges (GramAssembly.key 864).leftCharge (GramAssembly.key 864).rightCharge = raw40307 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40307Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40307 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 864).leftCharge (GramAssembly.key 864).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow864, Integer.Sparse.eval]

theorem keyMoment865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 865) =
      Integer.Sparse.eval keyMomentRow865 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 865).leftCharge (GramAssembly.key 865).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2744) := by
    have ha : gramCharges (GramAssembly.key 865).leftCharge (GramAssembly.key 865).rightCharge = raw40308 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40308Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40308 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 865).leftCharge (GramAssembly.key 865).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow865, Integer.Sparse.eval]

theorem keyMoment866 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 866) =
      Integer.Sparse.eval keyMomentRow866 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 866).leftCharge (GramAssembly.key 866).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2722) := by
    have ha : gramCharges (GramAssembly.key 866).leftCharge (GramAssembly.key 866).rightCharge = raw40309 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40309Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40309 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 866).leftCharge (GramAssembly.key 866).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow866, Integer.Sparse.eval]

theorem keyMoment867 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 867) =
      Integer.Sparse.eval keyMomentRow867 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 867).leftCharge (GramAssembly.key 867).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2723) := by
    have ha : gramCharges (GramAssembly.key 867).leftCharge (GramAssembly.key 867).rightCharge = raw40310 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40310Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40310 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 867).leftCharge (GramAssembly.key 867).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow867, Integer.Sparse.eval]

theorem keyMoment868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 868) =
      Integer.Sparse.eval keyMomentRow868 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 868).leftCharge (GramAssembly.key 868).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2724) := by
    have ha : gramCharges (GramAssembly.key 868).leftCharge (GramAssembly.key 868).rightCharge = raw40311 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40311Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40311 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 868).leftCharge (GramAssembly.key 868).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow868, Integer.Sparse.eval]

theorem keyMoment869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 869) =
      Integer.Sparse.eval keyMomentRow869 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 869).leftCharge (GramAssembly.key 869).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2731) := by
    have ha : gramCharges (GramAssembly.key 869).leftCharge (GramAssembly.key 869).rightCharge = raw40312 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40312Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40312 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 869).leftCharge (GramAssembly.key 869).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow869, Integer.Sparse.eval]

theorem keyMoment870 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 870) =
      Integer.Sparse.eval keyMomentRow870 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 870).leftCharge (GramAssembly.key 870).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2732) := by
    have ha : gramCharges (GramAssembly.key 870).leftCharge (GramAssembly.key 870).rightCharge = raw40313 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40313Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40313 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 870).leftCharge (GramAssembly.key 870).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow870, Integer.Sparse.eval]

theorem keyMoment871 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 871) =
      Integer.Sparse.eval keyMomentRow871 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 871).leftCharge (GramAssembly.key 871).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2738) := by
    have ha : gramCharges (GramAssembly.key 871).leftCharge (GramAssembly.key 871).rightCharge = raw40314 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40314Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40314 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 871).leftCharge (GramAssembly.key 871).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow871, Integer.Sparse.eval]

theorem keyMoment872 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 872) =
      Integer.Sparse.eval keyMomentRow872 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 872).leftCharge (GramAssembly.key 872).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2739) := by
    have ha : gramCharges (GramAssembly.key 872).leftCharge (GramAssembly.key 872).rightCharge = raw40315 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40315Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40315 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 872).leftCharge (GramAssembly.key 872).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow872, Integer.Sparse.eval]

theorem keyMoment873 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 873) =
      Integer.Sparse.eval keyMomentRow873 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 873).leftCharge (GramAssembly.key 873).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2741) := by
    have ha : gramCharges (GramAssembly.key 873).leftCharge (GramAssembly.key 873).rightCharge = raw40316 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40316Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40316 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 873).leftCharge (GramAssembly.key 873).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow873, Integer.Sparse.eval]

theorem keyMoment874 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 874) =
      Integer.Sparse.eval keyMomentRow874 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 874).leftCharge (GramAssembly.key 874).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2709) := by
    have ha : gramCharges (GramAssembly.key 874).leftCharge (GramAssembly.key 874).rightCharge = raw40317 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40317Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40317 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 874).leftCharge (GramAssembly.key 874).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow874, Integer.Sparse.eval]

theorem keyMoment875 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 875) =
      Integer.Sparse.eval keyMomentRow875 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 875).leftCharge (GramAssembly.key 875).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2710) := by
    have ha : gramCharges (GramAssembly.key 875).leftCharge (GramAssembly.key 875).rightCharge = raw40318 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40318Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40318 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 875).leftCharge (GramAssembly.key 875).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow875, Integer.Sparse.eval]

theorem keyMoment876 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 876) =
      Integer.Sparse.eval keyMomentRow876 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 876).leftCharge (GramAssembly.key 876).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2720) := by
    have ha : gramCharges (GramAssembly.key 876).leftCharge (GramAssembly.key 876).rightCharge = raw40319 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40319Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40319 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 876).leftCharge (GramAssembly.key 876).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow876, Integer.Sparse.eval]

theorem keyMoment877 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 877) =
      Integer.Sparse.eval keyMomentRow877 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 877).leftCharge (GramAssembly.key 877).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2721) := by
    have ha : gramCharges (GramAssembly.key 877).leftCharge (GramAssembly.key 877).rightCharge = raw40320 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40320Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40320 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 877).leftCharge (GramAssembly.key 877).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow877, Integer.Sparse.eval]

theorem keyMoment878 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 878) =
      Integer.Sparse.eval keyMomentRow878 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 878).leftCharge (GramAssembly.key 878).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2730) := by
    have ha : gramCharges (GramAssembly.key 878).leftCharge (GramAssembly.key 878).rightCharge = raw40321 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40321Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40321 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 878).leftCharge (GramAssembly.key 878).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow878, Integer.Sparse.eval]

theorem keyMoment879 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 879) =
      Integer.Sparse.eval keyMomentRow879 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 879).leftCharge (GramAssembly.key 879).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2783) := by
    have ha : gramCharges (GramAssembly.key 879).leftCharge (GramAssembly.key 879).rightCharge = raw40322 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40322Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40322 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 879).leftCharge (GramAssembly.key 879).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow879, Integer.Sparse.eval]

theorem keyMoment880 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 880) =
      Integer.Sparse.eval keyMomentRow880 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 880).leftCharge (GramAssembly.key 880).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2789) := by
    have ha : gramCharges (GramAssembly.key 880).leftCharge (GramAssembly.key 880).rightCharge = raw4485 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw4485Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical4485 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 880).leftCharge (GramAssembly.key 880).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow880, Integer.Sparse.eval]

theorem keyMoment881 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 881) =
      Integer.Sparse.eval keyMomentRow881 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 881).leftCharge (GramAssembly.key 881).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2765) := by
    have ha : gramCharges (GramAssembly.key 881).leftCharge (GramAssembly.key 881).rightCharge = raw40323 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40323Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40323 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 881).leftCharge (GramAssembly.key 881).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow881, Integer.Sparse.eval]

theorem keyMoment882 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 882) =
      Integer.Sparse.eval keyMomentRow882 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 882).leftCharge (GramAssembly.key 882).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2769) := by
    have ha : gramCharges (GramAssembly.key 882).leftCharge (GramAssembly.key 882).rightCharge = raw4702 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw4702Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical4702 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 882).leftCharge (GramAssembly.key 882).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow882, Integer.Sparse.eval]

theorem keyMoment883 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 883) =
      Integer.Sparse.eval keyMomentRow883 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 883).leftCharge (GramAssembly.key 883).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2774) := by
    have ha : gramCharges (GramAssembly.key 883).leftCharge (GramAssembly.key 883).rightCharge = raw40324 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40324Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40324 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 883).leftCharge (GramAssembly.key 883).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow883, Integer.Sparse.eval]

theorem keyMoment884 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 884) =
      Integer.Sparse.eval keyMomentRow884 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 884).leftCharge (GramAssembly.key 884).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2777) := by
    have ha : gramCharges (GramAssembly.key 884).leftCharge (GramAssembly.key 884).rightCharge = raw40325 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40325Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40325 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 884).leftCharge (GramAssembly.key 884).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow884, Integer.Sparse.eval]

theorem keyMoment885 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 885) =
      Integer.Sparse.eval keyMomentRow885 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 885).leftCharge (GramAssembly.key 885).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2781) := by
    have ha : gramCharges (GramAssembly.key 885).leftCharge (GramAssembly.key 885).rightCharge = raw40326 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40326Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40326 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 885).leftCharge (GramAssembly.key 885).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow885, Integer.Sparse.eval]

theorem keyMoment886 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 886) =
      Integer.Sparse.eval keyMomentRow886 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 886).leftCharge (GramAssembly.key 886).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2782) := by
    have ha : gramCharges (GramAssembly.key 886).leftCharge (GramAssembly.key 886).rightCharge = raw40327 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40327Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40327 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 886).leftCharge (GramAssembly.key 886).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow886, Integer.Sparse.eval]

theorem keyMoment887 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 887) =
      Integer.Sparse.eval keyMomentRow887 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 887).leftCharge (GramAssembly.key 887).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2751) := by
    have ha : gramCharges (GramAssembly.key 887).leftCharge (GramAssembly.key 887).rightCharge = raw40328 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40328Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40328 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 887).leftCharge (GramAssembly.key 887).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow887, Integer.Sparse.eval]

theorem keyMoment888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 888) =
      Integer.Sparse.eval keyMomentRow888 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 888).leftCharge (GramAssembly.key 888).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2754) := by
    have ha : gramCharges (GramAssembly.key 888).leftCharge (GramAssembly.key 888).rightCharge = raw40329 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40329Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40329 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 888).leftCharge (GramAssembly.key 888).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow888, Integer.Sparse.eval]

theorem keyMoment889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 889) =
      Integer.Sparse.eval keyMomentRow889 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 889).leftCharge (GramAssembly.key 889).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2763) := by
    have ha : gramCharges (GramAssembly.key 889).leftCharge (GramAssembly.key 889).rightCharge = raw40330 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40330Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40330 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 889).leftCharge (GramAssembly.key 889).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow889, Integer.Sparse.eval]

theorem keyMoment890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 890) =
      Integer.Sparse.eval keyMomentRow890 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 890).leftCharge (GramAssembly.key 890).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2764) := by
    have ha : gramCharges (GramAssembly.key 890).leftCharge (GramAssembly.key 890).rightCharge = raw40331 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40331Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40331 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 890).leftCharge (GramAssembly.key 890).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow890, Integer.Sparse.eval]

theorem keyMoment891 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 891) =
      Integer.Sparse.eval keyMomentRow891 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 891).leftCharge (GramAssembly.key 891).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2773) := by
    have ha : gramCharges (GramAssembly.key 891).leftCharge (GramAssembly.key 891).rightCharge = raw40332 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40332Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40332 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 891).leftCharge (GramAssembly.key 891).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow891, Integer.Sparse.eval]

theorem keyMoment892 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 892) =
      Integer.Sparse.eval keyMomentRow892 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 892).leftCharge (GramAssembly.key 892).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2750) := by
    have ha : gramCharges (GramAssembly.key 892).leftCharge (GramAssembly.key 892).rightCharge = raw40333 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40333Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40333 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 892).leftCharge (GramAssembly.key 892).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow892, Integer.Sparse.eval]

theorem keyMoment893 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 893) =
      Integer.Sparse.eval keyMomentRow893 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 893).leftCharge (GramAssembly.key 893).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2281) := by
    have ha : gramCharges (GramAssembly.key 893).leftCharge (GramAssembly.key 893).rightCharge = raw40334 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40334Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40334 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 893).leftCharge (GramAssembly.key 893).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow893, Integer.Sparse.eval]

theorem keyMoment894 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 894) =
      Integer.Sparse.eval keyMomentRow894 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 894).leftCharge (GramAssembly.key 894).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2734) := by
    have ha : gramCharges (GramAssembly.key 894).leftCharge (GramAssembly.key 894).rightCharge = raw40335 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40335Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40335 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 894).leftCharge (GramAssembly.key 894).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow894, Integer.Sparse.eval]

theorem keyMoment895 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 895) =
      Integer.Sparse.eval keyMomentRow895 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 895).leftCharge (GramAssembly.key 895).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3046) := by
    have ha : gramCharges (GramAssembly.key 895).leftCharge (GramAssembly.key 895).rightCharge = raw40336 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40336Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40336 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 895).leftCharge (GramAssembly.key 895).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow895, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt864 : keyMomentRows (864 : Fin 2886) =
    keyMomentRow864 := by decide +kernel

theorem keyMomentRowsAt865 : keyMomentRows (865 : Fin 2886) =
    keyMomentRow865 := by decide +kernel

theorem keyMomentRowsAt866 : keyMomentRows (866 : Fin 2886) =
    keyMomentRow866 := by decide +kernel

theorem keyMomentRowsAt867 : keyMomentRows (867 : Fin 2886) =
    keyMomentRow867 := by decide +kernel

theorem keyMomentRowsAt868 : keyMomentRows (868 : Fin 2886) =
    keyMomentRow868 := by decide +kernel

theorem keyMomentRowsAt869 : keyMomentRows (869 : Fin 2886) =
    keyMomentRow869 := by decide +kernel

theorem keyMomentRowsAt870 : keyMomentRows (870 : Fin 2886) =
    keyMomentRow870 := by decide +kernel

theorem keyMomentRowsAt871 : keyMomentRows (871 : Fin 2886) =
    keyMomentRow871 := by decide +kernel

theorem keyMomentRowsAt872 : keyMomentRows (872 : Fin 2886) =
    keyMomentRow872 := by decide +kernel

theorem keyMomentRowsAt873 : keyMomentRows (873 : Fin 2886) =
    keyMomentRow873 := by decide +kernel

theorem keyMomentRowsAt874 : keyMomentRows (874 : Fin 2886) =
    keyMomentRow874 := by decide +kernel

theorem keyMomentRowsAt875 : keyMomentRows (875 : Fin 2886) =
    keyMomentRow875 := by decide +kernel

theorem keyMomentRowsAt876 : keyMomentRows (876 : Fin 2886) =
    keyMomentRow876 := by decide +kernel

theorem keyMomentRowsAt877 : keyMomentRows (877 : Fin 2886) =
    keyMomentRow877 := by decide +kernel

theorem keyMomentRowsAt878 : keyMomentRows (878 : Fin 2886) =
    keyMomentRow878 := by decide +kernel

theorem keyMomentRowsAt879 : keyMomentRows (879 : Fin 2886) =
    keyMomentRow879 := by decide +kernel

theorem keyMomentRowsAt880 : keyMomentRows (880 : Fin 2886) =
    keyMomentRow880 := by decide +kernel

theorem keyMomentRowsAt881 : keyMomentRows (881 : Fin 2886) =
    keyMomentRow881 := by decide +kernel

theorem keyMomentRowsAt882 : keyMomentRows (882 : Fin 2886) =
    keyMomentRow882 := by decide +kernel

theorem keyMomentRowsAt883 : keyMomentRows (883 : Fin 2886) =
    keyMomentRow883 := by decide +kernel

theorem keyMomentRowsAt884 : keyMomentRows (884 : Fin 2886) =
    keyMomentRow884 := by decide +kernel

theorem keyMomentRowsAt885 : keyMomentRows (885 : Fin 2886) =
    keyMomentRow885 := by decide +kernel

theorem keyMomentRowsAt886 : keyMomentRows (886 : Fin 2886) =
    keyMomentRow886 := by decide +kernel

theorem keyMomentRowsAt887 : keyMomentRows (887 : Fin 2886) =
    keyMomentRow887 := by decide +kernel

theorem keyMomentRowsAt888 : keyMomentRows (888 : Fin 2886) =
    keyMomentRow888 := by decide +kernel

theorem keyMomentRowsAt889 : keyMomentRows (889 : Fin 2886) =
    keyMomentRow889 := by decide +kernel

theorem keyMomentRowsAt890 : keyMomentRows (890 : Fin 2886) =
    keyMomentRow890 := by decide +kernel

theorem keyMomentRowsAt891 : keyMomentRows (891 : Fin 2886) =
    keyMomentRow891 := by decide +kernel

theorem keyMomentRowsAt892 : keyMomentRows (892 : Fin 2886) =
    keyMomentRow892 := by decide +kernel

theorem keyMomentRowsAt893 : keyMomentRows (893 : Fin 2886) =
    keyMomentRow893 := by decide +kernel

theorem keyMomentRowsAt894 : keyMomentRows (894 : Fin 2886) =
    keyMomentRow894 := by decide +kernel

theorem keyMomentRowsAt895 : keyMomentRows (895 : Fin 2886) =
    keyMomentRow895 := by decide +kernel

theorem keyMomentChunkSound27_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 27) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 864 ∨ k.val = 865 ∨ k.val = 866 ∨ k.val = 867 ∨ k.val = 868 ∨ k.val = 869 ∨ k.val = 870 ∨ k.val = 871 ∨ k.val = 872 ∨ k.val = 873 ∨ k.val = 874 ∨ k.val = 875 ∨ k.val = 876 ∨ k.val = 877 ∨ k.val = 878 ∨ k.val = 879 ∨ k.val = 880 ∨ k.val = 881 ∨ k.val = 882 ∨ k.val = 883 ∨ k.val = 884 ∨ k.val = 885 ∨ k.val = 886 ∨ k.val = 887 ∨ k.val = 888 ∨ k.val = 889 ∨ k.val = 890 ∨ k.val = 891 ∨ k.val = 892 ∨ k.val = 893 ∨ k.val = 894 ∨ k.val = 895 := by omega
  rcases heq with h864 | h865 | h866 | h867 | h868 | h869 | h870 | h871 | h872 | h873 | h874 | h875 | h876 | h877 | h878 | h879 | h880 | h881 | h882 | h883 | h884 | h885 | h886 | h887 | h888 | h889 | h890 | h891 | h892 | h893 | h894 | h895
  · have he : k = (864 : Fin 2886) := Fin.ext h864
    subst k
    rw [keyMomentRowsAt864]
    exact keyMoment864 B hB
  · have he : k = (865 : Fin 2886) := Fin.ext h865
    subst k
    rw [keyMomentRowsAt865]
    exact keyMoment865 B hB
  · have he : k = (866 : Fin 2886) := Fin.ext h866
    subst k
    rw [keyMomentRowsAt866]
    exact keyMoment866 B hB
  · have he : k = (867 : Fin 2886) := Fin.ext h867
    subst k
    rw [keyMomentRowsAt867]
    exact keyMoment867 B hB
  · have he : k = (868 : Fin 2886) := Fin.ext h868
    subst k
    rw [keyMomentRowsAt868]
    exact keyMoment868 B hB
  · have he : k = (869 : Fin 2886) := Fin.ext h869
    subst k
    rw [keyMomentRowsAt869]
    exact keyMoment869 B hB
  · have he : k = (870 : Fin 2886) := Fin.ext h870
    subst k
    rw [keyMomentRowsAt870]
    exact keyMoment870 B hB
  · have he : k = (871 : Fin 2886) := Fin.ext h871
    subst k
    rw [keyMomentRowsAt871]
    exact keyMoment871 B hB
  · have he : k = (872 : Fin 2886) := Fin.ext h872
    subst k
    rw [keyMomentRowsAt872]
    exact keyMoment872 B hB
  · have he : k = (873 : Fin 2886) := Fin.ext h873
    subst k
    rw [keyMomentRowsAt873]
    exact keyMoment873 B hB
  · have he : k = (874 : Fin 2886) := Fin.ext h874
    subst k
    rw [keyMomentRowsAt874]
    exact keyMoment874 B hB
  · have he : k = (875 : Fin 2886) := Fin.ext h875
    subst k
    rw [keyMomentRowsAt875]
    exact keyMoment875 B hB
  · have he : k = (876 : Fin 2886) := Fin.ext h876
    subst k
    rw [keyMomentRowsAt876]
    exact keyMoment876 B hB
  · have he : k = (877 : Fin 2886) := Fin.ext h877
    subst k
    rw [keyMomentRowsAt877]
    exact keyMoment877 B hB
  · have he : k = (878 : Fin 2886) := Fin.ext h878
    subst k
    rw [keyMomentRowsAt878]
    exact keyMoment878 B hB
  · have he : k = (879 : Fin 2886) := Fin.ext h879
    subst k
    rw [keyMomentRowsAt879]
    exact keyMoment879 B hB
  · have he : k = (880 : Fin 2886) := Fin.ext h880
    subst k
    rw [keyMomentRowsAt880]
    exact keyMoment880 B hB
  · have he : k = (881 : Fin 2886) := Fin.ext h881
    subst k
    rw [keyMomentRowsAt881]
    exact keyMoment881 B hB
  · have he : k = (882 : Fin 2886) := Fin.ext h882
    subst k
    rw [keyMomentRowsAt882]
    exact keyMoment882 B hB
  · have he : k = (883 : Fin 2886) := Fin.ext h883
    subst k
    rw [keyMomentRowsAt883]
    exact keyMoment883 B hB
  · have he : k = (884 : Fin 2886) := Fin.ext h884
    subst k
    rw [keyMomentRowsAt884]
    exact keyMoment884 B hB
  · have he : k = (885 : Fin 2886) := Fin.ext h885
    subst k
    rw [keyMomentRowsAt885]
    exact keyMoment885 B hB
  · have he : k = (886 : Fin 2886) := Fin.ext h886
    subst k
    rw [keyMomentRowsAt886]
    exact keyMoment886 B hB
  · have he : k = (887 : Fin 2886) := Fin.ext h887
    subst k
    rw [keyMomentRowsAt887]
    exact keyMoment887 B hB
  · have he : k = (888 : Fin 2886) := Fin.ext h888
    subst k
    rw [keyMomentRowsAt888]
    exact keyMoment888 B hB
  · have he : k = (889 : Fin 2886) := Fin.ext h889
    subst k
    rw [keyMomentRowsAt889]
    exact keyMoment889 B hB
  · have he : k = (890 : Fin 2886) := Fin.ext h890
    subst k
    rw [keyMomentRowsAt890]
    exact keyMoment890 B hB
  · have he : k = (891 : Fin 2886) := Fin.ext h891
    subst k
    rw [keyMomentRowsAt891]
    exact keyMoment891 B hB
  · have he : k = (892 : Fin 2886) := Fin.ext h892
    subst k
    rw [keyMomentRowsAt892]
    exact keyMoment892 B hB
  · have he : k = (893 : Fin 2886) := Fin.ext h893
    subst k
    rw [keyMomentRowsAt893]
    exact keyMoment893 B hB
  · have he : k = (894 : Fin 2886) := Fin.ext h894
    subst k
    rw [keyMomentRowsAt894]
    exact keyMoment894 B hB
  · have he : k = (895 : Fin 2886) := Fin.ext h895
    subst k
    rw [keyMomentRowsAt895]
    exact keyMoment895 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound27_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound27_e_oai
