-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound37_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:54:05.607405+00:00
-- url     : https://prove2.me/submissions/186cf3a3-a452-46c0-874b-660c3c9b1401

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E108
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical150
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19298 raw19298Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw19298 raw19298Labels = mixedMoment B raw19298step0 raw19298step0Labels := by
      have hz : ∀ j, raw19298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19298step0 = (fun i j => raw19298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19298step0 raw19298; decide +kernel
      have hl : raw19298step0Labels = raw19298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19298 raw19298Labels permutation434 hz
    mixedMoment B raw19298step0 raw19298step0Labels = mixedMoment B raw19298step1 raw19298step1Labels := by
      have ha : raw19298step1 = (fun i j => raw19298step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19298step1 raw19298step0; decide +kernel
      have hl : raw19298step1Labels = raw19298step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19298step0 raw19298step0Labels permutation32 permutation3
    _ = mixedMoment B node3876 node3876Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical273
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34967 raw34967Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw34967 raw34967Labels = mixedMoment B raw34967step0 raw34967step0Labels := by
      have hz : ∀ j, raw34967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34967step0 = (fun i j => raw34967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34967step0 raw34967; decide +kernel
      have hl : raw34967step0Labels = raw34967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34967 raw34967Labels permutation346 hz
    mixedMoment B raw34967step0 raw34967step0Labels = mixedMoment B raw34967step1 raw34967step1Labels := by
      have ha : raw34967step1 = (fun i j => raw34967step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34967step1 raw34967step0; decide +kernel
      have hl : raw34967step1Labels = raw34967step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34967step0 raw34967step0Labels permutation32 permutation3
    _ = mixedMoment B node3881 node3881Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical274
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35153 raw35153Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw35153 raw35153Labels = mixedMoment B raw35153step0 raw35153step0Labels := by
      have hz : ∀ j, raw35153 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35153step0 = (fun i j => raw35153 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35153step0 raw35153; decide +kernel
      have hl : raw35153step0Labels = raw35153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35153 raw35153Labels permutation434 hz
    mixedMoment B raw35153step0 raw35153step0Labels = mixedMoment B raw35153step1 raw35153step1Labels := by
      have hz : ∀ j, raw35153step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35153step1 = (fun i j => raw35153step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35153step1 raw35153step0; decide +kernel
      have hl : raw35153step1Labels = raw35153step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35153step0 raw35153step0Labels permutation80 hz
    mixedMoment B raw35153step1 raw35153step1Labels = mixedMoment B raw35153step2 raw35153step2Labels := by
      have ha : raw35153step2 = (fun i j => raw35153step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35153step2 raw35153step1; decide +kernel
      have hl : raw35153step2Labels = raw35153step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35153step1 raw35153step1Labels permutation15 permutation6
    mixedMoment B raw35153step2 raw35153step2Labels = mixedMoment B raw35153step3 raw35153step3Labels := by
      have ha : raw35153step3 = -raw35153step2 := by apply Matrix.ext; change ∀ i j, raw35153step3 i j = -(raw35153step2 i j); unfold raw35153step3 raw35153step2; decide +kernel
      have hl : raw35153step3Labels = raw35153step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2774 node2774Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical317
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40619 raw40619Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw40619 raw40619Labels = mixedMoment B raw40619step0 raw40619step0Labels := by
      have ha : raw40619step0 = (fun i j => raw40619 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40619step0 raw40619; decide +kernel
      have hl : raw40619step0Labels = raw40619Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40619 raw40619Labels permutation152 permutation3
    _ = mixedMoment B node3846 node3846Labels := by rfl

theorem canonical40620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40620 raw40620Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw40620 raw40620Labels = mixedMoment B raw40620step0 raw40620step0Labels := by
      have ha : raw40620step0 = (fun i j => raw40620 (permutation599 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40620step0 raw40620; decide +kernel
      have hl : raw40620step0Labels = raw40620Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40620 raw40620Labels permutation599 permutation6
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical40621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40621 raw40621Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw40621 raw40621Labels = mixedMoment B raw40621step0 raw40621step0Labels := by
      have ha : raw40621step0 = (fun i j => raw40621 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40621step0 raw40621; decide +kernel
      have hl : raw40621step0Labels = raw40621Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40621 raw40621Labels permutation152 permutation3
    _ = mixedMoment B node3848 node3848Labels := by rfl

theorem canonical40622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40622 raw40622Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw40622 raw40622Labels = mixedMoment B raw40622step0 raw40622step0Labels := by
      have ha : raw40622step0 = (fun i j => raw40622 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40622step0 raw40622; decide +kernel
      have hl : raw40622step0Labels = raw40622Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40622 raw40622Labels permutation152 permutation3
    _ = mixedMoment B node3849 node3849Labels := by rfl

theorem canonical40623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40623 raw40623Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw40623 raw40623Labels = mixedMoment B raw40623step0 raw40623step0Labels := by
      have ha : raw40623step0 = (fun i j => raw40623 (permutation380 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40623step0 raw40623; decide +kernel
      have hl : raw40623step0Labels = raw40623Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40623 raw40623Labels permutation380 permutation6
    mixedMoment B raw40623step0 raw40623step0Labels = mixedMoment B raw40623step1 raw40623step1Labels := by
      have ha : raw40623step1 = -raw40623step0 := by apply Matrix.ext; change ∀ i j, raw40623step1 i j = -(raw40623step0 i j); unfold raw40623step1 raw40623step0; decide +kernel
      have hl : raw40623step1Labels = raw40623step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical40624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40624 raw40624Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw40624 raw40624Labels = mixedMoment B raw40624step0 raw40624step0Labels := by
      have hz : ∀ j, raw40624 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40624step0 = (fun i j => raw40624 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40624step0 raw40624; decide +kernel
      have hl : raw40624step0Labels = raw40624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40624 raw40624Labels permutation520 hz
    mixedMoment B raw40624step0 raw40624step0Labels = mixedMoment B raw40624step1 raw40624step1Labels := by
      have hz : ∀ j, raw40624step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40624step1 = (fun i j => raw40624step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40624step1 raw40624step0; decide +kernel
      have hl : raw40624step1Labels = raw40624step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40624step0 raw40624step0Labels permutation104 hz
    mixedMoment B raw40624step1 raw40624step1Labels = mixedMoment B raw40624step2 raw40624step2Labels := by
      have ha : raw40624step2 = (fun i j => raw40624step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40624step2 raw40624step1; decide +kernel
      have hl : raw40624step2Labels = raw40624step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40624step1 raw40624step1Labels permutation31 permutation3
    mixedMoment B raw40624step2 raw40624step2Labels = mixedMoment B raw40624step3 raw40624step3Labels := by
      have ha : raw40624step3 = -raw40624step2 := by apply Matrix.ext; change ∀ i j, raw40624step3 i j = -(raw40624step2 i j); unfold raw40624step3 raw40624step2; decide +kernel
      have hl : raw40624step3Labels = raw40624step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical40625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40625 raw40625Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw40625 raw40625Labels = mixedMoment B raw40625step0 raw40625step0Labels := by
      have hz : ∀ j, raw40625 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40625step0 = (fun i j => raw40625 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40625step0 raw40625; decide +kernel
      have hl : raw40625step0Labels = raw40625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40625 raw40625Labels permutation434 hz
    mixedMoment B raw40625step0 raw40625step0Labels = mixedMoment B raw40625step1 raw40625step1Labels := by
      have ha : raw40625step1 = (fun i j => raw40625step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40625step1 raw40625step0; decide +kernel
      have hl : raw40625step1Labels = raw40625step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40625step0 raw40625step0Labels permutation151 permutation3
    mixedMoment B raw40625step1 raw40625step1Labels = mixedMoment B raw40625step2 raw40625step2Labels := by
      have ha : raw40625step2 = -raw40625step1 := by apply Matrix.ext; change ∀ i j, raw40625step2 i j = -(raw40625step1 i j); unfold raw40625step2 raw40625step1; decide +kernel
      have hl : raw40625step2Labels = raw40625step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3086 node3086Labels := by rfl

theorem canonical40626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40626 raw40626Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw40626 raw40626Labels = mixedMoment B raw40626step0 raw40626step0Labels := by
      have hz : ∀ j, raw40626 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40626step0 = (fun i j => raw40626 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40626step0 raw40626; decide +kernel
      have hl : raw40626step0Labels = raw40626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40626 raw40626Labels permutation434 hz
    mixedMoment B raw40626step0 raw40626step0Labels = mixedMoment B raw40626step1 raw40626step1Labels := by
      have ha : raw40626step1 = (fun i j => raw40626step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40626step1 raw40626step0; decide +kernel
      have hl : raw40626step1Labels = raw40626step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40626step0 raw40626step0Labels permutation151 permutation3
    mixedMoment B raw40626step1 raw40626step1Labels = mixedMoment B raw40626step2 raw40626step2Labels := by
      have ha : raw40626step2 = -raw40626step1 := by apply Matrix.ext; change ∀ i j, raw40626step2 i j = -(raw40626step1 i j); unfold raw40626step2 raw40626step1; decide +kernel
      have hl : raw40626step2Labels = raw40626step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical40627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40627 raw40627Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw40627 raw40627Labels = mixedMoment B raw40627step0 raw40627step0Labels := by
      have hz : ∀ j, raw40627 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40627step0 = (fun i j => raw40627 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40627step0 raw40627; decide +kernel
      have hl : raw40627step0Labels = raw40627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40627 raw40627Labels permutation434 hz
    mixedMoment B raw40627step0 raw40627step0Labels = mixedMoment B raw40627step1 raw40627step1Labels := by
      have ha : raw40627step1 = (fun i j => raw40627step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40627step1 raw40627step0; decide +kernel
      have hl : raw40627step1Labels = raw40627step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40627step0 raw40627step0Labels permutation32 permutation3
    _ = mixedMoment B node3877 node3877Labels := by rfl

theorem canonical40628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40628 raw40628Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw40628 raw40628Labels = mixedMoment B raw40628step0 raw40628step0Labels := by
      have ha : raw40628step0 = (fun i j => raw40628 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40628step0 raw40628; decide +kernel
      have hl : raw40628step0Labels = raw40628Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40628 raw40628Labels permutation152 permutation3
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical40629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40629 raw40629Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw40629 raw40629Labels = mixedMoment B raw40629step0 raw40629step0Labels := by
      have ha : raw40629step0 = (fun i j => raw40629 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40629step0 raw40629; decide +kernel
      have hl : raw40629step0Labels = raw40629Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40629 raw40629Labels permutation152 permutation3
    _ = mixedMoment B node3872 node3872Labels := by rfl

theorem canonical40630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40630 raw40630Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw40630 raw40630Labels = mixedMoment B raw40630step0 raw40630step0Labels := by
      have ha : raw40630step0 = (fun i j => raw40630 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40630step0 raw40630; decide +kernel
      have hl : raw40630step0Labels = raw40630Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40630 raw40630Labels permutation152 permutation3
    _ = mixedMoment B node3874 node3874Labels := by rfl

theorem canonical40631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40631 raw40631Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw40631 raw40631Labels = mixedMoment B raw40631step0 raw40631step0Labels := by
      have ha : raw40631step0 = (fun i j => raw40631 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40631step0 raw40631; decide +kernel
      have hl : raw40631step0Labels = raw40631Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40631 raw40631Labels permutation152 permutation3
    _ = mixedMoment B node3875 node3875Labels := by rfl

theorem canonical40632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40632 raw40632Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw40632 raw40632Labels = mixedMoment B raw40632step0 raw40632step0Labels := by
      have hz : ∀ j, raw40632 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40632step0 = (fun i j => raw40632 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40632step0 raw40632; decide +kernel
      have hl : raw40632step0Labels = raw40632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40632 raw40632Labels permutation434 hz
    mixedMoment B raw40632step0 raw40632step0Labels = mixedMoment B raw40632step1 raw40632step1Labels := by
      have hz : ∀ j, raw40632step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40632step1 = (fun i j => raw40632step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40632step1 raw40632step0; decide +kernel
      have hl : raw40632step1Labels = raw40632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40632step0 raw40632step0Labels permutation80 hz
    mixedMoment B raw40632step1 raw40632step1Labels = mixedMoment B raw40632step2 raw40632step2Labels := by
      have ha : raw40632step2 = (fun i j => raw40632step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40632step2 raw40632step1; decide +kernel
      have hl : raw40632step2Labels = raw40632step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40632step1 raw40632step1Labels permutation8 permutation3
    _ = mixedMoment B node3886 node3886Labels := by rfl

theorem canonical40633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40633 raw40633Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw40633 raw40633Labels = mixedMoment B raw40633step0 raw40633step0Labels := by
      have hz : ∀ j, raw40633 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40633step0 = (fun i j => raw40633 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40633step0 raw40633; decide +kernel
      have hl : raw40633step0Labels = raw40633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40633 raw40633Labels permutation434 hz
    mixedMoment B raw40633step0 raw40633step0Labels = mixedMoment B raw40633step1 raw40633step1Labels := by
      have hz : ∀ j, raw40633step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40633step1 = (fun i j => raw40633step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40633step1 raw40633step0; decide +kernel
      have hl : raw40633step1Labels = raw40633step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40633step0 raw40633step0Labels permutation80 hz
    mixedMoment B raw40633step1 raw40633step1Labels = mixedMoment B raw40633step2 raw40633step2Labels := by
      have ha : raw40633step2 = (fun i j => raw40633step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40633step2 raw40633step1; decide +kernel
      have hl : raw40633step2Labels = raw40633step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40633step1 raw40633step1Labels permutation27 permutation6
    _ = mixedMoment B node3055 node3055Labels := by rfl

theorem canonical40634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40634 raw40634Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw40634 raw40634Labels = mixedMoment B raw40634step0 raw40634step0Labels := by
      have hz : ∀ j, raw40634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40634step0 = (fun i j => raw40634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40634step0 raw40634; decide +kernel
      have hl : raw40634step0Labels = raw40634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40634 raw40634Labels permutation346 hz
    mixedMoment B raw40634step0 raw40634step0Labels = mixedMoment B raw40634step1 raw40634step1Labels := by
      have ha : raw40634step1 = (fun i j => raw40634step0 (permutation133 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40634step1 raw40634step0; decide +kernel
      have hl : raw40634step1Labels = raw40634step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40634step0 raw40634step0Labels permutation133 permutation6
    _ = mixedMoment B node3039 node3039Labels := by rfl

theorem canonical40635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40635 raw40635Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw40635 raw40635Labels = mixedMoment B raw40635step0 raw40635step0Labels := by
      have hz : ∀ j, raw40635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40635step0 = (fun i j => raw40635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40635step0 raw40635; decide +kernel
      have hl : raw40635step0Labels = raw40635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40635 raw40635Labels permutation346 hz
    mixedMoment B raw40635step0 raw40635step0Labels = mixedMoment B raw40635step1 raw40635step1Labels := by
      have ha : raw40635step1 = (fun i j => raw40635step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40635step1 raw40635step0; decide +kernel
      have hl : raw40635step1Labels = raw40635step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40635step0 raw40635step0Labels permutation32 permutation3
    _ = mixedMoment B node3884 node3884Labels := by rfl

theorem canonical40636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40636 raw40636Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw40636 raw40636Labels = mixedMoment B raw40636step0 raw40636step0Labels := by
      have hz : ∀ j, raw40636 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40636step0 = (fun i j => raw40636 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40636step0 raw40636; decide +kernel
      have hl : raw40636step0Labels = raw40636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40636 raw40636Labels permutation346 hz
    mixedMoment B raw40636step0 raw40636step0Labels = mixedMoment B raw40636step1 raw40636step1Labels := by
      have ha : raw40636step1 = (fun i j => raw40636step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40636step1 raw40636step0; decide +kernel
      have hl : raw40636step1Labels = raw40636step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40636step0 raw40636step0Labels permutation32 permutation3
    _ = mixedMoment B node3885 node3885Labels := by rfl

theorem canonical40637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40637 raw40637Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw40637 raw40637Labels = mixedMoment B raw40637step0 raw40637step0Labels := by
      have hz : ∀ j, raw40637 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40637step0 = (fun i j => raw40637 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40637step0 raw40637; decide +kernel
      have hl : raw40637step0Labels = raw40637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40637 raw40637Labels permutation520 hz
    mixedMoment B raw40637step0 raw40637step0Labels = mixedMoment B raw40637step1 raw40637step1Labels := by
      have hz : ∀ j, raw40637step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40637step1 = (fun i j => raw40637step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40637step1 raw40637step0; decide +kernel
      have hl : raw40637step1Labels = raw40637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40637step0 raw40637step0Labels permutation104 hz
    mixedMoment B raw40637step1 raw40637step1Labels = mixedMoment B raw40637step2 raw40637step2Labels := by
      have ha : raw40637step2 = (fun i j => raw40637step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40637step2 raw40637step1; decide +kernel
      have hl : raw40637step2Labels = raw40637step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40637step1 raw40637step1Labels permutation14 permutation6
    mixedMoment B raw40637step2 raw40637step2Labels = mixedMoment B raw40637step3 raw40637step3Labels := by
      have ha : raw40637step3 = -raw40637step2 := by apply Matrix.ext; change ∀ i j, raw40637step3 i j = -(raw40637step2 i j); unfold raw40637step3 raw40637step2; decide +kernel
      have hl : raw40637step3Labels = raw40637step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2777 node2777Labels := by rfl

theorem canonical40638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40638 raw40638Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw40638 raw40638Labels = mixedMoment B raw40638step0 raw40638step0Labels := by
      have hz : ∀ j, raw40638 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40638step0 = (fun i j => raw40638 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40638step0 raw40638; decide +kernel
      have hl : raw40638step0Labels = raw40638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40638 raw40638Labels permutation434 hz
    mixedMoment B raw40638step0 raw40638step0Labels = mixedMoment B raw40638step1 raw40638step1Labels := by
      have ha : raw40638step1 = (fun i j => raw40638step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40638step1 raw40638step0; decide +kernel
      have hl : raw40638step1Labels = raw40638step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40638step0 raw40638step0Labels permutation61 permutation6
    mixedMoment B raw40638step1 raw40638step1Labels = mixedMoment B raw40638step2 raw40638step2Labels := by
      have ha : raw40638step2 = -raw40638step1 := by apply Matrix.ext; change ∀ i j, raw40638step2 i j = -(raw40638step1 i j); unfold raw40638step2 raw40638step1; decide +kernel
      have hl : raw40638step2Labels = raw40638step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical40639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40639 raw40639Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw40639 raw40639Labels = mixedMoment B raw40639step0 raw40639step0Labels := by
      have hz : ∀ j, raw40639 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40639step0 = (fun i j => raw40639 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40639step0 raw40639; decide +kernel
      have hl : raw40639step0Labels = raw40639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40639 raw40639Labels permutation434 hz
    mixedMoment B raw40639step0 raw40639step0Labels = mixedMoment B raw40639step1 raw40639step1Labels := by
      have ha : raw40639step1 = (fun i j => raw40639step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40639step1 raw40639step0; decide +kernel
      have hl : raw40639step1Labels = raw40639step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40639step0 raw40639step0Labels permutation68 permutation6
    mixedMoment B raw40639step1 raw40639step1Labels = mixedMoment B raw40639step2 raw40639step2Labels := by
      have ha : raw40639step2 = -raw40639step1 := by apply Matrix.ext; change ∀ i j, raw40639step2 i j = -(raw40639step1 i j); unfold raw40639step2 raw40639step1; decide +kernel
      have hl : raw40639step2Labels = raw40639step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2732 node2732Labels := by rfl

theorem canonical40640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40640 raw40640Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw40640 raw40640Labels = mixedMoment B raw40640step0 raw40640step0Labels := by
      have ha : raw40640step0 = (fun i j => raw40640 (permutation336 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40640step0 raw40640; decide +kernel
      have hl : raw40640step0Labels = raw40640Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40640 raw40640Labels permutation336 permutation6
    mixedMoment B raw40640step0 raw40640step0Labels = mixedMoment B raw40640step1 raw40640step1Labels := by
      have ha : raw40640step1 = -raw40640step0 := by apply Matrix.ext; change ∀ i j, raw40640step1 i j = -(raw40640step0 i j); unfold raw40640step1 raw40640step0; decide +kernel
      have hl : raw40640step1Labels = raw40640step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2730 node2730Labels := by rfl

theorem canonical40641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40641 raw40641Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw40641 raw40641Labels = mixedMoment B raw40641step0 raw40641step0Labels := by
      have hz : ∀ j, raw40641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40641step0 = (fun i j => raw40641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40641step0 raw40641; decide +kernel
      have hl : raw40641step0Labels = raw40641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40641 raw40641Labels permutation434 hz
    mixedMoment B raw40641step0 raw40641step0Labels = mixedMoment B raw40641step1 raw40641step1Labels := by
      have hz : ∀ j, raw40641step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40641step1 = (fun i j => raw40641step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40641step1 raw40641step0; decide +kernel
      have hl : raw40641step1Labels = raw40641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40641step0 raw40641step0Labels permutation80 hz
    mixedMoment B raw40641step1 raw40641step1Labels = mixedMoment B raw40641step2 raw40641step2Labels := by
      have ha : raw40641step2 = (fun i j => raw40641step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40641step2 raw40641step1; decide +kernel
      have hl : raw40641step2Labels = raw40641step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40641step1 raw40641step1Labels permutation16 permutation6
    mixedMoment B raw40641step2 raw40641step2Labels = mixedMoment B raw40641step3 raw40641step3Labels := by
      have ha : raw40641step3 = -raw40641step2 := by apply Matrix.ext; change ∀ i j, raw40641step3 i j = -(raw40641step2 i j); unfold raw40641step3 raw40641step2; decide +kernel
      have hl : raw40641step3Labels = raw40641step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2734 node2734Labels := by rfl

theorem canonical40642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40642 raw40642Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw40642 raw40642Labels = mixedMoment B raw40642step0 raw40642step0Labels := by
      have hz : ∀ j, raw40642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40642step0 = (fun i j => raw40642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40642step0 raw40642; decide +kernel
      have hl : raw40642step0Labels = raw40642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40642 raw40642Labels permutation346 hz
    mixedMoment B raw40642step0 raw40642step0Labels = mixedMoment B raw40642step1 raw40642step1Labels := by
      have ha : raw40642step1 = (fun i j => raw40642step0 (permutation75 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40642step1 raw40642step0; decide +kernel
      have hl : raw40642step1Labels = raw40642step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40642step0 raw40642step0Labels permutation75 permutation6
    mixedMoment B raw40642step1 raw40642step1Labels = mixedMoment B raw40642step2 raw40642step2Labels := by
      have ha : raw40642step2 = -raw40642step1 := by apply Matrix.ext; change ∀ i j, raw40642step2 i j = -(raw40642step1 i j); unfold raw40642step2 raw40642step1; decide +kernel
      have hl : raw40642step2Labels = raw40642step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2731 node2731Labels := by rfl

theorem canonical40643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40643 raw40643Labels = mixedMoment B node3629 node3629Labels := by
  calc
    mixedMoment B raw40643 raw40643Labels = mixedMoment B raw40643step0 raw40643step0Labels := by
      have hz : ∀ j, raw40643 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40643step0 = (fun i j => raw40643 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40643step0 raw40643; decide +kernel
      have hl : raw40643step0Labels = raw40643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40643 raw40643Labels permutation520 hz
    mixedMoment B raw40643step0 raw40643step0Labels = mixedMoment B raw40643step1 raw40643step1Labels := by
      have hz : ∀ j, raw40643step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40643step1 = (fun i j => raw40643step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40643step1 raw40643step0; decide +kernel
      have hl : raw40643step1Labels = raw40643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40643step0 raw40643step0Labels permutation104 hz
    mixedMoment B raw40643step1 raw40643step1Labels = mixedMoment B raw40643step2 raw40643step2Labels := by
      have hz : ∀ j, raw40643step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40643step2 = (fun i j => raw40643step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40643step2 raw40643step1; decide +kernel
      have hl : raw40643step2Labels = raw40643step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40643step1 raw40643step1Labels permutation20 hz
    mixedMoment B raw40643step2 raw40643step2Labels = mixedMoment B raw40643step3 raw40643step3Labels := by
      have ha : raw40643step3 = (fun i j => raw40643step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40643step3 raw40643step2; decide +kernel
      have hl : raw40643step3Labels = raw40643step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40643step2 raw40643step2Labels permutation7 permutation3
    mixedMoment B raw40643step3 raw40643step3Labels = mixedMoment B raw40643step4 raw40643step4Labels := by
      have ha : raw40643step4 = -raw40643step3 := by apply Matrix.ext; change ∀ i j, raw40643step4 i j = -(raw40643step3 i j); unfold raw40643step4 raw40643step3; decide +kernel
      have hl : raw40643step4Labels = raw40643step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3629 node3629Labels := by rfl

theorem canonical40644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40644 raw40644Labels = mixedMoment B node3905 node3905Labels := by
  calc
    mixedMoment B raw40644 raw40644Labels = mixedMoment B raw40644step0 raw40644step0Labels := by
      have hz : ∀ j, raw40644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40644step0 = (fun i j => raw40644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40644step0 raw40644; decide +kernel
      have hl : raw40644step0Labels = raw40644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40644 raw40644Labels permutation434 hz
    mixedMoment B raw40644step0 raw40644step0Labels = mixedMoment B raw40644step1 raw40644step1Labels := by
      have hz : ∀ j, raw40644step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40644step1 = (fun i j => raw40644step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40644step1 raw40644step0; decide +kernel
      have hl : raw40644step1Labels = raw40644step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40644step0 raw40644step0Labels permutation80 hz
    mixedMoment B raw40644step1 raw40644step1Labels = mixedMoment B raw40644step2 raw40644step2Labels := by
      have ha : raw40644step2 = (fun i j => raw40644step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40644step2 raw40644step1; decide +kernel
      have hl : raw40644step2Labels = raw40644step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40644step1 raw40644step1Labels permutation8 permutation3
    _ = mixedMoment B node3905 node3905Labels := by rfl

theorem canonical40645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40645 raw40645Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw40645 raw40645Labels = mixedMoment B raw40645step0 raw40645step0Labels := by
      have hz : ∀ j, raw40645 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40645step0 = (fun i j => raw40645 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40645step0 raw40645; decide +kernel
      have hl : raw40645step0Labels = raw40645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40645 raw40645Labels permutation434 hz
    mixedMoment B raw40645step0 raw40645step0Labels = mixedMoment B raw40645step1 raw40645step1Labels := by
      have hz : ∀ j, raw40645step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40645step1 = (fun i j => raw40645step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40645step1 raw40645step0; decide +kernel
      have hl : raw40645step1Labels = raw40645step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40645step0 raw40645step0Labels permutation80 hz
    mixedMoment B raw40645step1 raw40645step1Labels = mixedMoment B raw40645step2 raw40645step2Labels := by
      have ha : raw40645step2 = (fun i j => raw40645step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40645step2 raw40645step1; decide +kernel
      have hl : raw40645step2Labels = raw40645step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40645step1 raw40645step1Labels permutation8 permutation3
    _ = mixedMoment B node3907 node3907Labels := by rfl

theorem canonical40646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40646 raw40646Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw40646 raw40646Labels = mixedMoment B raw40646step0 raw40646step0Labels := by
      have hz : ∀ j, raw40646 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40646step0 = (fun i j => raw40646 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40646step0 raw40646; decide +kernel
      have hl : raw40646step0Labels = raw40646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40646 raw40646Labels permutation434 hz
    mixedMoment B raw40646step0 raw40646step0Labels = mixedMoment B raw40646step1 raw40646step1Labels := by
      have hz : ∀ j, raw40646step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40646step1 = (fun i j => raw40646step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40646step1 raw40646step0; decide +kernel
      have hl : raw40646step1Labels = raw40646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40646step0 raw40646step0Labels permutation80 hz
    mixedMoment B raw40646step1 raw40646step1Labels = mixedMoment B raw40646step2 raw40646step2Labels := by
      have ha : raw40646step2 = (fun i j => raw40646step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40646step2 raw40646step1; decide +kernel
      have hl : raw40646step2Labels = raw40646step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40646step1 raw40646step1Labels permutation20 permutation6
    mixedMoment B raw40646step2 raw40646step2Labels = mixedMoment B raw40646step3 raw40646step3Labels := by
      have ha : raw40646step3 = -raw40646step2 := by apply Matrix.ext; change ∀ i j, raw40646step3 i j = -(raw40646step2 i j); unfold raw40646step3 raw40646step2; decide +kernel
      have hl : raw40646step3Labels = raw40646step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical40647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40647 raw40647Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw40647 raw40647Labels = mixedMoment B raw40647step0 raw40647step0Labels := by
      have hz : ∀ j, raw40647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40647step0 = (fun i j => raw40647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40647step0 raw40647; decide +kernel
      have hl : raw40647step0Labels = raw40647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40647 raw40647Labels permutation434 hz
    mixedMoment B raw40647step0 raw40647step0Labels = mixedMoment B raw40647step1 raw40647step1Labels := by
      have hz : ∀ j, raw40647step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40647step1 = (fun i j => raw40647step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40647step1 raw40647step0; decide +kernel
      have hl : raw40647step1Labels = raw40647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40647step0 raw40647step0Labels permutation80 hz
    mixedMoment B raw40647step1 raw40647step1Labels = mixedMoment B raw40647step2 raw40647step2Labels := by
      have ha : raw40647step2 = (fun i j => raw40647step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40647step2 raw40647step1; decide +kernel
      have hl : raw40647step2Labels = raw40647step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40647step1 raw40647step1Labels permutation27 permutation6
    mixedMoment B raw40647step2 raw40647step2Labels = mixedMoment B raw40647step3 raw40647step3Labels := by
      have ha : raw40647step3 = -raw40647step2 := by apply Matrix.ext; change ∀ i j, raw40647step3 i j = -(raw40647step2 i j); unfold raw40647step3 raw40647step2; decide +kernel
      have hl : raw40647step3Labels = raw40647step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3632 node3632Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1184 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1184) =
      Integer.Sparse.eval keyMomentRow1184 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1184).leftCharge (GramAssembly.key 1184).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3846) := by
    have ha : gramCharges (GramAssembly.key 1184).leftCharge (GramAssembly.key 1184).rightCharge = raw40619 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40619Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40619 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1184).leftCharge (GramAssembly.key 1184).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1184, Integer.Sparse.eval]

theorem keyMoment1185 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1185) =
      Integer.Sparse.eval keyMomentRow1185 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1185).leftCharge (GramAssembly.key 1185).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3037) := by
    have ha : gramCharges (GramAssembly.key 1185).leftCharge (GramAssembly.key 1185).rightCharge = raw40620 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40620Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40620 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1185).leftCharge (GramAssembly.key 1185).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1185, Integer.Sparse.eval]

theorem keyMoment1186 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1186) =
      Integer.Sparse.eval keyMomentRow1186 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1186).leftCharge (GramAssembly.key 1186).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3848) := by
    have ha : gramCharges (GramAssembly.key 1186).leftCharge (GramAssembly.key 1186).rightCharge = raw40621 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40621Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40621 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1186).leftCharge (GramAssembly.key 1186).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1186, Integer.Sparse.eval]

theorem keyMoment1187 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1187) =
      Integer.Sparse.eval keyMomentRow1187 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1187).leftCharge (GramAssembly.key 1187).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3849) := by
    have ha : gramCharges (GramAssembly.key 1187).leftCharge (GramAssembly.key 1187).rightCharge = raw40622 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40622Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40622 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1187).leftCharge (GramAssembly.key 1187).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1187, Integer.Sparse.eval]

theorem keyMoment1188 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1188) =
      Integer.Sparse.eval keyMomentRow1188 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1188).leftCharge (GramAssembly.key 1188).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3840) := by
    have ha : gramCharges (GramAssembly.key 1188).leftCharge (GramAssembly.key 1188).rightCharge = raw40623 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40623Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40623 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1188).leftCharge (GramAssembly.key 1188).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1188, Integer.Sparse.eval]

theorem keyMoment1189 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1189) =
      Integer.Sparse.eval keyMomentRow1189 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1189).leftCharge (GramAssembly.key 1189).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2765) := by
    have ha : gramCharges (GramAssembly.key 1189).leftCharge (GramAssembly.key 1189).rightCharge = raw40624 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40624Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40624 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1189).leftCharge (GramAssembly.key 1189).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1189, Integer.Sparse.eval]

theorem keyMoment1190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1190) =
      Integer.Sparse.eval keyMomentRow1190 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1190).leftCharge (GramAssembly.key 1190).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3086) := by
    have ha : gramCharges (GramAssembly.key 1190).leftCharge (GramAssembly.key 1190).rightCharge = raw40625 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40625Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40625 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1190).leftCharge (GramAssembly.key 1190).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1190, Integer.Sparse.eval]

theorem keyMoment1191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1191) =
      Integer.Sparse.eval keyMomentRow1191 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1191).leftCharge (GramAssembly.key 1191).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3850) := by
    have ha : gramCharges (GramAssembly.key 1191).leftCharge (GramAssembly.key 1191).rightCharge = raw40626 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40626Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40626 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1191).leftCharge (GramAssembly.key 1191).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1191, Integer.Sparse.eval]

theorem keyMoment1192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1192) =
      Integer.Sparse.eval keyMomentRow1192 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1192).leftCharge (GramAssembly.key 1192).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3876) := by
    have ha : gramCharges (GramAssembly.key 1192).leftCharge (GramAssembly.key 1192).rightCharge = raw19298 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw19298Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical19298 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1192).leftCharge (GramAssembly.key 1192).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1192, Integer.Sparse.eval]

theorem keyMoment1193 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1193) =
      Integer.Sparse.eval keyMomentRow1193 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1193).leftCharge (GramAssembly.key 1193).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3877) := by
    have ha : gramCharges (GramAssembly.key 1193).leftCharge (GramAssembly.key 1193).rightCharge = raw40627 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40627Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40627 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1193).leftCharge (GramAssembly.key 1193).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1193, Integer.Sparse.eval]

theorem keyMoment1194 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1194) =
      Integer.Sparse.eval keyMomentRow1194 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1194).leftCharge (GramAssembly.key 1194).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3871) := by
    have ha : gramCharges (GramAssembly.key 1194).leftCharge (GramAssembly.key 1194).rightCharge = raw40628 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40628Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40628 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1194).leftCharge (GramAssembly.key 1194).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1194, Integer.Sparse.eval]

theorem keyMoment1195 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1195) =
      Integer.Sparse.eval keyMomentRow1195 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1195).leftCharge (GramAssembly.key 1195).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3872) := by
    have ha : gramCharges (GramAssembly.key 1195).leftCharge (GramAssembly.key 1195).rightCharge = raw40629 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40629Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40629 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1195).leftCharge (GramAssembly.key 1195).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1195, Integer.Sparse.eval]

theorem keyMoment1196 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1196) =
      Integer.Sparse.eval keyMomentRow1196 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1196).leftCharge (GramAssembly.key 1196).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3874) := by
    have ha : gramCharges (GramAssembly.key 1196).leftCharge (GramAssembly.key 1196).rightCharge = raw40630 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40630Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40630 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1196).leftCharge (GramAssembly.key 1196).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1196, Integer.Sparse.eval]

theorem keyMoment1197 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1197) =
      Integer.Sparse.eval keyMomentRow1197 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1197).leftCharge (GramAssembly.key 1197).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3875) := by
    have ha : gramCharges (GramAssembly.key 1197).leftCharge (GramAssembly.key 1197).rightCharge = raw40631 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40631Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40631 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1197).leftCharge (GramAssembly.key 1197).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1197, Integer.Sparse.eval]

theorem keyMoment1198 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1198) =
      Integer.Sparse.eval keyMomentRow1198 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1198).leftCharge (GramAssembly.key 1198).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3886) := by
    have ha : gramCharges (GramAssembly.key 1198).leftCharge (GramAssembly.key 1198).rightCharge = raw40632 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40632Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40632 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1198).leftCharge (GramAssembly.key 1198).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1198, Integer.Sparse.eval]

theorem keyMoment1199 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1199) =
      Integer.Sparse.eval keyMomentRow1199 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1199).leftCharge (GramAssembly.key 1199).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3055) := by
    have ha : gramCharges (GramAssembly.key 1199).leftCharge (GramAssembly.key 1199).rightCharge = raw40633 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40633Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40633 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1199).leftCharge (GramAssembly.key 1199).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1199, Integer.Sparse.eval]

theorem keyMoment1200 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1200) =
      Integer.Sparse.eval keyMomentRow1200 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1200).leftCharge (GramAssembly.key 1200).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3881) := by
    have ha : gramCharges (GramAssembly.key 1200).leftCharge (GramAssembly.key 1200).rightCharge = raw34967 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw34967Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical34967 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1200).leftCharge (GramAssembly.key 1200).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1200, Integer.Sparse.eval]

theorem keyMoment1201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1201) =
      Integer.Sparse.eval keyMomentRow1201 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1201).leftCharge (GramAssembly.key 1201).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3039) := by
    have ha : gramCharges (GramAssembly.key 1201).leftCharge (GramAssembly.key 1201).rightCharge = raw40634 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40634Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40634 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1201).leftCharge (GramAssembly.key 1201).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1201, Integer.Sparse.eval]

theorem keyMoment1202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1202) =
      Integer.Sparse.eval keyMomentRow1202 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1202).leftCharge (GramAssembly.key 1202).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3884) := by
    have ha : gramCharges (GramAssembly.key 1202).leftCharge (GramAssembly.key 1202).rightCharge = raw40635 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40635Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40635 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1202).leftCharge (GramAssembly.key 1202).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1202, Integer.Sparse.eval]

theorem keyMoment1203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1203) =
      Integer.Sparse.eval keyMomentRow1203 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1203).leftCharge (GramAssembly.key 1203).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3885) := by
    have ha : gramCharges (GramAssembly.key 1203).leftCharge (GramAssembly.key 1203).rightCharge = raw40636 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40636Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40636 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1203).leftCharge (GramAssembly.key 1203).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1203, Integer.Sparse.eval]

theorem keyMoment1204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1204) =
      Integer.Sparse.eval keyMomentRow1204 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1204).leftCharge (GramAssembly.key 1204).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2777) := by
    have ha : gramCharges (GramAssembly.key 1204).leftCharge (GramAssembly.key 1204).rightCharge = raw40637 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40637Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40637 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1204).leftCharge (GramAssembly.key 1204).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1204, Integer.Sparse.eval]

theorem keyMoment1205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1205) =
      Integer.Sparse.eval keyMomentRow1205 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1205).leftCharge (GramAssembly.key 1205).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2773) := by
    have ha : gramCharges (GramAssembly.key 1205).leftCharge (GramAssembly.key 1205).rightCharge = raw40638 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40638Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40638 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1205).leftCharge (GramAssembly.key 1205).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1205, Integer.Sparse.eval]

theorem keyMoment1206 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1206) =
      Integer.Sparse.eval keyMomentRow1206 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1206).leftCharge (GramAssembly.key 1206).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2732) := by
    have ha : gramCharges (GramAssembly.key 1206).leftCharge (GramAssembly.key 1206).rightCharge = raw40639 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40639Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40639 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1206).leftCharge (GramAssembly.key 1206).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1206, Integer.Sparse.eval]

theorem keyMoment1207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1207) =
      Integer.Sparse.eval keyMomentRow1207 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1207).leftCharge (GramAssembly.key 1207).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2730) := by
    have ha : gramCharges (GramAssembly.key 1207).leftCharge (GramAssembly.key 1207).rightCharge = raw40640 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40640Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40640 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1207).leftCharge (GramAssembly.key 1207).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1207, Integer.Sparse.eval]

theorem keyMoment1208 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1208) =
      Integer.Sparse.eval keyMomentRow1208 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1208).leftCharge (GramAssembly.key 1208).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2774) := by
    have ha : gramCharges (GramAssembly.key 1208).leftCharge (GramAssembly.key 1208).rightCharge = raw35153 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw35153Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical35153 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1208).leftCharge (GramAssembly.key 1208).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1208, Integer.Sparse.eval]

theorem keyMoment1209 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1209) =
      Integer.Sparse.eval keyMomentRow1209 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1209).leftCharge (GramAssembly.key 1209).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2734) := by
    have ha : gramCharges (GramAssembly.key 1209).leftCharge (GramAssembly.key 1209).rightCharge = raw40641 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40641Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40641 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1209).leftCharge (GramAssembly.key 1209).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1209, Integer.Sparse.eval]

theorem keyMoment1210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1210) =
      Integer.Sparse.eval keyMomentRow1210 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1210).leftCharge (GramAssembly.key 1210).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2731) := by
    have ha : gramCharges (GramAssembly.key 1210).leftCharge (GramAssembly.key 1210).rightCharge = raw40642 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40642Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40642 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1210).leftCharge (GramAssembly.key 1210).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1210, Integer.Sparse.eval]

theorem keyMoment1211 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1211) =
      Integer.Sparse.eval keyMomentRow1211 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1211).leftCharge (GramAssembly.key 1211).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3629) := by
    have ha : gramCharges (GramAssembly.key 1211).leftCharge (GramAssembly.key 1211).rightCharge = raw40643 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40643Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40643 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1211).leftCharge (GramAssembly.key 1211).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1211, Integer.Sparse.eval]

theorem keyMoment1212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1212) =
      Integer.Sparse.eval keyMomentRow1212 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1212).leftCharge (GramAssembly.key 1212).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3905) := by
    have ha : gramCharges (GramAssembly.key 1212).leftCharge (GramAssembly.key 1212).rightCharge = raw40644 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40644Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40644 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1212).leftCharge (GramAssembly.key 1212).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1212, Integer.Sparse.eval]

theorem keyMoment1213 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1213) =
      Integer.Sparse.eval keyMomentRow1213 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1213).leftCharge (GramAssembly.key 1213).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3907) := by
    have ha : gramCharges (GramAssembly.key 1213).leftCharge (GramAssembly.key 1213).rightCharge = raw40645 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40645Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40645 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1213).leftCharge (GramAssembly.key 1213).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1213, Integer.Sparse.eval]

theorem keyMoment1214 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1214) =
      Integer.Sparse.eval keyMomentRow1214 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1214).leftCharge (GramAssembly.key 1214).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2279) := by
    have ha : gramCharges (GramAssembly.key 1214).leftCharge (GramAssembly.key 1214).rightCharge = raw40646 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40646Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40646 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1214).leftCharge (GramAssembly.key 1214).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1214, Integer.Sparse.eval]

theorem keyMoment1215 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1215) =
      Integer.Sparse.eval keyMomentRow1215 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1215).leftCharge (GramAssembly.key 1215).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3632) := by
    have ha : gramCharges (GramAssembly.key 1215).leftCharge (GramAssembly.key 1215).rightCharge = raw40647 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40647Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40647 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1215).leftCharge (GramAssembly.key 1215).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1215, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1184 : keyMomentRows (1184 : Fin 2886) =
    keyMomentRow1184 := by decide +kernel

theorem keyMomentRowsAt1185 : keyMomentRows (1185 : Fin 2886) =
    keyMomentRow1185 := by decide +kernel

theorem keyMomentRowsAt1186 : keyMomentRows (1186 : Fin 2886) =
    keyMomentRow1186 := by decide +kernel

theorem keyMomentRowsAt1187 : keyMomentRows (1187 : Fin 2886) =
    keyMomentRow1187 := by decide +kernel

theorem keyMomentRowsAt1188 : keyMomentRows (1188 : Fin 2886) =
    keyMomentRow1188 := by decide +kernel

theorem keyMomentRowsAt1189 : keyMomentRows (1189 : Fin 2886) =
    keyMomentRow1189 := by decide +kernel

theorem keyMomentRowsAt1190 : keyMomentRows (1190 : Fin 2886) =
    keyMomentRow1190 := by decide +kernel

theorem keyMomentRowsAt1191 : keyMomentRows (1191 : Fin 2886) =
    keyMomentRow1191 := by decide +kernel

theorem keyMomentRowsAt1192 : keyMomentRows (1192 : Fin 2886) =
    keyMomentRow1192 := by decide +kernel

theorem keyMomentRowsAt1193 : keyMomentRows (1193 : Fin 2886) =
    keyMomentRow1193 := by decide +kernel

theorem keyMomentRowsAt1194 : keyMomentRows (1194 : Fin 2886) =
    keyMomentRow1194 := by decide +kernel

theorem keyMomentRowsAt1195 : keyMomentRows (1195 : Fin 2886) =
    keyMomentRow1195 := by decide +kernel

theorem keyMomentRowsAt1196 : keyMomentRows (1196 : Fin 2886) =
    keyMomentRow1196 := by decide +kernel

theorem keyMomentRowsAt1197 : keyMomentRows (1197 : Fin 2886) =
    keyMomentRow1197 := by decide +kernel

theorem keyMomentRowsAt1198 : keyMomentRows (1198 : Fin 2886) =
    keyMomentRow1198 := by decide +kernel

theorem keyMomentRowsAt1199 : keyMomentRows (1199 : Fin 2886) =
    keyMomentRow1199 := by decide +kernel

theorem keyMomentRowsAt1200 : keyMomentRows (1200 : Fin 2886) =
    keyMomentRow1200 := by decide +kernel

theorem keyMomentRowsAt1201 : keyMomentRows (1201 : Fin 2886) =
    keyMomentRow1201 := by decide +kernel

theorem keyMomentRowsAt1202 : keyMomentRows (1202 : Fin 2886) =
    keyMomentRow1202 := by decide +kernel

theorem keyMomentRowsAt1203 : keyMomentRows (1203 : Fin 2886) =
    keyMomentRow1203 := by decide +kernel

theorem keyMomentRowsAt1204 : keyMomentRows (1204 : Fin 2886) =
    keyMomentRow1204 := by decide +kernel

theorem keyMomentRowsAt1205 : keyMomentRows (1205 : Fin 2886) =
    keyMomentRow1205 := by decide +kernel

theorem keyMomentRowsAt1206 : keyMomentRows (1206 : Fin 2886) =
    keyMomentRow1206 := by decide +kernel

theorem keyMomentRowsAt1207 : keyMomentRows (1207 : Fin 2886) =
    keyMomentRow1207 := by decide +kernel

theorem keyMomentRowsAt1208 : keyMomentRows (1208 : Fin 2886) =
    keyMomentRow1208 := by decide +kernel

theorem keyMomentRowsAt1209 : keyMomentRows (1209 : Fin 2886) =
    keyMomentRow1209 := by decide +kernel

theorem keyMomentRowsAt1210 : keyMomentRows (1210 : Fin 2886) =
    keyMomentRow1210 := by decide +kernel

theorem keyMomentRowsAt1211 : keyMomentRows (1211 : Fin 2886) =
    keyMomentRow1211 := by decide +kernel

theorem keyMomentRowsAt1212 : keyMomentRows (1212 : Fin 2886) =
    keyMomentRow1212 := by decide +kernel

theorem keyMomentRowsAt1213 : keyMomentRows (1213 : Fin 2886) =
    keyMomentRow1213 := by decide +kernel

theorem keyMomentRowsAt1214 : keyMomentRows (1214 : Fin 2886) =
    keyMomentRow1214 := by decide +kernel

theorem keyMomentRowsAt1215 : keyMomentRows (1215 : Fin 2886) =
    keyMomentRow1215 := by decide +kernel

theorem keyMomentChunkSound37_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 37) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1184 ∨ k.val = 1185 ∨ k.val = 1186 ∨ k.val = 1187 ∨ k.val = 1188 ∨ k.val = 1189 ∨ k.val = 1190 ∨ k.val = 1191 ∨ k.val = 1192 ∨ k.val = 1193 ∨ k.val = 1194 ∨ k.val = 1195 ∨ k.val = 1196 ∨ k.val = 1197 ∨ k.val = 1198 ∨ k.val = 1199 ∨ k.val = 1200 ∨ k.val = 1201 ∨ k.val = 1202 ∨ k.val = 1203 ∨ k.val = 1204 ∨ k.val = 1205 ∨ k.val = 1206 ∨ k.val = 1207 ∨ k.val = 1208 ∨ k.val = 1209 ∨ k.val = 1210 ∨ k.val = 1211 ∨ k.val = 1212 ∨ k.val = 1213 ∨ k.val = 1214 ∨ k.val = 1215 := by omega
  rcases heq with h1184 | h1185 | h1186 | h1187 | h1188 | h1189 | h1190 | h1191 | h1192 | h1193 | h1194 | h1195 | h1196 | h1197 | h1198 | h1199 | h1200 | h1201 | h1202 | h1203 | h1204 | h1205 | h1206 | h1207 | h1208 | h1209 | h1210 | h1211 | h1212 | h1213 | h1214 | h1215
  · have he : k = (1184 : Fin 2886) := Fin.ext h1184
    subst k
    rw [keyMomentRowsAt1184]
    exact keyMoment1184 B hB
  · have he : k = (1185 : Fin 2886) := Fin.ext h1185
    subst k
    rw [keyMomentRowsAt1185]
    exact keyMoment1185 B hB
  · have he : k = (1186 : Fin 2886) := Fin.ext h1186
    subst k
    rw [keyMomentRowsAt1186]
    exact keyMoment1186 B hB
  · have he : k = (1187 : Fin 2886) := Fin.ext h1187
    subst k
    rw [keyMomentRowsAt1187]
    exact keyMoment1187 B hB
  · have he : k = (1188 : Fin 2886) := Fin.ext h1188
    subst k
    rw [keyMomentRowsAt1188]
    exact keyMoment1188 B hB
  · have he : k = (1189 : Fin 2886) := Fin.ext h1189
    subst k
    rw [keyMomentRowsAt1189]
    exact keyMoment1189 B hB
  · have he : k = (1190 : Fin 2886) := Fin.ext h1190
    subst k
    rw [keyMomentRowsAt1190]
    exact keyMoment1190 B hB
  · have he : k = (1191 : Fin 2886) := Fin.ext h1191
    subst k
    rw [keyMomentRowsAt1191]
    exact keyMoment1191 B hB
  · have he : k = (1192 : Fin 2886) := Fin.ext h1192
    subst k
    rw [keyMomentRowsAt1192]
    exact keyMoment1192 B hB
  · have he : k = (1193 : Fin 2886) := Fin.ext h1193
    subst k
    rw [keyMomentRowsAt1193]
    exact keyMoment1193 B hB
  · have he : k = (1194 : Fin 2886) := Fin.ext h1194
    subst k
    rw [keyMomentRowsAt1194]
    exact keyMoment1194 B hB
  · have he : k = (1195 : Fin 2886) := Fin.ext h1195
    subst k
    rw [keyMomentRowsAt1195]
    exact keyMoment1195 B hB
  · have he : k = (1196 : Fin 2886) := Fin.ext h1196
    subst k
    rw [keyMomentRowsAt1196]
    exact keyMoment1196 B hB
  · have he : k = (1197 : Fin 2886) := Fin.ext h1197
    subst k
    rw [keyMomentRowsAt1197]
    exact keyMoment1197 B hB
  · have he : k = (1198 : Fin 2886) := Fin.ext h1198
    subst k
    rw [keyMomentRowsAt1198]
    exact keyMoment1198 B hB
  · have he : k = (1199 : Fin 2886) := Fin.ext h1199
    subst k
    rw [keyMomentRowsAt1199]
    exact keyMoment1199 B hB
  · have he : k = (1200 : Fin 2886) := Fin.ext h1200
    subst k
    rw [keyMomentRowsAt1200]
    exact keyMoment1200 B hB
  · have he : k = (1201 : Fin 2886) := Fin.ext h1201
    subst k
    rw [keyMomentRowsAt1201]
    exact keyMoment1201 B hB
  · have he : k = (1202 : Fin 2886) := Fin.ext h1202
    subst k
    rw [keyMomentRowsAt1202]
    exact keyMoment1202 B hB
  · have he : k = (1203 : Fin 2886) := Fin.ext h1203
    subst k
    rw [keyMomentRowsAt1203]
    exact keyMoment1203 B hB
  · have he : k = (1204 : Fin 2886) := Fin.ext h1204
    subst k
    rw [keyMomentRowsAt1204]
    exact keyMoment1204 B hB
  · have he : k = (1205 : Fin 2886) := Fin.ext h1205
    subst k
    rw [keyMomentRowsAt1205]
    exact keyMoment1205 B hB
  · have he : k = (1206 : Fin 2886) := Fin.ext h1206
    subst k
    rw [keyMomentRowsAt1206]
    exact keyMoment1206 B hB
  · have he : k = (1207 : Fin 2886) := Fin.ext h1207
    subst k
    rw [keyMomentRowsAt1207]
    exact keyMoment1207 B hB
  · have he : k = (1208 : Fin 2886) := Fin.ext h1208
    subst k
    rw [keyMomentRowsAt1208]
    exact keyMoment1208 B hB
  · have he : k = (1209 : Fin 2886) := Fin.ext h1209
    subst k
    rw [keyMomentRowsAt1209]
    exact keyMoment1209 B hB
  · have he : k = (1210 : Fin 2886) := Fin.ext h1210
    subst k
    rw [keyMomentRowsAt1210]
    exact keyMoment1210 B hB
  · have he : k = (1211 : Fin 2886) := Fin.ext h1211
    subst k
    rw [keyMomentRowsAt1211]
    exact keyMoment1211 B hB
  · have he : k = (1212 : Fin 2886) := Fin.ext h1212
    subst k
    rw [keyMomentRowsAt1212]
    exact keyMoment1212 B hB
  · have he : k = (1213 : Fin 2886) := Fin.ext h1213
    subst k
    rw [keyMomentRowsAt1213]
    exact keyMoment1213 B hB
  · have he : k = (1214 : Fin 2886) := Fin.ext h1214
    subst k
    rw [keyMomentRowsAt1214]
    exact keyMoment1214 B hB
  · have he : k = (1215 : Fin 2886) := Fin.ext h1215
    subst k
    rw [keyMomentRowsAt1215]
    exact keyMoment1215 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound37_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound37_e_oai
