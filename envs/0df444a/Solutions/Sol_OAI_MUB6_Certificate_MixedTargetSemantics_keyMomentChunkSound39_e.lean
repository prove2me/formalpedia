-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound39_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:54:35.826829+00:00
-- url     : https://prove2.me/submissions/17ea6461-c2d0-444c-bbb4-63ba78573578

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E093
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17178 raw17178Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw17178 raw17178Labels = mixedMoment B raw17178step0 raw17178step0Labels := by
      have hz : ∀ j, raw17178 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17178step0 = (fun i j => raw17178 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17178step0 raw17178; decide +kernel
      have hl : raw17178step0Labels = raw17178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17178 raw17178Labels permutation520 hz
    mixedMoment B raw17178step0 raw17178step0Labels = mixedMoment B raw17178step1 raw17178step1Labels := by
      have ha : raw17178step1 = (fun i j => raw17178step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17178step1 raw17178step0; decide +kernel
      have hl : raw17178step1Labels = raw17178step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17178step0 raw17178step0Labels permutation145 permutation3
    mixedMoment B raw17178step1 raw17178step1Labels = mixedMoment B raw17178step2 raw17178step2Labels := by
      have ha : raw17178step2 = -raw17178step1 := by apply Matrix.ext; change ∀ i j, raw17178step2 i j = -(raw17178step1 i j); unfold raw17178step2 raw17178step1; decide +kernel
      have hl : raw17178step2Labels = raw17178step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2244 node2244Labels := by rfl

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

theorem canonical40675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40675 raw40675Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw40675 raw40675Labels = mixedMoment B raw40675step0 raw40675step0Labels := by
      have ha : raw40675step0 = (fun i j => raw40675 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40675step0 raw40675; decide +kernel
      have hl : raw40675step0Labels = raw40675Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40675 raw40675Labels permutation152 permutation3
    _ = mixedMoment B node3956 node3956Labels := by rfl

theorem canonical40676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40676 raw40676Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw40676 raw40676Labels = mixedMoment B raw40676step0 raw40676step0Labels := by
      have ha : raw40676step0 = (fun i j => raw40676 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40676step0 raw40676; decide +kernel
      have hl : raw40676step0Labels = raw40676Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40676 raw40676Labels permutation152 permutation3
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical40677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40677 raw40677Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw40677 raw40677Labels = mixedMoment B raw40677step0 raw40677step0Labels := by
      have hz : ∀ j, raw40677 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40677step0 = (fun i j => raw40677 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40677step0 raw40677; decide +kernel
      have hl : raw40677step0Labels = raw40677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40677 raw40677Labels permutation520 hz
    mixedMoment B raw40677step0 raw40677step0Labels = mixedMoment B raw40677step1 raw40677step1Labels := by
      have hz : ∀ j, raw40677step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40677step1 = (fun i j => raw40677step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40677step1 raw40677step0; decide +kernel
      have hl : raw40677step1Labels = raw40677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40677step0 raw40677step0Labels permutation104 hz
    mixedMoment B raw40677step1 raw40677step1Labels = mixedMoment B raw40677step2 raw40677step2Labels := by
      have ha : raw40677step2 = (fun i j => raw40677step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40677step2 raw40677step1; decide +kernel
      have hl : raw40677step2Labels = raw40677step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40677step1 raw40677step1Labels permutation31 permutation3
    mixedMoment B raw40677step2 raw40677step2Labels = mixedMoment B raw40677step3 raw40677step3Labels := by
      have ha : raw40677step3 = -raw40677step2 := by apply Matrix.ext; change ∀ i j, raw40677step3 i j = -(raw40677step2 i j); unfold raw40677step3 raw40677step2; decide +kernel
      have hl : raw40677step3Labels = raw40677step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2265 node2265Labels := by rfl

theorem canonical40678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40678 raw40678Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw40678 raw40678Labels = mixedMoment B raw40678step0 raw40678step0Labels := by
      have hz : ∀ j, raw40678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40678step0 = (fun i j => raw40678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40678step0 raw40678; decide +kernel
      have hl : raw40678step0Labels = raw40678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40678 raw40678Labels permutation434 hz
    mixedMoment B raw40678step0 raw40678step0Labels = mixedMoment B raw40678step1 raw40678step1Labels := by
      have ha : raw40678step1 = (fun i j => raw40678step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40678step1 raw40678step0; decide +kernel
      have hl : raw40678step1Labels = raw40678step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40678step0 raw40678step0Labels permutation151 permutation3
    mixedMoment B raw40678step1 raw40678step1Labels = mixedMoment B raw40678step2 raw40678step2Labels := by
      have ha : raw40678step2 = -raw40678step1 := by apply Matrix.ext; change ∀ i j, raw40678step2 i j = -(raw40678step1 i j); unfold raw40678step2 raw40678step1; decide +kernel
      have hl : raw40678step2Labels = raw40678step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3808 node3808Labels := by rfl

theorem canonical40679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40679 raw40679Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw40679 raw40679Labels = mixedMoment B raw40679step0 raw40679step0Labels := by
      have hz : ∀ j, raw40679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40679step0 = (fun i j => raw40679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40679step0 raw40679; decide +kernel
      have hl : raw40679step0Labels = raw40679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40679 raw40679Labels permutation434 hz
    mixedMoment B raw40679step0 raw40679step0Labels = mixedMoment B raw40679step1 raw40679step1Labels := by
      have ha : raw40679step1 = (fun i j => raw40679step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40679step1 raw40679step0; decide +kernel
      have hl : raw40679step1Labels = raw40679step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40679step0 raw40679step0Labels permutation151 permutation3
    mixedMoment B raw40679step1 raw40679step1Labels = mixedMoment B raw40679step2 raw40679step2Labels := by
      have ha : raw40679step2 = -raw40679step1 := by apply Matrix.ext; change ∀ i j, raw40679step2 i j = -(raw40679step1 i j); unfold raw40679step2 raw40679step1; decide +kernel
      have hl : raw40679step2Labels = raw40679step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical40680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40680 raw40680Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw40680 raw40680Labels = mixedMoment B raw40680step0 raw40680step0Labels := by
      have hz : ∀ j, raw40680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40680step0 = (fun i j => raw40680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40680step0 raw40680; decide +kernel
      have hl : raw40680step0Labels = raw40680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40680 raw40680Labels permutation434 hz
    mixedMoment B raw40680step0 raw40680step0Labels = mixedMoment B raw40680step1 raw40680step1Labels := by
      have ha : raw40680step1 = (fun i j => raw40680step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40680step1 raw40680step0; decide +kernel
      have hl : raw40680step1Labels = raw40680step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40680step0 raw40680step0Labels permutation104 permutation6
    mixedMoment B raw40680step1 raw40680step1Labels = mixedMoment B raw40680step2 raw40680step2Labels := by
      have ha : raw40680step2 = -raw40680step1 := by apply Matrix.ext; change ∀ i j, raw40680step2 i j = -(raw40680step1 i j); unfold raw40680step2 raw40680step1; decide +kernel
      have hl : raw40680step2Labels = raw40680step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical40681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40681 raw40681Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw40681 raw40681Labels = mixedMoment B raw40681step0 raw40681step0Labels := by
      have ha : raw40681step0 = (fun i j => raw40681 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40681step0 raw40681; decide +kernel
      have hl : raw40681step0Labels = raw40681Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40681 raw40681Labels permutation152 permutation3
    _ = mixedMoment B node3972 node3972Labels := by rfl

theorem canonical40682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40682 raw40682Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw40682 raw40682Labels = mixedMoment B raw40682step0 raw40682step0Labels := by
      have ha : raw40682step0 = (fun i j => raw40682 (permutation439 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40682step0 raw40682; decide +kernel
      have hl : raw40682step0Labels = raw40682Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40682 raw40682Labels permutation439 permutation6
    mixedMoment B raw40682step0 raw40682step0Labels = mixedMoment B raw40682step1 raw40682step1Labels := by
      have ha : raw40682step1 = -raw40682step0 := by apply Matrix.ext; change ∀ i j, raw40682step1 i j = -(raw40682step0 i j); unfold raw40682step1 raw40682step0; decide +kernel
      have hl : raw40682step1Labels = raw40682step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical40683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40683 raw40683Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw40683 raw40683Labels = mixedMoment B raw40683step0 raw40683step0Labels := by
      have ha : raw40683step0 = (fun i j => raw40683 (permutation443 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40683step0 raw40683; decide +kernel
      have hl : raw40683step0Labels = raw40683Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40683 raw40683Labels permutation443 permutation6
    mixedMoment B raw40683step0 raw40683step0Labels = mixedMoment B raw40683step1 raw40683step1Labels := by
      have ha : raw40683step1 = -raw40683step0 := by apply Matrix.ext; change ∀ i j, raw40683step1 i j = -(raw40683step0 i j); unfold raw40683step1 raw40683step0; decide +kernel
      have hl : raw40683step1Labels = raw40683step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3872 node3872Labels := by rfl

theorem canonical40684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40684 raw40684Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw40684 raw40684Labels = mixedMoment B raw40684step0 raw40684step0Labels := by
      have hz : ∀ j, raw40684 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40684step0 = (fun i j => raw40684 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40684step0 raw40684; decide +kernel
      have hl : raw40684step0Labels = raw40684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40684 raw40684Labels permutation434 hz
    mixedMoment B raw40684step0 raw40684step0Labels = mixedMoment B raw40684step1 raw40684step1Labels := by
      have hz : ∀ j, raw40684step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40684step1 = (fun i j => raw40684step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40684step1 raw40684step0; decide +kernel
      have hl : raw40684step1Labels = raw40684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40684step0 raw40684step0Labels permutation80 hz
    mixedMoment B raw40684step1 raw40684step1Labels = mixedMoment B raw40684step2 raw40684step2Labels := by
      have ha : raw40684step2 = (fun i j => raw40684step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40684step2 raw40684step1; decide +kernel
      have hl : raw40684step2Labels = raw40684step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40684step1 raw40684step1Labels permutation28 permutation6
    _ = mixedMoment B node3098 node3098Labels := by rfl

theorem canonical40685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40685 raw40685Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw40685 raw40685Labels = mixedMoment B raw40685step0 raw40685step0Labels := by
      have hz : ∀ j, raw40685 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40685step0 = (fun i j => raw40685 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40685step0 raw40685; decide +kernel
      have hl : raw40685step0Labels = raw40685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40685 raw40685Labels permutation520 hz
    mixedMoment B raw40685step0 raw40685step0Labels = mixedMoment B raw40685step1 raw40685step1Labels := by
      have hz : ∀ j, raw40685step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40685step1 = (fun i j => raw40685step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40685step1 raw40685step0; decide +kernel
      have hl : raw40685step1Labels = raw40685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40685step0 raw40685step0Labels permutation104 hz
    mixedMoment B raw40685step1 raw40685step1Labels = mixedMoment B raw40685step2 raw40685step2Labels := by
      have ha : raw40685step2 = (fun i j => raw40685step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40685step2 raw40685step1; decide +kernel
      have hl : raw40685step2Labels = raw40685step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40685step1 raw40685step1Labels permutation31 permutation3
    mixedMoment B raw40685step2 raw40685step2Labels = mixedMoment B raw40685step3 raw40685step3Labels := by
      have ha : raw40685step3 = -raw40685step2 := by apply Matrix.ext; change ∀ i j, raw40685step3 i j = -(raw40685step2 i j); unfold raw40685step3 raw40685step2; decide +kernel
      have hl : raw40685step3Labels = raw40685step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2278 node2278Labels := by rfl

theorem canonical40686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40686 raw40686Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw40686 raw40686Labels = mixedMoment B raw40686step0 raw40686step0Labels := by
      have hz : ∀ j, raw40686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40686step0 = (fun i j => raw40686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40686step0 raw40686; decide +kernel
      have hl : raw40686step0Labels = raw40686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40686 raw40686Labels permutation434 hz
    mixedMoment B raw40686step0 raw40686step0Labels = mixedMoment B raw40686step1 raw40686step1Labels := by
      have ha : raw40686step1 = (fun i j => raw40686step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40686step1 raw40686step0; decide +kernel
      have hl : raw40686step1Labels = raw40686step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40686step0 raw40686step0Labels permutation151 permutation3
    mixedMoment B raw40686step1 raw40686step1Labels = mixedMoment B raw40686step2 raw40686step2Labels := by
      have ha : raw40686step2 = -raw40686step1 := by apply Matrix.ext; change ∀ i j, raw40686step2 i j = -(raw40686step1 i j); unfold raw40686step2 raw40686step1; decide +kernel
      have hl : raw40686step2Labels = raw40686step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2731 node2731Labels := by rfl

theorem canonical40687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40687 raw40687Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw40687 raw40687Labels = mixedMoment B raw40687step0 raw40687step0Labels := by
      have hz : ∀ j, raw40687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40687step0 = (fun i j => raw40687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40687step0 raw40687; decide +kernel
      have hl : raw40687step0Labels = raw40687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40687 raw40687Labels permutation434 hz
    mixedMoment B raw40687step0 raw40687step0Labels = mixedMoment B raw40687step1 raw40687step1Labels := by
      have ha : raw40687step1 = (fun i j => raw40687step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40687step1 raw40687step0; decide +kernel
      have hl : raw40687step1Labels = raw40687step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40687step0 raw40687step0Labels permutation151 permutation3
    mixedMoment B raw40687step1 raw40687step1Labels = mixedMoment B raw40687step2 raw40687step2Labels := by
      have ha : raw40687step2 = -raw40687step1 := by apply Matrix.ext; change ∀ i j, raw40687step2 i j = -(raw40687step1 i j); unfold raw40687step2 raw40687step1; decide +kernel
      have hl : raw40687step2Labels = raw40687step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3044 node3044Labels := by rfl

theorem canonical40688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40688 raw40688Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw40688 raw40688Labels = mixedMoment B raw40688step0 raw40688step0Labels := by
      have hz : ∀ j, raw40688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40688step0 = (fun i j => raw40688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40688step0 raw40688; decide +kernel
      have hl : raw40688step0Labels = raw40688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40688 raw40688Labels permutation434 hz
    mixedMoment B raw40688step0 raw40688step0Labels = mixedMoment B raw40688step1 raw40688step1Labels := by
      have ha : raw40688step1 = (fun i j => raw40688step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40688step1 raw40688step0; decide +kernel
      have hl : raw40688step1Labels = raw40688step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40688step0 raw40688step0Labels permutation151 permutation3
    mixedMoment B raw40688step1 raw40688step1Labels = mixedMoment B raw40688step2 raw40688step2Labels := by
      have ha : raw40688step2 = -raw40688step1 := by apply Matrix.ext; change ∀ i j, raw40688step2 i j = -(raw40688step1 i j); unfold raw40688step2 raw40688step1; decide +kernel
      have hl : raw40688step2Labels = raw40688step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical40689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40689 raw40689Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw40689 raw40689Labels = mixedMoment B raw40689step0 raw40689step0Labels := by
      have hz : ∀ j, raw40689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40689step0 = (fun i j => raw40689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40689step0 raw40689; decide +kernel
      have hl : raw40689step0Labels = raw40689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40689 raw40689Labels permutation434 hz
    mixedMoment B raw40689step0 raw40689step0Labels = mixedMoment B raw40689step1 raw40689step1Labels := by
      have ha : raw40689step1 = (fun i j => raw40689step0 (permutation98 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40689step1 raw40689step0; decide +kernel
      have hl : raw40689step1Labels = raw40689step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40689step0 raw40689step0Labels permutation98 permutation6
    _ = mixedMoment B node3884 node3884Labels := by rfl

theorem canonical40690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40690 raw40690Labels = mixedMoment B node3506 node3506Labels := by
  calc
    mixedMoment B raw40690 raw40690Labels = mixedMoment B raw40690step0 raw40690step0Labels := by
      have hz : ∀ j, raw40690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40690step0 = (fun i j => raw40690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40690step0 raw40690; decide +kernel
      have hl : raw40690step0Labels = raw40690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40690 raw40690Labels permutation434 hz
    mixedMoment B raw40690step0 raw40690step0Labels = mixedMoment B raw40690step1 raw40690step1Labels := by
      have ha : raw40690step1 = (fun i j => raw40690step0 (permutation111 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40690step1 raw40690step0; decide +kernel
      have hl : raw40690step1Labels = raw40690step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40690step0 raw40690step0Labels permutation111 permutation6
    mixedMoment B raw40690step1 raw40690step1Labels = mixedMoment B raw40690step2 raw40690step2Labels := by
      have ha : raw40690step2 = -raw40690step1 := by apply Matrix.ext; change ∀ i j, raw40690step2 i j = -(raw40690step1 i j); unfold raw40690step2 raw40690step1; decide +kernel
      have hl : raw40690step2Labels = raw40690step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3506 node3506Labels := by rfl

theorem canonical40691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40691 raw40691Labels = mixedMoment B node3068 node3068Labels := by
  calc
    mixedMoment B raw40691 raw40691Labels = mixedMoment B raw40691step0 raw40691step0Labels := by
      have ha : raw40691step0 = (fun i j => raw40691 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40691step0 raw40691; decide +kernel
      have hl : raw40691step0Labels = raw40691Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40691 raw40691Labels permutation664 permutation3
    mixedMoment B raw40691step0 raw40691step0Labels = mixedMoment B raw40691step1 raw40691step1Labels := by
      have ha : raw40691step1 = -raw40691step0 := by apply Matrix.ext; change ∀ i j, raw40691step1 i j = -(raw40691step0 i j); unfold raw40691step1 raw40691step0; decide +kernel
      have hl : raw40691step1Labels = raw40691step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3068 node3068Labels := by rfl

theorem canonical40692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40692 raw40692Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw40692 raw40692Labels = mixedMoment B raw40692step0 raw40692step0Labels := by
      have ha : raw40692step0 = (fun i j => raw40692 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40692step0 raw40692; decide +kernel
      have hl : raw40692step0Labels = raw40692Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40692 raw40692Labels permutation688 permutation3
    mixedMoment B raw40692step0 raw40692step0Labels = mixedMoment B raw40692step1 raw40692step1Labels := by
      have ha : raw40692step1 = -raw40692step0 := by apply Matrix.ext; change ∀ i j, raw40692step1 i j = -(raw40692step0 i j); unfold raw40692step1 raw40692step0; decide +kernel
      have hl : raw40692step1Labels = raw40692step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical40693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40693 raw40693Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw40693 raw40693Labels = mixedMoment B raw40693step0 raw40693step0Labels := by
      have ha : raw40693step0 = (fun i j => raw40693 (permutation428 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40693step0 raw40693; decide +kernel
      have hl : raw40693step0Labels = raw40693Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40693 raw40693Labels permutation428 permutation6
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical40694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40694 raw40694Labels = mixedMoment B node3730 node3730Labels := by
  calc
    mixedMoment B raw40694 raw40694Labels = mixedMoment B raw40694step0 raw40694step0Labels := by
      have ha : raw40694step0 = (fun i j => raw40694 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40694step0 raw40694; decide +kernel
      have hl : raw40694step0Labels = raw40694Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40694 raw40694Labels permutation414 permutation6
    _ = mixedMoment B node3730 node3730Labels := by rfl

theorem canonical40695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40695 raw40695Labels = mixedMoment B node3826 node3826Labels := by
  calc
    mixedMoment B raw40695 raw40695Labels = mixedMoment B raw40695step0 raw40695step0Labels := by
      have ha : raw40695step0 = (fun i j => raw40695 (permutation409 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40695step0 raw40695; decide +kernel
      have hl : raw40695step0Labels = raw40695Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40695 raw40695Labels permutation409 permutation6
    _ = mixedMoment B node3826 node3826Labels := by rfl

theorem canonical40696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40696 raw40696Labels = mixedMoment B node3723 node3723Labels := by
  calc
    mixedMoment B raw40696 raw40696Labels = mixedMoment B raw40696step0 raw40696step0Labels := by
      have ha : raw40696step0 = (fun i j => raw40696 (permutation428 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40696step0 raw40696; decide +kernel
      have hl : raw40696step0Labels = raw40696Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40696 raw40696Labels permutation428 permutation6
    _ = mixedMoment B node3723 node3723Labels := by rfl

theorem canonical40697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40697 raw40697Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw40697 raw40697Labels = mixedMoment B raw40697step0 raw40697step0Labels := by
      have ha : raw40697step0 = (fun i j => raw40697 (permutation389 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40697step0 raw40697; decide +kernel
      have hl : raw40697step0Labels = raw40697Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40697 raw40697Labels permutation389 permutation6
    _ = mixedMoment B node3848 node3848Labels := by rfl

theorem canonical40698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40698 raw40698Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw40698 raw40698Labels = mixedMoment B raw40698step0 raw40698step0Labels := by
      have ha : raw40698step0 = (fun i j => raw40698 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40698step0 raw40698; decide +kernel
      have hl : raw40698step0Labels = raw40698Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40698 raw40698Labels permutation393 permutation6
    _ = mixedMoment B node3909 node3909Labels := by rfl

theorem canonical40699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40699 raw40699Labels = mixedMoment B node2709 node2709Labels := by
  calc
    mixedMoment B raw40699 raw40699Labels = mixedMoment B raw40699step0 raw40699step0Labels := by
      have ha : raw40699step0 = (fun i j => raw40699 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40699step0 raw40699; decide +kernel
      have hl : raw40699step0Labels = raw40699Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40699 raw40699Labels permutation682 permutation3
    mixedMoment B raw40699step0 raw40699step0Labels = mixedMoment B raw40699step1 raw40699step1Labels := by
      have ha : raw40699step1 = -raw40699step0 := by apply Matrix.ext; change ∀ i j, raw40699step1 i j = -(raw40699step0 i j); unfold raw40699step1 raw40699step0; decide +kernel
      have hl : raw40699step1Labels = raw40699step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2709 node2709Labels := by rfl

theorem canonical40700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40700 raw40700Labels = mixedMoment B node3029 node3029Labels := by
  calc
    mixedMoment B raw40700 raw40700Labels = mixedMoment B raw40700step0 raw40700step0Labels := by
      have ha : raw40700step0 = (fun i j => raw40700 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40700step0 raw40700; decide +kernel
      have hl : raw40700step0Labels = raw40700Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40700 raw40700Labels permutation682 permutation3
    mixedMoment B raw40700step0 raw40700step0Labels = mixedMoment B raw40700step1 raw40700step1Labels := by
      have ha : raw40700step1 = -raw40700step0 := by apply Matrix.ext; change ∀ i j, raw40700step1 i j = -(raw40700step0 i j); unfold raw40700step1 raw40700step0; decide +kernel
      have hl : raw40700step1Labels = raw40700step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3029 node3029Labels := by rfl

theorem canonical40701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40701 raw40701Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw40701 raw40701Labels = mixedMoment B raw40701step0 raw40701step0Labels := by
      have ha : raw40701step0 = (fun i j => raw40701 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40701step0 raw40701; decide +kernel
      have hl : raw40701step0Labels = raw40701Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40701 raw40701Labels permutation682 permutation3
    mixedMoment B raw40701step0 raw40701step0Labels = mixedMoment B raw40701step1 raw40701step1Labels := by
      have ha : raw40701step1 = -raw40701step0 := by apply Matrix.ext; change ∀ i j, raw40701step1 i j = -(raw40701step0 i j); unfold raw40701step1 raw40701step0; decide +kernel
      have hl : raw40701step1Labels = raw40701step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical40702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40702 raw40702Labels = mixedMoment B node3953 node3953Labels := by
  calc
    mixedMoment B raw40702 raw40702Labels = mixedMoment B raw40702step0 raw40702step0Labels := by
      have ha : raw40702step0 = (fun i j => raw40702 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40702step0 raw40702; decide +kernel
      have hl : raw40702step0Labels = raw40702Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40702 raw40702Labels permutation682 permutation3
    mixedMoment B raw40702step0 raw40702step0Labels = mixedMoment B raw40702step1 raw40702step1Labels := by
      have ha : raw40702step1 = -raw40702step0 := by apply Matrix.ext; change ∀ i j, raw40702step1 i j = -(raw40702step0 i j); unfold raw40702step1 raw40702step0; decide +kernel
      have hl : raw40702step1Labels = raw40702step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3953 node3953Labels := by rfl

theorem canonical40703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40703 raw40703Labels = mixedMoment B node3505 node3505Labels := by
  calc
    mixedMoment B raw40703 raw40703Labels = mixedMoment B raw40703step0 raw40703step0Labels := by
      have ha : raw40703step0 = (fun i j => raw40703 (permutation529 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40703step0 raw40703; decide +kernel
      have hl : raw40703step0Labels = raw40703Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40703 raw40703Labels permutation529 permutation6
    mixedMoment B raw40703step0 raw40703step0Labels = mixedMoment B raw40703step1 raw40703step1Labels := by
      have ha : raw40703step1 = -raw40703step0 := by apply Matrix.ext; change ∀ i j, raw40703step1 i j = -(raw40703step0 i j); unfold raw40703step1 raw40703step0; decide +kernel
      have hl : raw40703step1Labels = raw40703step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3505 node3505Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical318
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40704 raw40704Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw40704 raw40704Labels = mixedMoment B raw40704step0 raw40704step0Labels := by
      have hz : ∀ j, raw40704 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40704step0 = (fun i j => raw40704 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40704step0 raw40704; decide +kernel
      have hl : raw40704step0Labels = raw40704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40704 raw40704Labels permutation434 hz
    mixedMoment B raw40704step0 raw40704step0Labels = mixedMoment B raw40704step1 raw40704step1Labels := by
      have ha : raw40704step1 = (fun i j => raw40704step0 (permutation140 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40704step1 raw40704step0; decide +kernel
      have hl : raw40704step1Labels = raw40704step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40704step0 raw40704step0Labels permutation140 permutation6
    _ = mixedMoment B node2952 node2952Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11912 raw11912Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw11912 raw11912Labels = mixedMoment B raw11912step0 raw11912step0Labels := by
      have ha : raw11912step0 = (fun i j => raw11912 (permutation364 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11912step0 raw11912; decide +kernel
      have hl : raw11912step0Labels = raw11912Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11912 raw11912Labels permutation364 permutation6
    mixedMoment B raw11912step0 raw11912step0Labels = mixedMoment B raw11912step1 raw11912step1Labels := by
      have ha : raw11912step1 = -raw11912step0 := by apply Matrix.ext; change ∀ i j, raw11912step1 i j = -(raw11912step0 i j); unfold raw11912step1 raw11912step0; decide +kernel
      have hl : raw11912step1Labels = raw11912step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3874 node3874Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1248) =
      Integer.Sparse.eval keyMomentRow1248 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1248).leftCharge (GramAssembly.key 1248).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3956) := by
    have ha : gramCharges (GramAssembly.key 1248).leftCharge (GramAssembly.key 1248).rightCharge = raw40675 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40675Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40675 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1248).leftCharge (GramAssembly.key 1248).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1248, Integer.Sparse.eval]

theorem keyMoment1249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1249) =
      Integer.Sparse.eval keyMomentRow1249 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1249).leftCharge (GramAssembly.key 1249).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3957) := by
    have ha : gramCharges (GramAssembly.key 1249).leftCharge (GramAssembly.key 1249).rightCharge = raw40676 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40676Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40676 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1249).leftCharge (GramAssembly.key 1249).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1249, Integer.Sparse.eval]

theorem keyMoment1250 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1250) =
      Integer.Sparse.eval keyMomentRow1250 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1250).leftCharge (GramAssembly.key 1250).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3874) := by
    have ha : gramCharges (GramAssembly.key 1250).leftCharge (GramAssembly.key 1250).rightCharge = raw11912 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw11912Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical11912 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1250).leftCharge (GramAssembly.key 1250).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1250, Integer.Sparse.eval]

theorem keyMoment1251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1251) =
      Integer.Sparse.eval keyMomentRow1251 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1251).leftCharge (GramAssembly.key 1251).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2265) := by
    have ha : gramCharges (GramAssembly.key 1251).leftCharge (GramAssembly.key 1251).rightCharge = raw40677 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40677Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40677 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1251).leftCharge (GramAssembly.key 1251).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1251, Integer.Sparse.eval]

theorem keyMoment1252 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1252) =
      Integer.Sparse.eval keyMomentRow1252 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1252).leftCharge (GramAssembly.key 1252).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3808) := by
    have ha : gramCharges (GramAssembly.key 1252).leftCharge (GramAssembly.key 1252).rightCharge = raw40678 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40678Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40678 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1252).leftCharge (GramAssembly.key 1252).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1252, Integer.Sparse.eval]

theorem keyMoment1253 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1253) =
      Integer.Sparse.eval keyMomentRow1253 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1253).leftCharge (GramAssembly.key 1253).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3958) := by
    have ha : gramCharges (GramAssembly.key 1253).leftCharge (GramAssembly.key 1253).rightCharge = raw40679 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40679Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40679 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1253).leftCharge (GramAssembly.key 1253).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1253, Integer.Sparse.eval]

theorem keyMoment1254 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1254) =
      Integer.Sparse.eval keyMomentRow1254 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1254).leftCharge (GramAssembly.key 1254).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3573) := by
    have ha : gramCharges (GramAssembly.key 1254).leftCharge (GramAssembly.key 1254).rightCharge = raw40680 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40680Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40680 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1254).leftCharge (GramAssembly.key 1254).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1254, Integer.Sparse.eval]

theorem keyMoment1255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1255) =
      Integer.Sparse.eval keyMomentRow1255 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1255).leftCharge (GramAssembly.key 1255).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3972) := by
    have ha : gramCharges (GramAssembly.key 1255).leftCharge (GramAssembly.key 1255).rightCharge = raw40681 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40681Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40681 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1255).leftCharge (GramAssembly.key 1255).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1255, Integer.Sparse.eval]

theorem keyMoment1256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1256) =
      Integer.Sparse.eval keyMomentRow1256 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1256).leftCharge (GramAssembly.key 1256).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3880) := by
    have ha : gramCharges (GramAssembly.key 1256).leftCharge (GramAssembly.key 1256).rightCharge = raw40682 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40682Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40682 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1256).leftCharge (GramAssembly.key 1256).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1256, Integer.Sparse.eval]

theorem keyMoment1257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1257) =
      Integer.Sparse.eval keyMomentRow1257 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1257).leftCharge (GramAssembly.key 1257).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3872) := by
    have ha : gramCharges (GramAssembly.key 1257).leftCharge (GramAssembly.key 1257).rightCharge = raw40683 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40683Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40683 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1257).leftCharge (GramAssembly.key 1257).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1257, Integer.Sparse.eval]

theorem keyMoment1258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1258) =
      Integer.Sparse.eval keyMomentRow1258 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1258).leftCharge (GramAssembly.key 1258).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3098) := by
    have ha : gramCharges (GramAssembly.key 1258).leftCharge (GramAssembly.key 1258).rightCharge = raw40684 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40684Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40684 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1258).leftCharge (GramAssembly.key 1258).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1258, Integer.Sparse.eval]

theorem keyMoment1259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1259) =
      Integer.Sparse.eval keyMomentRow1259 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1259).leftCharge (GramAssembly.key 1259).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2278) := by
    have ha : gramCharges (GramAssembly.key 1259).leftCharge (GramAssembly.key 1259).rightCharge = raw40685 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40685Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40685 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1259).leftCharge (GramAssembly.key 1259).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1259, Integer.Sparse.eval]

theorem keyMoment1260 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1260) =
      Integer.Sparse.eval keyMomentRow1260 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1260).leftCharge (GramAssembly.key 1260).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2731) := by
    have ha : gramCharges (GramAssembly.key 1260).leftCharge (GramAssembly.key 1260).rightCharge = raw40686 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40686Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40686 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1260).leftCharge (GramAssembly.key 1260).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1260, Integer.Sparse.eval]

theorem keyMoment1261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1261) =
      Integer.Sparse.eval keyMomentRow1261 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1261).leftCharge (GramAssembly.key 1261).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3044) := by
    have ha : gramCharges (GramAssembly.key 1261).leftCharge (GramAssembly.key 1261).rightCharge = raw40687 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40687Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40687 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1261).leftCharge (GramAssembly.key 1261).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1261, Integer.Sparse.eval]

theorem keyMoment1262 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1262) =
      Integer.Sparse.eval keyMomentRow1262 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1262).leftCharge (GramAssembly.key 1262).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3813) := by
    have ha : gramCharges (GramAssembly.key 1262).leftCharge (GramAssembly.key 1262).rightCharge = raw40688 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40688Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40688 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1262).leftCharge (GramAssembly.key 1262).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1262, Integer.Sparse.eval]

theorem keyMoment1263 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1263) =
      Integer.Sparse.eval keyMomentRow1263 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1263).leftCharge (GramAssembly.key 1263).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3884) := by
    have ha : gramCharges (GramAssembly.key 1263).leftCharge (GramAssembly.key 1263).rightCharge = raw40689 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40689Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40689 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1263).leftCharge (GramAssembly.key 1263).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1263, Integer.Sparse.eval]

theorem keyMoment1264 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1264) =
      Integer.Sparse.eval keyMomentRow1264 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1264).leftCharge (GramAssembly.key 1264).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3506) := by
    have ha : gramCharges (GramAssembly.key 1264).leftCharge (GramAssembly.key 1264).rightCharge = raw40690 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40690Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40690 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1264).leftCharge (GramAssembly.key 1264).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1264, Integer.Sparse.eval]

theorem keyMoment1265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1265) =
      Integer.Sparse.eval keyMomentRow1265 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1265).leftCharge (GramAssembly.key 1265).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3068) := by
    have ha : gramCharges (GramAssembly.key 1265).leftCharge (GramAssembly.key 1265).rightCharge = raw40691 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40691Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40691 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1265).leftCharge (GramAssembly.key 1265).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1265, Integer.Sparse.eval]

theorem keyMoment1266 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1266) =
      Integer.Sparse.eval keyMomentRow1266 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1266).leftCharge (GramAssembly.key 1266).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3840) := by
    have ha : gramCharges (GramAssembly.key 1266).leftCharge (GramAssembly.key 1266).rightCharge = raw40692 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40692Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40692 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1266).leftCharge (GramAssembly.key 1266).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1266, Integer.Sparse.eval]

theorem keyMoment1267 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1267) =
      Integer.Sparse.eval keyMomentRow1267 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1267).leftCharge (GramAssembly.key 1267).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3880) := by
    have ha : gramCharges (GramAssembly.key 1267).leftCharge (GramAssembly.key 1267).rightCharge = raw40693 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40693Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40693 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1267).leftCharge (GramAssembly.key 1267).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1267, Integer.Sparse.eval]

theorem keyMoment1268 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1268) =
      Integer.Sparse.eval keyMomentRow1268 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1268).leftCharge (GramAssembly.key 1268).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3730) := by
    have ha : gramCharges (GramAssembly.key 1268).leftCharge (GramAssembly.key 1268).rightCharge = raw40694 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40694Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40694 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1268).leftCharge (GramAssembly.key 1268).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1268, Integer.Sparse.eval]

theorem keyMoment1269 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1269) =
      Integer.Sparse.eval keyMomentRow1269 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1269).leftCharge (GramAssembly.key 1269).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3826) := by
    have ha : gramCharges (GramAssembly.key 1269).leftCharge (GramAssembly.key 1269).rightCharge = raw40695 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40695Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40695 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1269).leftCharge (GramAssembly.key 1269).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1269, Integer.Sparse.eval]

theorem keyMoment1270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1270) =
      Integer.Sparse.eval keyMomentRow1270 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1270).leftCharge (GramAssembly.key 1270).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3723) := by
    have ha : gramCharges (GramAssembly.key 1270).leftCharge (GramAssembly.key 1270).rightCharge = raw40696 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40696Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40696 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1270).leftCharge (GramAssembly.key 1270).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1270, Integer.Sparse.eval]

theorem keyMoment1271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1271) =
      Integer.Sparse.eval keyMomentRow1271 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1271).leftCharge (GramAssembly.key 1271).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3848) := by
    have ha : gramCharges (GramAssembly.key 1271).leftCharge (GramAssembly.key 1271).rightCharge = raw40697 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40697Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40697 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1271).leftCharge (GramAssembly.key 1271).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1271, Integer.Sparse.eval]

theorem keyMoment1272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1272) =
      Integer.Sparse.eval keyMomentRow1272 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1272).leftCharge (GramAssembly.key 1272).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3909) := by
    have ha : gramCharges (GramAssembly.key 1272).leftCharge (GramAssembly.key 1272).rightCharge = raw40698 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40698Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40698 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1272).leftCharge (GramAssembly.key 1272).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1272, Integer.Sparse.eval]

theorem keyMoment1273 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1273) =
      Integer.Sparse.eval keyMomentRow1273 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1273).leftCharge (GramAssembly.key 1273).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2244) := by
    have ha : gramCharges (GramAssembly.key 1273).leftCharge (GramAssembly.key 1273).rightCharge = raw17178 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw17178Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical17178 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1273).leftCharge (GramAssembly.key 1273).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1273, Integer.Sparse.eval]

theorem keyMoment1274 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1274) =
      Integer.Sparse.eval keyMomentRow1274 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1274).leftCharge (GramAssembly.key 1274).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2709) := by
    have ha : gramCharges (GramAssembly.key 1274).leftCharge (GramAssembly.key 1274).rightCharge = raw40699 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40699Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40699 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1274).leftCharge (GramAssembly.key 1274).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1274, Integer.Sparse.eval]

theorem keyMoment1275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1275) =
      Integer.Sparse.eval keyMomentRow1275 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1275).leftCharge (GramAssembly.key 1275).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3029) := by
    have ha : gramCharges (GramAssembly.key 1275).leftCharge (GramAssembly.key 1275).rightCharge = raw40700 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40700Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40700 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1275).leftCharge (GramAssembly.key 1275).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1275, Integer.Sparse.eval]

theorem keyMoment1276 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1276) =
      Integer.Sparse.eval keyMomentRow1276 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1276).leftCharge (GramAssembly.key 1276).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3800) := by
    have ha : gramCharges (GramAssembly.key 1276).leftCharge (GramAssembly.key 1276).rightCharge = raw40701 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40701Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40701 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1276).leftCharge (GramAssembly.key 1276).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1276, Integer.Sparse.eval]

theorem keyMoment1277 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1277) =
      Integer.Sparse.eval keyMomentRow1277 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1277).leftCharge (GramAssembly.key 1277).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3953) := by
    have ha : gramCharges (GramAssembly.key 1277).leftCharge (GramAssembly.key 1277).rightCharge = raw40702 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40702Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40702 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1277).leftCharge (GramAssembly.key 1277).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1277, Integer.Sparse.eval]

theorem keyMoment1278 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1278) =
      Integer.Sparse.eval keyMomentRow1278 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1278).leftCharge (GramAssembly.key 1278).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3505) := by
    have ha : gramCharges (GramAssembly.key 1278).leftCharge (GramAssembly.key 1278).rightCharge = raw40703 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40703Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40703 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1278).leftCharge (GramAssembly.key 1278).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1278, Integer.Sparse.eval]

theorem keyMoment1279 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1279) =
      Integer.Sparse.eval keyMomentRow1279 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1279).leftCharge (GramAssembly.key 1279).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2952) := by
    have ha : gramCharges (GramAssembly.key 1279).leftCharge (GramAssembly.key 1279).rightCharge = raw40704 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40704Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40704 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1279).leftCharge (GramAssembly.key 1279).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1279, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1248 : keyMomentRows (1248 : Fin 2886) =
    keyMomentRow1248 := by decide +kernel

theorem keyMomentRowsAt1249 : keyMomentRows (1249 : Fin 2886) =
    keyMomentRow1249 := by decide +kernel

theorem keyMomentRowsAt1250 : keyMomentRows (1250 : Fin 2886) =
    keyMomentRow1250 := by decide +kernel

theorem keyMomentRowsAt1251 : keyMomentRows (1251 : Fin 2886) =
    keyMomentRow1251 := by decide +kernel

theorem keyMomentRowsAt1252 : keyMomentRows (1252 : Fin 2886) =
    keyMomentRow1252 := by decide +kernel

theorem keyMomentRowsAt1253 : keyMomentRows (1253 : Fin 2886) =
    keyMomentRow1253 := by decide +kernel

theorem keyMomentRowsAt1254 : keyMomentRows (1254 : Fin 2886) =
    keyMomentRow1254 := by decide +kernel

theorem keyMomentRowsAt1255 : keyMomentRows (1255 : Fin 2886) =
    keyMomentRow1255 := by decide +kernel

theorem keyMomentRowsAt1256 : keyMomentRows (1256 : Fin 2886) =
    keyMomentRow1256 := by decide +kernel

theorem keyMomentRowsAt1257 : keyMomentRows (1257 : Fin 2886) =
    keyMomentRow1257 := by decide +kernel

theorem keyMomentRowsAt1258 : keyMomentRows (1258 : Fin 2886) =
    keyMomentRow1258 := by decide +kernel

theorem keyMomentRowsAt1259 : keyMomentRows (1259 : Fin 2886) =
    keyMomentRow1259 := by decide +kernel

theorem keyMomentRowsAt1260 : keyMomentRows (1260 : Fin 2886) =
    keyMomentRow1260 := by decide +kernel

theorem keyMomentRowsAt1261 : keyMomentRows (1261 : Fin 2886) =
    keyMomentRow1261 := by decide +kernel

theorem keyMomentRowsAt1262 : keyMomentRows (1262 : Fin 2886) =
    keyMomentRow1262 := by decide +kernel

theorem keyMomentRowsAt1263 : keyMomentRows (1263 : Fin 2886) =
    keyMomentRow1263 := by decide +kernel

theorem keyMomentRowsAt1264 : keyMomentRows (1264 : Fin 2886) =
    keyMomentRow1264 := by decide +kernel

theorem keyMomentRowsAt1265 : keyMomentRows (1265 : Fin 2886) =
    keyMomentRow1265 := by decide +kernel

theorem keyMomentRowsAt1266 : keyMomentRows (1266 : Fin 2886) =
    keyMomentRow1266 := by decide +kernel

theorem keyMomentRowsAt1267 : keyMomentRows (1267 : Fin 2886) =
    keyMomentRow1267 := by decide +kernel

theorem keyMomentRowsAt1268 : keyMomentRows (1268 : Fin 2886) =
    keyMomentRow1268 := by decide +kernel

theorem keyMomentRowsAt1269 : keyMomentRows (1269 : Fin 2886) =
    keyMomentRow1269 := by decide +kernel

theorem keyMomentRowsAt1270 : keyMomentRows (1270 : Fin 2886) =
    keyMomentRow1270 := by decide +kernel

theorem keyMomentRowsAt1271 : keyMomentRows (1271 : Fin 2886) =
    keyMomentRow1271 := by decide +kernel

theorem keyMomentRowsAt1272 : keyMomentRows (1272 : Fin 2886) =
    keyMomentRow1272 := by decide +kernel

theorem keyMomentRowsAt1273 : keyMomentRows (1273 : Fin 2886) =
    keyMomentRow1273 := by decide +kernel

theorem keyMomentRowsAt1274 : keyMomentRows (1274 : Fin 2886) =
    keyMomentRow1274 := by decide +kernel

theorem keyMomentRowsAt1275 : keyMomentRows (1275 : Fin 2886) =
    keyMomentRow1275 := by decide +kernel

theorem keyMomentRowsAt1276 : keyMomentRows (1276 : Fin 2886) =
    keyMomentRow1276 := by decide +kernel

theorem keyMomentRowsAt1277 : keyMomentRows (1277 : Fin 2886) =
    keyMomentRow1277 := by decide +kernel

theorem keyMomentRowsAt1278 : keyMomentRows (1278 : Fin 2886) =
    keyMomentRow1278 := by decide +kernel

theorem keyMomentRowsAt1279 : keyMomentRows (1279 : Fin 2886) =
    keyMomentRow1279 := by decide +kernel

theorem keyMomentChunkSound39_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 39) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1248 ∨ k.val = 1249 ∨ k.val = 1250 ∨ k.val = 1251 ∨ k.val = 1252 ∨ k.val = 1253 ∨ k.val = 1254 ∨ k.val = 1255 ∨ k.val = 1256 ∨ k.val = 1257 ∨ k.val = 1258 ∨ k.val = 1259 ∨ k.val = 1260 ∨ k.val = 1261 ∨ k.val = 1262 ∨ k.val = 1263 ∨ k.val = 1264 ∨ k.val = 1265 ∨ k.val = 1266 ∨ k.val = 1267 ∨ k.val = 1268 ∨ k.val = 1269 ∨ k.val = 1270 ∨ k.val = 1271 ∨ k.val = 1272 ∨ k.val = 1273 ∨ k.val = 1274 ∨ k.val = 1275 ∨ k.val = 1276 ∨ k.val = 1277 ∨ k.val = 1278 ∨ k.val = 1279 := by omega
  rcases heq with h1248 | h1249 | h1250 | h1251 | h1252 | h1253 | h1254 | h1255 | h1256 | h1257 | h1258 | h1259 | h1260 | h1261 | h1262 | h1263 | h1264 | h1265 | h1266 | h1267 | h1268 | h1269 | h1270 | h1271 | h1272 | h1273 | h1274 | h1275 | h1276 | h1277 | h1278 | h1279
  · have he : k = (1248 : Fin 2886) := Fin.ext h1248
    subst k
    rw [keyMomentRowsAt1248]
    exact keyMoment1248 B hB
  · have he : k = (1249 : Fin 2886) := Fin.ext h1249
    subst k
    rw [keyMomentRowsAt1249]
    exact keyMoment1249 B hB
  · have he : k = (1250 : Fin 2886) := Fin.ext h1250
    subst k
    rw [keyMomentRowsAt1250]
    exact keyMoment1250 B hB
  · have he : k = (1251 : Fin 2886) := Fin.ext h1251
    subst k
    rw [keyMomentRowsAt1251]
    exact keyMoment1251 B hB
  · have he : k = (1252 : Fin 2886) := Fin.ext h1252
    subst k
    rw [keyMomentRowsAt1252]
    exact keyMoment1252 B hB
  · have he : k = (1253 : Fin 2886) := Fin.ext h1253
    subst k
    rw [keyMomentRowsAt1253]
    exact keyMoment1253 B hB
  · have he : k = (1254 : Fin 2886) := Fin.ext h1254
    subst k
    rw [keyMomentRowsAt1254]
    exact keyMoment1254 B hB
  · have he : k = (1255 : Fin 2886) := Fin.ext h1255
    subst k
    rw [keyMomentRowsAt1255]
    exact keyMoment1255 B hB
  · have he : k = (1256 : Fin 2886) := Fin.ext h1256
    subst k
    rw [keyMomentRowsAt1256]
    exact keyMoment1256 B hB
  · have he : k = (1257 : Fin 2886) := Fin.ext h1257
    subst k
    rw [keyMomentRowsAt1257]
    exact keyMoment1257 B hB
  · have he : k = (1258 : Fin 2886) := Fin.ext h1258
    subst k
    rw [keyMomentRowsAt1258]
    exact keyMoment1258 B hB
  · have he : k = (1259 : Fin 2886) := Fin.ext h1259
    subst k
    rw [keyMomentRowsAt1259]
    exact keyMoment1259 B hB
  · have he : k = (1260 : Fin 2886) := Fin.ext h1260
    subst k
    rw [keyMomentRowsAt1260]
    exact keyMoment1260 B hB
  · have he : k = (1261 : Fin 2886) := Fin.ext h1261
    subst k
    rw [keyMomentRowsAt1261]
    exact keyMoment1261 B hB
  · have he : k = (1262 : Fin 2886) := Fin.ext h1262
    subst k
    rw [keyMomentRowsAt1262]
    exact keyMoment1262 B hB
  · have he : k = (1263 : Fin 2886) := Fin.ext h1263
    subst k
    rw [keyMomentRowsAt1263]
    exact keyMoment1263 B hB
  · have he : k = (1264 : Fin 2886) := Fin.ext h1264
    subst k
    rw [keyMomentRowsAt1264]
    exact keyMoment1264 B hB
  · have he : k = (1265 : Fin 2886) := Fin.ext h1265
    subst k
    rw [keyMomentRowsAt1265]
    exact keyMoment1265 B hB
  · have he : k = (1266 : Fin 2886) := Fin.ext h1266
    subst k
    rw [keyMomentRowsAt1266]
    exact keyMoment1266 B hB
  · have he : k = (1267 : Fin 2886) := Fin.ext h1267
    subst k
    rw [keyMomentRowsAt1267]
    exact keyMoment1267 B hB
  · have he : k = (1268 : Fin 2886) := Fin.ext h1268
    subst k
    rw [keyMomentRowsAt1268]
    exact keyMoment1268 B hB
  · have he : k = (1269 : Fin 2886) := Fin.ext h1269
    subst k
    rw [keyMomentRowsAt1269]
    exact keyMoment1269 B hB
  · have he : k = (1270 : Fin 2886) := Fin.ext h1270
    subst k
    rw [keyMomentRowsAt1270]
    exact keyMoment1270 B hB
  · have he : k = (1271 : Fin 2886) := Fin.ext h1271
    subst k
    rw [keyMomentRowsAt1271]
    exact keyMoment1271 B hB
  · have he : k = (1272 : Fin 2886) := Fin.ext h1272
    subst k
    rw [keyMomentRowsAt1272]
    exact keyMoment1272 B hB
  · have he : k = (1273 : Fin 2886) := Fin.ext h1273
    subst k
    rw [keyMomentRowsAt1273]
    exact keyMoment1273 B hB
  · have he : k = (1274 : Fin 2886) := Fin.ext h1274
    subst k
    rw [keyMomentRowsAt1274]
    exact keyMoment1274 B hB
  · have he : k = (1275 : Fin 2886) := Fin.ext h1275
    subst k
    rw [keyMomentRowsAt1275]
    exact keyMoment1275 B hB
  · have he : k = (1276 : Fin 2886) := Fin.ext h1276
    subst k
    rw [keyMomentRowsAt1276]
    exact keyMoment1276 B hB
  · have he : k = (1277 : Fin 2886) := Fin.ext h1277
    subst k
    rw [keyMomentRowsAt1277]
    exact keyMoment1277 B hB
  · have he : k = (1278 : Fin 2886) := Fin.ext h1278
    subst k
    rw [keyMomentRowsAt1278]
    exact keyMoment1278 B hB
  · have he : k = (1279 : Fin 2886) := Fin.ext h1279
    subst k
    rw [keyMomentRowsAt1279]
    exact keyMoment1279 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound39_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound39_e_oai
