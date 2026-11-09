-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound48_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:57:06.759055+00:00
-- url     : https://prove2.me/submissions/0719262a-6c73-4a68-b5e5-2897fca672fe

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

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical319
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40954 raw40954Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw40954 raw40954Labels = mixedMoment B raw40954step0 raw40954step0Labels := by
      have ha : raw40954step0 = (fun i j => raw40954 (permutation301 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40954step0 raw40954; decide +kernel
      have hl : raw40954step0Labels = raw40954Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40954 raw40954Labels permutation301 permutation6
    _ = mixedMoment B node3782 node3782Labels := by rfl

theorem canonical40955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40955 raw40955Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw40955 raw40955Labels = mixedMoment B raw40955step0 raw40955step0Labels := by
      have ha : raw40955step0 = (fun i j => raw40955 (permutation302 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40955step0 raw40955; decide +kernel
      have hl : raw40955step0Labels = raw40955Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40955 raw40955Labels permutation302 permutation6
    _ = mixedMoment B node3801 node3801Labels := by rfl

theorem canonical40956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40956 raw40956Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw40956 raw40956Labels = mixedMoment B raw40956step0 raw40956step0Labels := by
      have ha : raw40956step0 = (fun i j => raw40956 (permutation450 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40956step0 raw40956; decide +kernel
      have hl : raw40956step0Labels = raw40956Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40956 raw40956Labels permutation450 permutation6
    mixedMoment B raw40956step0 raw40956step0Labels = mixedMoment B raw40956step1 raw40956step1Labels := by
      have ha : raw40956step1 = -raw40956step0 := by apply Matrix.ext; change ∀ i j, raw40956step1 i j = -(raw40956step0 i j); unfold raw40956step1 raw40956step0; decide +kernel
      have hl : raw40956step1Labels = raw40956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3719 node3719Labels := by rfl

theorem canonical40957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40957 raw40957Labels = mixedMoment B node1802 node1802Labels := by
  calc
    mixedMoment B raw40957 raw40957Labels = mixedMoment B raw40957step0 raw40957step0Labels := by
      have ha : raw40957step0 = (fun i j => raw40957 (permutation447 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40957step0 raw40957; decide +kernel
      have hl : raw40957step0Labels = raw40957Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40957 raw40957Labels permutation447 permutation6
    mixedMoment B raw40957step0 raw40957step0Labels = mixedMoment B raw40957step1 raw40957step1Labels := by
      have ha : raw40957step1 = -raw40957step0 := by apply Matrix.ext; change ∀ i j, raw40957step1 i j = -(raw40957step0 i j); unfold raw40957step1 raw40957step0; decide +kernel
      have hl : raw40957step1Labels = raw40957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1802 node1802Labels := by rfl

theorem canonical40958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40958 raw40958Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw40958 raw40958Labels = mixedMoment B raw40958step0 raw40958step0Labels := by
      have hz : ∀ j, raw40958 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40958step0 = (fun i j => raw40958 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40958step0 raw40958; decide +kernel
      have hl : raw40958step0Labels = raw40958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40958 raw40958Labels permutation434 hz
    mixedMoment B raw40958step0 raw40958step0Labels = mixedMoment B raw40958step1 raw40958step1Labels := by
      have hz : ∀ j, raw40958step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40958step1 = (fun i j => raw40958step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40958step1 raw40958step0; decide +kernel
      have hl : raw40958step1Labels = raw40958step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40958step0 raw40958step0Labels permutation80 hz
    mixedMoment B raw40958step1 raw40958step1Labels = mixedMoment B raw40958step2 raw40958step2Labels := by
      have ha : raw40958step2 = (fun i j => raw40958step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40958step2 raw40958step1; decide +kernel
      have hl : raw40958step2Labels = raw40958step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40958step1 raw40958step1Labels permutation20 permutation6
    mixedMoment B raw40958step2 raw40958step2Labels = mixedMoment B raw40958step3 raw40958step3Labels := by
      have ha : raw40958step3 = -raw40958step2 := by apply Matrix.ext; change ∀ i j, raw40958step3 i j = -(raw40958step2 i j); unfold raw40958step3 raw40958step2; decide +kernel
      have hl : raw40958step3Labels = raw40958step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1819 node1819Labels := by rfl

theorem canonical40959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40959 raw40959Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw40959 raw40959Labels = mixedMoment B raw40959step0 raw40959step0Labels := by
      have hz : ∀ j, raw40959 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40959step0 = (fun i j => raw40959 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40959step0 raw40959; decide +kernel
      have hl : raw40959step0Labels = raw40959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40959 raw40959Labels permutation434 hz
    mixedMoment B raw40959step0 raw40959step0Labels = mixedMoment B raw40959step1 raw40959step1Labels := by
      have hz : ∀ j, raw40959step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40959step1 = (fun i j => raw40959step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40959step1 raw40959step0; decide +kernel
      have hl : raw40959step1Labels = raw40959step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40959step0 raw40959step0Labels permutation80 hz
    mixedMoment B raw40959step1 raw40959step1Labels = mixedMoment B raw40959step2 raw40959step2Labels := by
      have ha : raw40959step2 = (fun i j => raw40959step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40959step2 raw40959step1; decide +kernel
      have hl : raw40959step2Labels = raw40959step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40959step1 raw40959step1Labels permutation27 permutation6
    mixedMoment B raw40959step2 raw40959step2Labels = mixedMoment B raw40959step3 raw40959step3Labels := by
      have ha : raw40959step3 = -raw40959step2 := by apply Matrix.ext; change ∀ i j, raw40959step3 i j = -(raw40959step2 i j); unfold raw40959step3 raw40959step2; decide +kernel
      have hl : raw40959step3Labels = raw40959step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3397 node3397Labels := by rfl

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

theorem canonical40960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40960 raw40960Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw40960 raw40960Labels = mixedMoment B raw40960step0 raw40960step0Labels := by
      have hz : ∀ j, raw40960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40960step0 = (fun i j => raw40960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40960step0 raw40960; decide +kernel
      have hl : raw40960step0Labels = raw40960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40960 raw40960Labels permutation346 hz
    mixedMoment B raw40960step0 raw40960step0Labels = mixedMoment B raw40960step1 raw40960step1Labels := by
      have ha : raw40960step1 = (fun i j => raw40960step0 (permutation136 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40960step1 raw40960step0; decide +kernel
      have hl : raw40960step1Labels = raw40960step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40960step0 raw40960step0Labels permutation136 permutation6
    _ = mixedMoment B node2817 node2817Labels := by rfl

theorem canonical40961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40961 raw40961Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw40961 raw40961Labels = mixedMoment B raw40961step0 raw40961step0Labels := by
      have hz : ∀ j, raw40961 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40961step0 = (fun i j => raw40961 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40961step0 raw40961; decide +kernel
      have hl : raw40961step0Labels = raw40961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40961 raw40961Labels permutation346 hz
    mixedMoment B raw40961step0 raw40961step0Labels = mixedMoment B raw40961step1 raw40961step1Labels := by
      have ha : raw40961step1 = (fun i j => raw40961step0 (permutation71 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40961step1 raw40961step0; decide +kernel
      have hl : raw40961step1Labels = raw40961step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40961step0 raw40961step0Labels permutation71 permutation6
    _ = mixedMoment B node3706 node3706Labels := by rfl

theorem canonical40962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40962 raw40962Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw40962 raw40962Labels = mixedMoment B raw40962step0 raw40962step0Labels := by
      have hz : ∀ j, raw40962 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40962step0 = (fun i j => raw40962 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40962step0 raw40962; decide +kernel
      have hl : raw40962step0Labels = raw40962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40962 raw40962Labels permutation346 hz
    mixedMoment B raw40962step0 raw40962step0Labels = mixedMoment B raw40962step1 raw40962step1Labels := by
      have ha : raw40962step1 = (fun i j => raw40962step0 (permutation72 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40962step1 raw40962step0; decide +kernel
      have hl : raw40962step1Labels = raw40962step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40962step0 raw40962step0Labels permutation72 permutation6
    _ = mixedMoment B node3693 node3693Labels := by rfl

theorem canonical40963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40963 raw40963Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw40963 raw40963Labels = mixedMoment B raw40963step0 raw40963step0Labels := by
      have hz : ∀ j, raw40963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40963step0 = (fun i j => raw40963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40963step0 raw40963; decide +kernel
      have hl : raw40963step0Labels = raw40963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40963 raw40963Labels permutation346 hz
    mixedMoment B raw40963step0 raw40963step0Labels = mixedMoment B raw40963step1 raw40963step1Labels := by
      have ha : raw40963step1 = (fun i j => raw40963step0 (permutation85 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40963step1 raw40963step0; decide +kernel
      have hl : raw40963step1Labels = raw40963step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40963step0 raw40963step0Labels permutation85 permutation6
    mixedMoment B raw40963step1 raw40963step1Labels = mixedMoment B raw40963step2 raw40963step2Labels := by
      have ha : raw40963step2 = -raw40963step1 := by apply Matrix.ext; change ∀ i j, raw40963step2 i j = -(raw40963step1 i j); unfold raw40963step2 raw40963step1; decide +kernel
      have hl : raw40963step2Labels = raw40963step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1810 node1810Labels := by rfl

theorem canonical40964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40964 raw40964Labels = mixedMoment B node2814 node2814Labels := by
  calc
    mixedMoment B raw40964 raw40964Labels = mixedMoment B raw40964step0 raw40964step0Labels := by
      have ha : raw40964step0 = (fun i j => raw40964 (permutation609 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40964step0 raw40964; decide +kernel
      have hl : raw40964step0Labels = raw40964Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40964 raw40964Labels permutation609 permutation6
    _ = mixedMoment B node2814 node2814Labels := by rfl

theorem canonical40965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40965 raw40965Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw40965 raw40965Labels = mixedMoment B raw40965step0 raw40965step0Labels := by
      have ha : raw40965step0 = (fun i j => raw40965 (permutation332 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40965step0 raw40965; decide +kernel
      have hl : raw40965step0Labels = raw40965Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40965 raw40965Labels permutation332 permutation6
    _ = mixedMoment B node3692 node3692Labels := by rfl

theorem canonical40966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40966 raw40966Labels = mixedMoment B node3671 node3671Labels := by
  calc
    mixedMoment B raw40966 raw40966Labels = mixedMoment B raw40966step0 raw40966step0Labels := by
      have ha : raw40966step0 = (fun i j => raw40966 (permutation331 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40966step0 raw40966; decide +kernel
      have hl : raw40966step0Labels = raw40966Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40966 raw40966Labels permutation331 permutation6
    _ = mixedMoment B node3671 node3671Labels := by rfl

theorem canonical40967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40967 raw40967Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw40967 raw40967Labels = mixedMoment B raw40967step0 raw40967step0Labels := by
      have hz : ∀ j, raw40967 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40967step0 = (fun i j => raw40967 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40967step0 raw40967; decide +kernel
      have hl : raw40967step0Labels = raw40967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40967 raw40967Labels permutation520 hz
    mixedMoment B raw40967step0 raw40967step0Labels = mixedMoment B raw40967step1 raw40967step1Labels := by
      have ha : raw40967step1 = (fun i j => raw40967step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40967step1 raw40967step0; decide +kernel
      have hl : raw40967step1Labels = raw40967step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40967step0 raw40967step0Labels permutation137 permutation3
    mixedMoment B raw40967step1 raw40967step1Labels = mixedMoment B raw40967step2 raw40967step2Labels := by
      have ha : raw40967step2 = -raw40967step1 := by apply Matrix.ext; change ∀ i j, raw40967step2 i j = -(raw40967step1 i j); unfold raw40967step2 raw40967step1; decide +kernel
      have hl : raw40967step2Labels = raw40967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3619 node3619Labels := by rfl

theorem canonical40968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40968 raw40968Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw40968 raw40968Labels = mixedMoment B raw40968step0 raw40968step0Labels := by
      have ha : raw40968step0 = (fun i j => raw40968 (permutation674 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40968step0 raw40968; decide +kernel
      have hl : raw40968step0Labels = raw40968Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40968 raw40968Labels permutation674 permutation3
    mixedMoment B raw40968step0 raw40968step0Labels = mixedMoment B raw40968step1 raw40968step1Labels := by
      have ha : raw40968step1 = -raw40968step0 := by apply Matrix.ext; change ∀ i j, raw40968step1 i j = -(raw40968step0 i j); unfold raw40968step1 raw40968step0; decide +kernel
      have hl : raw40968step1Labels = raw40968step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3899 node3899Labels := by rfl

theorem canonical40969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40969 raw40969Labels = mixedMoment B node3731 node3731Labels := by
  calc
    mixedMoment B raw40969 raw40969Labels = mixedMoment B raw40969step0 raw40969step0Labels := by
      have ha : raw40969step0 = (fun i j => raw40969 (permutation526 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40969step0 raw40969; decide +kernel
      have hl : raw40969step0Labels = raw40969Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40969 raw40969Labels permutation526 permutation6
    mixedMoment B raw40969step0 raw40969step0Labels = mixedMoment B raw40969step1 raw40969step1Labels := by
      have ha : raw40969step1 = -raw40969step0 := by apply Matrix.ext; change ∀ i j, raw40969step1 i j = -(raw40969step0 i j); unfold raw40969step1 raw40969step0; decide +kernel
      have hl : raw40969step1Labels = raw40969step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3731 node3731Labels := by rfl

theorem canonical40970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40970 raw40970Labels = mixedMoment B node1811 node1811Labels := by
  calc
    mixedMoment B raw40970 raw40970Labels = mixedMoment B raw40970step0 raw40970step0Labels := by
      have ha : raw40970step0 = (fun i j => raw40970 (permutation520 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40970step0 raw40970; decide +kernel
      have hl : raw40970step0Labels = raw40970Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40970 raw40970Labels permutation520 permutation6
    mixedMoment B raw40970step0 raw40970step0Labels = mixedMoment B raw40970step1 raw40970step1Labels := by
      have ha : raw40970step1 = -raw40970step0 := by apply Matrix.ext; change ∀ i j, raw40970step1 i j = -(raw40970step0 i j); unfold raw40970step1 raw40970step0; decide +kernel
      have hl : raw40970step1Labels = raw40970step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1811 node1811Labels := by rfl

theorem canonical40971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40971 raw40971Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw40971 raw40971Labels = mixedMoment B raw40971step0 raw40971step0Labels := by
      have ha : raw40971step0 = (fun i j => raw40971 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40971step0 raw40971; decide +kernel
      have hl : raw40971step0Labels = raw40971Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40971 raw40971Labels permutation260 permutation6
    mixedMoment B raw40971step0 raw40971step0Labels = mixedMoment B raw40971step1 raw40971step1Labels := by
      have ha : raw40971step1 = -raw40971step0 := by apply Matrix.ext; change ∀ i j, raw40971step1 i j = -(raw40971step0 i j); unfold raw40971step1 raw40971step0; decide +kernel
      have hl : raw40971step1Labels = raw40971step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4025 node4025Labels := by rfl

theorem canonical40972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40972 raw40972Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw40972 raw40972Labels = mixedMoment B raw40972step0 raw40972step0Labels := by
      have hz : ∀ j, raw40972 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40972step0 = (fun i j => raw40972 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40972step0 raw40972; decide +kernel
      have hl : raw40972step0Labels = raw40972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40972 raw40972Labels permutation434 hz
    mixedMoment B raw40972step0 raw40972step0Labels = mixedMoment B raw40972step1 raw40972step1Labels := by
      have ha : raw40972step1 = (fun i j => raw40972step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40972step1 raw40972step0; decide +kernel
      have hl : raw40972step1Labels = raw40972step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40972step0 raw40972step0Labels permutation104 permutation6
    mixedMoment B raw40972step1 raw40972step1Labels = mixedMoment B raw40972step2 raw40972step2Labels := by
      have ha : raw40972step2 = -raw40972step1 := by apply Matrix.ext; change ∀ i j, raw40972step2 i j = -(raw40972step1 i j); unfold raw40972step2 raw40972step1; decide +kernel
      have hl : raw40972step2Labels = raw40972step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1812 node1812Labels := by rfl

theorem canonical40973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40973 raw40973Labels = mixedMoment B node2896 node2896Labels := by
  calc
    mixedMoment B raw40973 raw40973Labels = mixedMoment B raw40973step0 raw40973step0Labels := by
      have ha : raw40973step0 = (fun i j => raw40973 (permutation608 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40973step0 raw40973; decide +kernel
      have hl : raw40973step0Labels = raw40973Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40973 raw40973Labels permutation608 permutation6
    _ = mixedMoment B node2896 node2896Labels := by rfl

theorem canonical40974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40974 raw40974Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw40974 raw40974Labels = mixedMoment B raw40974step0 raw40974step0Labels := by
      have ha : raw40974step0 = (fun i j => raw40974 (permutation448 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40974step0 raw40974; decide +kernel
      have hl : raw40974step0Labels = raw40974Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40974 raw40974Labels permutation448 permutation6
    mixedMoment B raw40974step0 raw40974step0Labels = mixedMoment B raw40974step1 raw40974step1Labels := by
      have ha : raw40974step1 = -raw40974step0 := by apply Matrix.ext; change ∀ i j, raw40974step1 i j = -(raw40974step0 i j); unfold raw40974step1 raw40974step0; decide +kernel
      have hl : raw40974step1Labels = raw40974step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3721 node3721Labels := by rfl

theorem canonical40975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40975 raw40975Labels = mixedMoment B node1805 node1805Labels := by
  calc
    mixedMoment B raw40975 raw40975Labels = mixedMoment B raw40975step0 raw40975step0Labels := by
      have ha : raw40975step0 = (fun i j => raw40975 (permutation448 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40975step0 raw40975; decide +kernel
      have hl : raw40975step0Labels = raw40975Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40975 raw40975Labels permutation448 permutation6
    mixedMoment B raw40975step0 raw40975step0Labels = mixedMoment B raw40975step1 raw40975step1Labels := by
      have ha : raw40975step1 = -raw40975step0 := by apply Matrix.ext; change ∀ i j, raw40975step1 i j = -(raw40975step0 i j); unfold raw40975step1 raw40975step0; decide +kernel
      have hl : raw40975step1Labels = raw40975step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1805 node1805Labels := by rfl

theorem canonical40976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40976 raw40976Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw40976 raw40976Labels = mixedMoment B raw40976step0 raw40976step0Labels := by
      have hz : ∀ j, raw40976 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40976step0 = (fun i j => raw40976 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40976step0 raw40976; decide +kernel
      have hl : raw40976step0Labels = raw40976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40976 raw40976Labels permutation434 hz
    mixedMoment B raw40976step0 raw40976step0Labels = mixedMoment B raw40976step1 raw40976step1Labels := by
      have hz : ∀ j, raw40976step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40976step1 = (fun i j => raw40976step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40976step1 raw40976step0; decide +kernel
      have hl : raw40976step1Labels = raw40976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40976step0 raw40976step0Labels permutation80 hz
    mixedMoment B raw40976step1 raw40976step1Labels = mixedMoment B raw40976step2 raw40976step2Labels := by
      have ha : raw40976step2 = (fun i j => raw40976step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40976step2 raw40976step1; decide +kernel
      have hl : raw40976step2Labels = raw40976step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40976step1 raw40976step1Labels permutation28 permutation6
    _ = mixedMoment B node1143 node1143Labels := by rfl

theorem canonical40977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40977 raw40977Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw40977 raw40977Labels = mixedMoment B raw40977step0 raw40977step0Labels := by
      have hz : ∀ j, raw40977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40977step0 = (fun i j => raw40977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40977step0 raw40977; decide +kernel
      have hl : raw40977step0Labels = raw40977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40977 raw40977Labels permutation434 hz
    mixedMoment B raw40977step0 raw40977step0Labels = mixedMoment B raw40977step1 raw40977step1Labels := by
      have hz : ∀ j, raw40977step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40977step1 = (fun i j => raw40977step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40977step1 raw40977step0; decide +kernel
      have hl : raw40977step1Labels = raw40977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40977step0 raw40977step0Labels permutation80 hz
    mixedMoment B raw40977step1 raw40977step1Labels = mixedMoment B raw40977step2 raw40977step2Labels := by
      have ha : raw40977step2 = (fun i j => raw40977step1 (permutation22 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40977step2 raw40977step1; decide +kernel
      have hl : raw40977step2Labels = raw40977step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40977step1 raw40977step1Labels permutation22 permutation6
    _ = mixedMoment B node2522 node2522Labels := by rfl

theorem canonical40978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40978 raw40978Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw40978 raw40978Labels = mixedMoment B raw40978step0 raw40978step0Labels := by
      have hz : ∀ j, raw40978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40978step0 = (fun i j => raw40978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40978step0 raw40978; decide +kernel
      have hl : raw40978step0Labels = raw40978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40978 raw40978Labels permutation346 hz
    mixedMoment B raw40978step0 raw40978step0Labels = mixedMoment B raw40978step1 raw40978step1Labels := by
      have ha : raw40978step1 = (fun i j => raw40978step0 (permutation136 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40978step1 raw40978step0; decide +kernel
      have hl : raw40978step1Labels = raw40978step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40978step0 raw40978step0Labels permutation136 permutation6
    _ = mixedMoment B node1138 node1138Labels := by rfl

theorem canonical40979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40979 raw40979Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw40979 raw40979Labels = mixedMoment B raw40979step0 raw40979step0Labels := by
      have hz : ∀ j, raw40979 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40979step0 = (fun i j => raw40979 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40979step0 raw40979; decide +kernel
      have hl : raw40979step0Labels = raw40979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40979 raw40979Labels permutation346 hz
    mixedMoment B raw40979step0 raw40979step0Labels = mixedMoment B raw40979step1 raw40979step1Labels := by
      have ha : raw40979step1 = (fun i j => raw40979step0 (permutation113 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40979step1 raw40979step0; decide +kernel
      have hl : raw40979step1Labels = raw40979step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40979step0 raw40979step0Labels permutation113 permutation6
    _ = mixedMoment B node2515 node2515Labels := by rfl

theorem canonical40980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40980 raw40980Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw40980 raw40980Labels = mixedMoment B raw40980step0 raw40980step0Labels := by
      have hz : ∀ j, raw40980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40980step0 = (fun i j => raw40980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40980step0 raw40980; decide +kernel
      have hl : raw40980step0Labels = raw40980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40980 raw40980Labels permutation346 hz
    mixedMoment B raw40980step0 raw40980step0Labels = mixedMoment B raw40980step1 raw40980step1Labels := by
      have ha : raw40980step1 = (fun i j => raw40980step0 (permutation114 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40980step1 raw40980step0; decide +kernel
      have hl : raw40980step1Labels = raw40980step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40980step0 raw40980step0Labels permutation114 permutation6
    _ = mixedMoment B node2488 node2488Labels := by rfl

theorem canonical40981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40981 raw40981Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw40981 raw40981Labels = mixedMoment B raw40981step0 raw40981step0Labels := by
      have hz : ∀ j, raw40981 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40981step0 = (fun i j => raw40981 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40981step0 raw40981; decide +kernel
      have hl : raw40981step0Labels = raw40981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40981 raw40981Labels permutation346 hz
    mixedMoment B raw40981step0 raw40981step0Labels = mixedMoment B raw40981step1 raw40981step1Labels := by
      have ha : raw40981step1 = (fun i j => raw40981step0 (permutation84 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40981step1 raw40981step0; decide +kernel
      have hl : raw40981step1Labels = raw40981step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40981step0 raw40981step0Labels permutation84 permutation6
    mixedMoment B raw40981step1 raw40981step1Labels = mixedMoment B raw40981step2 raw40981step2Labels := by
      have ha : raw40981step2 = -raw40981step1 := by apply Matrix.ext; change ∀ i j, raw40981step2 i j = -(raw40981step1 i j); unfold raw40981step2 raw40981step1; decide +kernel
      have hl : raw40981step2Labels = raw40981step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1807 node1807Labels := by rfl

theorem canonical40982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40982 raw40982Labels = mixedMoment B node1815 node1815Labels := by
  calc
    mixedMoment B raw40982 raw40982Labels = mixedMoment B raw40982step0 raw40982step0Labels := by
      have hz : ∀ j, raw40982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40982step0 = (fun i j => raw40982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40982step0 raw40982; decide +kernel
      have hl : raw40982step0Labels = raw40982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40982 raw40982Labels permutation346 hz
    mixedMoment B raw40982step0 raw40982step0Labels = mixedMoment B raw40982step1 raw40982step1Labels := by
      have ha : raw40982step1 = (fun i j => raw40982step0 (permutation80 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40982step1 raw40982step0; decide +kernel
      have hl : raw40982step1Labels = raw40982step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40982step0 raw40982step0Labels permutation80 permutation6
    mixedMoment B raw40982step1 raw40982step1Labels = mixedMoment B raw40982step2 raw40982step2Labels := by
      have ha : raw40982step2 = -raw40982step1 := by apply Matrix.ext; change ∀ i j, raw40982step2 i j = -(raw40982step1 i j); unfold raw40982step2 raw40982step1; decide +kernel
      have hl : raw40982step2Labels = raw40982step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1815 node1815Labels := by rfl

theorem canonical40983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40983 raw40983Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw40983 raw40983Labels = mixedMoment B raw40983step0 raw40983step0Labels := by
      have ha : raw40983step0 = (fun i j => raw40983 (permutation540 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40983step0 raw40983; decide +kernel
      have hl : raw40983step0Labels = raw40983Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40983 raw40983Labels permutation540 permutation6
    _ = mixedMoment B node2483 node2483Labels := by rfl

theorem canonical40984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40984 raw40984Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw40984 raw40984Labels = mixedMoment B raw40984step0 raw40984step0Labels := by
      have ha : raw40984step0 = (fun i j => raw40984 (permutation539 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40984step0 raw40984; decide +kernel
      have hl : raw40984step0Labels = raw40984Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40984 raw40984Labels permutation539 permutation6
    _ = mixedMoment B node2431 node2431Labels := by rfl

theorem canonical40985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40985 raw40985Labels = mixedMoment B node3709 node3709Labels := by
  calc
    mixedMoment B raw40985 raw40985Labels = mixedMoment B raw40985step0 raw40985step0Labels := by
      have ha : raw40985step0 = (fun i j => raw40985 (permutation440 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40985step0 raw40985; decide +kernel
      have hl : raw40985step0Labels = raw40985Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40985 raw40985Labels permutation440 permutation6
    mixedMoment B raw40985step0 raw40985step0Labels = mixedMoment B raw40985step1 raw40985step1Labels := by
      have ha : raw40985step1 = -raw40985step0 := by apply Matrix.ext; change ∀ i j, raw40985step1 i j = -(raw40985step0 i j); unfold raw40985step1 raw40985step0; decide +kernel
      have hl : raw40985step1Labels = raw40985step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3709 node3709Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1536 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1536) =
      Integer.Sparse.eval keyMomentRow1536 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1536).leftCharge (GramAssembly.key 1536).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3782) := by
    have ha : gramCharges (GramAssembly.key 1536).leftCharge (GramAssembly.key 1536).rightCharge = raw40954 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40954Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40954 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1536).leftCharge (GramAssembly.key 1536).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1536, Integer.Sparse.eval]

theorem keyMoment1537 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1537) =
      Integer.Sparse.eval keyMomentRow1537 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1537).leftCharge (GramAssembly.key 1537).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3801) := by
    have ha : gramCharges (GramAssembly.key 1537).leftCharge (GramAssembly.key 1537).rightCharge = raw40955 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40955Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40955 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1537).leftCharge (GramAssembly.key 1537).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1537, Integer.Sparse.eval]

theorem keyMoment1538 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1538) =
      Integer.Sparse.eval keyMomentRow1538 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1538).leftCharge (GramAssembly.key 1538).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3719) := by
    have ha : gramCharges (GramAssembly.key 1538).leftCharge (GramAssembly.key 1538).rightCharge = raw40956 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40956Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40956 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1538).leftCharge (GramAssembly.key 1538).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1538, Integer.Sparse.eval]

theorem keyMoment1539 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1539) =
      Integer.Sparse.eval keyMomentRow1539 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1539).leftCharge (GramAssembly.key 1539).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1802) := by
    have ha : gramCharges (GramAssembly.key 1539).leftCharge (GramAssembly.key 1539).rightCharge = raw40957 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40957Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40957 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1539).leftCharge (GramAssembly.key 1539).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1539, Integer.Sparse.eval]

theorem keyMoment1540 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1540) =
      Integer.Sparse.eval keyMomentRow1540 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1540).leftCharge (GramAssembly.key 1540).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1819) := by
    have ha : gramCharges (GramAssembly.key 1540).leftCharge (GramAssembly.key 1540).rightCharge = raw40958 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40958Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40958 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1540).leftCharge (GramAssembly.key 1540).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1540, Integer.Sparse.eval]

theorem keyMoment1541 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1541) =
      Integer.Sparse.eval keyMomentRow1541 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1541).leftCharge (GramAssembly.key 1541).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3397) := by
    have ha : gramCharges (GramAssembly.key 1541).leftCharge (GramAssembly.key 1541).rightCharge = raw40959 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40959Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40959 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1541).leftCharge (GramAssembly.key 1541).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1541, Integer.Sparse.eval]

theorem keyMoment1542 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1542) =
      Integer.Sparse.eval keyMomentRow1542 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1542).leftCharge (GramAssembly.key 1542).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2817) := by
    have ha : gramCharges (GramAssembly.key 1542).leftCharge (GramAssembly.key 1542).rightCharge = raw40960 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40960Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40960 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1542).leftCharge (GramAssembly.key 1542).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1542, Integer.Sparse.eval]

theorem keyMoment1543 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1543) =
      Integer.Sparse.eval keyMomentRow1543 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1543).leftCharge (GramAssembly.key 1543).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3706) := by
    have ha : gramCharges (GramAssembly.key 1543).leftCharge (GramAssembly.key 1543).rightCharge = raw40961 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40961Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40961 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1543).leftCharge (GramAssembly.key 1543).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1543, Integer.Sparse.eval]

theorem keyMoment1544 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1544) =
      Integer.Sparse.eval keyMomentRow1544 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1544).leftCharge (GramAssembly.key 1544).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3693) := by
    have ha : gramCharges (GramAssembly.key 1544).leftCharge (GramAssembly.key 1544).rightCharge = raw40962 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40962Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40962 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1544).leftCharge (GramAssembly.key 1544).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1544, Integer.Sparse.eval]

theorem keyMoment1545 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1545) =
      Integer.Sparse.eval keyMomentRow1545 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1545).leftCharge (GramAssembly.key 1545).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1810) := by
    have ha : gramCharges (GramAssembly.key 1545).leftCharge (GramAssembly.key 1545).rightCharge = raw40963 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40963Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40963 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1545).leftCharge (GramAssembly.key 1545).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1545, Integer.Sparse.eval]

theorem keyMoment1546 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1546) =
      Integer.Sparse.eval keyMomentRow1546 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1546).leftCharge (GramAssembly.key 1546).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2814) := by
    have ha : gramCharges (GramAssembly.key 1546).leftCharge (GramAssembly.key 1546).rightCharge = raw40964 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40964Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40964 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1546).leftCharge (GramAssembly.key 1546).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1546, Integer.Sparse.eval]

theorem keyMoment1547 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1547) =
      Integer.Sparse.eval keyMomentRow1547 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1547).leftCharge (GramAssembly.key 1547).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3692) := by
    have ha : gramCharges (GramAssembly.key 1547).leftCharge (GramAssembly.key 1547).rightCharge = raw40965 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40965Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40965 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1547).leftCharge (GramAssembly.key 1547).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1547, Integer.Sparse.eval]

theorem keyMoment1548 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1548) =
      Integer.Sparse.eval keyMomentRow1548 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1548).leftCharge (GramAssembly.key 1548).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3671) := by
    have ha : gramCharges (GramAssembly.key 1548).leftCharge (GramAssembly.key 1548).rightCharge = raw40966 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40966Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40966 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1548).leftCharge (GramAssembly.key 1548).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1548, Integer.Sparse.eval]

theorem keyMoment1549 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1549) =
      Integer.Sparse.eval keyMomentRow1549 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1549).leftCharge (GramAssembly.key 1549).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3619) := by
    have ha : gramCharges (GramAssembly.key 1549).leftCharge (GramAssembly.key 1549).rightCharge = raw40967 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40967Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40967 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1549).leftCharge (GramAssembly.key 1549).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1549, Integer.Sparse.eval]

theorem keyMoment1550 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1550) =
      Integer.Sparse.eval keyMomentRow1550 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1550).leftCharge (GramAssembly.key 1550).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3899) := by
    have ha : gramCharges (GramAssembly.key 1550).leftCharge (GramAssembly.key 1550).rightCharge = raw40968 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40968Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40968 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1550).leftCharge (GramAssembly.key 1550).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1550, Integer.Sparse.eval]

theorem keyMoment1551 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1551) =
      Integer.Sparse.eval keyMomentRow1551 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1551).leftCharge (GramAssembly.key 1551).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3731) := by
    have ha : gramCharges (GramAssembly.key 1551).leftCharge (GramAssembly.key 1551).rightCharge = raw40969 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40969Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40969 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1551).leftCharge (GramAssembly.key 1551).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1551, Integer.Sparse.eval]

theorem keyMoment1552 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1552) =
      Integer.Sparse.eval keyMomentRow1552 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1552).leftCharge (GramAssembly.key 1552).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1811) := by
    have ha : gramCharges (GramAssembly.key 1552).leftCharge (GramAssembly.key 1552).rightCharge = raw40970 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40970Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40970 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1552).leftCharge (GramAssembly.key 1552).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1552, Integer.Sparse.eval]

theorem keyMoment1553 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1553) =
      Integer.Sparse.eval keyMomentRow1553 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1553).leftCharge (GramAssembly.key 1553).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4025) := by
    have ha : gramCharges (GramAssembly.key 1553).leftCharge (GramAssembly.key 1553).rightCharge = raw40971 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40971Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40971 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1553).leftCharge (GramAssembly.key 1553).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1553, Integer.Sparse.eval]

theorem keyMoment1554 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1554) =
      Integer.Sparse.eval keyMomentRow1554 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1554).leftCharge (GramAssembly.key 1554).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1812) := by
    have ha : gramCharges (GramAssembly.key 1554).leftCharge (GramAssembly.key 1554).rightCharge = raw40972 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40972Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40972 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1554).leftCharge (GramAssembly.key 1554).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1554, Integer.Sparse.eval]

theorem keyMoment1555 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1555) =
      Integer.Sparse.eval keyMomentRow1555 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1555).leftCharge (GramAssembly.key 1555).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2896) := by
    have ha : gramCharges (GramAssembly.key 1555).leftCharge (GramAssembly.key 1555).rightCharge = raw40973 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40973Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40973 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1555).leftCharge (GramAssembly.key 1555).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1555, Integer.Sparse.eval]

theorem keyMoment1556 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1556) =
      Integer.Sparse.eval keyMomentRow1556 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1556).leftCharge (GramAssembly.key 1556).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3721) := by
    have ha : gramCharges (GramAssembly.key 1556).leftCharge (GramAssembly.key 1556).rightCharge = raw40974 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40974Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40974 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1556).leftCharge (GramAssembly.key 1556).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1556, Integer.Sparse.eval]

theorem keyMoment1557 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1557) =
      Integer.Sparse.eval keyMomentRow1557 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1557).leftCharge (GramAssembly.key 1557).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1805) := by
    have ha : gramCharges (GramAssembly.key 1557).leftCharge (GramAssembly.key 1557).rightCharge = raw40975 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40975Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40975 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1557).leftCharge (GramAssembly.key 1557).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1557, Integer.Sparse.eval]

theorem keyMoment1558 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1558) =
      Integer.Sparse.eval keyMomentRow1558 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1558).leftCharge (GramAssembly.key 1558).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1143) := by
    have ha : gramCharges (GramAssembly.key 1558).leftCharge (GramAssembly.key 1558).rightCharge = raw40976 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40976Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40976 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1558).leftCharge (GramAssembly.key 1558).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1558, Integer.Sparse.eval]

theorem keyMoment1559 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1559) =
      Integer.Sparse.eval keyMomentRow1559 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1559).leftCharge (GramAssembly.key 1559).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2522) := by
    have ha : gramCharges (GramAssembly.key 1559).leftCharge (GramAssembly.key 1559).rightCharge = raw40977 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40977Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40977 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1559).leftCharge (GramAssembly.key 1559).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1559, Integer.Sparse.eval]

theorem keyMoment1560 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1560) =
      Integer.Sparse.eval keyMomentRow1560 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1560).leftCharge (GramAssembly.key 1560).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1138) := by
    have ha : gramCharges (GramAssembly.key 1560).leftCharge (GramAssembly.key 1560).rightCharge = raw40978 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40978Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40978 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1560).leftCharge (GramAssembly.key 1560).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1560, Integer.Sparse.eval]

theorem keyMoment1561 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1561) =
      Integer.Sparse.eval keyMomentRow1561 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1561).leftCharge (GramAssembly.key 1561).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2515) := by
    have ha : gramCharges (GramAssembly.key 1561).leftCharge (GramAssembly.key 1561).rightCharge = raw40979 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40979Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40979 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1561).leftCharge (GramAssembly.key 1561).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1561, Integer.Sparse.eval]

theorem keyMoment1562 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1562) =
      Integer.Sparse.eval keyMomentRow1562 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1562).leftCharge (GramAssembly.key 1562).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2488) := by
    have ha : gramCharges (GramAssembly.key 1562).leftCharge (GramAssembly.key 1562).rightCharge = raw40980 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40980Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40980 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1562).leftCharge (GramAssembly.key 1562).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1562, Integer.Sparse.eval]

theorem keyMoment1563 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1563) =
      Integer.Sparse.eval keyMomentRow1563 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1563).leftCharge (GramAssembly.key 1563).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1807) := by
    have ha : gramCharges (GramAssembly.key 1563).leftCharge (GramAssembly.key 1563).rightCharge = raw40981 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40981Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40981 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1563).leftCharge (GramAssembly.key 1563).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1563, Integer.Sparse.eval]

theorem keyMoment1564 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1564) =
      Integer.Sparse.eval keyMomentRow1564 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1564).leftCharge (GramAssembly.key 1564).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1815) := by
    have ha : gramCharges (GramAssembly.key 1564).leftCharge (GramAssembly.key 1564).rightCharge = raw40982 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40982Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40982 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1564).leftCharge (GramAssembly.key 1564).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1564, Integer.Sparse.eval]

theorem keyMoment1565 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1565) =
      Integer.Sparse.eval keyMomentRow1565 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1565).leftCharge (GramAssembly.key 1565).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2483) := by
    have ha : gramCharges (GramAssembly.key 1565).leftCharge (GramAssembly.key 1565).rightCharge = raw40983 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40983Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40983 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1565).leftCharge (GramAssembly.key 1565).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1565, Integer.Sparse.eval]

theorem keyMoment1566 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1566) =
      Integer.Sparse.eval keyMomentRow1566 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1566).leftCharge (GramAssembly.key 1566).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2431) := by
    have ha : gramCharges (GramAssembly.key 1566).leftCharge (GramAssembly.key 1566).rightCharge = raw40984 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40984Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40984 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1566).leftCharge (GramAssembly.key 1566).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1566, Integer.Sparse.eval]

theorem keyMoment1567 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1567) =
      Integer.Sparse.eval keyMomentRow1567 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1567).leftCharge (GramAssembly.key 1567).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3709) := by
    have ha : gramCharges (GramAssembly.key 1567).leftCharge (GramAssembly.key 1567).rightCharge = raw40985 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40985Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40985 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1567).leftCharge (GramAssembly.key 1567).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1567, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1536 : keyMomentRows (1536 : Fin 2886) =
    keyMomentRow1536 := by decide +kernel

theorem keyMomentRowsAt1537 : keyMomentRows (1537 : Fin 2886) =
    keyMomentRow1537 := by decide +kernel

theorem keyMomentRowsAt1538 : keyMomentRows (1538 : Fin 2886) =
    keyMomentRow1538 := by decide +kernel

theorem keyMomentRowsAt1539 : keyMomentRows (1539 : Fin 2886) =
    keyMomentRow1539 := by decide +kernel

theorem keyMomentRowsAt1540 : keyMomentRows (1540 : Fin 2886) =
    keyMomentRow1540 := by decide +kernel

theorem keyMomentRowsAt1541 : keyMomentRows (1541 : Fin 2886) =
    keyMomentRow1541 := by decide +kernel

theorem keyMomentRowsAt1542 : keyMomentRows (1542 : Fin 2886) =
    keyMomentRow1542 := by decide +kernel

theorem keyMomentRowsAt1543 : keyMomentRows (1543 : Fin 2886) =
    keyMomentRow1543 := by decide +kernel

theorem keyMomentRowsAt1544 : keyMomentRows (1544 : Fin 2886) =
    keyMomentRow1544 := by decide +kernel

theorem keyMomentRowsAt1545 : keyMomentRows (1545 : Fin 2886) =
    keyMomentRow1545 := by decide +kernel

theorem keyMomentRowsAt1546 : keyMomentRows (1546 : Fin 2886) =
    keyMomentRow1546 := by decide +kernel

theorem keyMomentRowsAt1547 : keyMomentRows (1547 : Fin 2886) =
    keyMomentRow1547 := by decide +kernel

theorem keyMomentRowsAt1548 : keyMomentRows (1548 : Fin 2886) =
    keyMomentRow1548 := by decide +kernel

theorem keyMomentRowsAt1549 : keyMomentRows (1549 : Fin 2886) =
    keyMomentRow1549 := by decide +kernel

theorem keyMomentRowsAt1550 : keyMomentRows (1550 : Fin 2886) =
    keyMomentRow1550 := by decide +kernel

theorem keyMomentRowsAt1551 : keyMomentRows (1551 : Fin 2886) =
    keyMomentRow1551 := by decide +kernel

theorem keyMomentRowsAt1552 : keyMomentRows (1552 : Fin 2886) =
    keyMomentRow1552 := by decide +kernel

theorem keyMomentRowsAt1553 : keyMomentRows (1553 : Fin 2886) =
    keyMomentRow1553 := by decide +kernel

theorem keyMomentRowsAt1554 : keyMomentRows (1554 : Fin 2886) =
    keyMomentRow1554 := by decide +kernel

theorem keyMomentRowsAt1555 : keyMomentRows (1555 : Fin 2886) =
    keyMomentRow1555 := by decide +kernel

theorem keyMomentRowsAt1556 : keyMomentRows (1556 : Fin 2886) =
    keyMomentRow1556 := by decide +kernel

theorem keyMomentRowsAt1557 : keyMomentRows (1557 : Fin 2886) =
    keyMomentRow1557 := by decide +kernel

theorem keyMomentRowsAt1558 : keyMomentRows (1558 : Fin 2886) =
    keyMomentRow1558 := by decide +kernel

theorem keyMomentRowsAt1559 : keyMomentRows (1559 : Fin 2886) =
    keyMomentRow1559 := by decide +kernel

theorem keyMomentRowsAt1560 : keyMomentRows (1560 : Fin 2886) =
    keyMomentRow1560 := by decide +kernel

theorem keyMomentRowsAt1561 : keyMomentRows (1561 : Fin 2886) =
    keyMomentRow1561 := by decide +kernel

theorem keyMomentRowsAt1562 : keyMomentRows (1562 : Fin 2886) =
    keyMomentRow1562 := by decide +kernel

theorem keyMomentRowsAt1563 : keyMomentRows (1563 : Fin 2886) =
    keyMomentRow1563 := by decide +kernel

theorem keyMomentRowsAt1564 : keyMomentRows (1564 : Fin 2886) =
    keyMomentRow1564 := by decide +kernel

theorem keyMomentRowsAt1565 : keyMomentRows (1565 : Fin 2886) =
    keyMomentRow1565 := by decide +kernel

theorem keyMomentRowsAt1566 : keyMomentRows (1566 : Fin 2886) =
    keyMomentRow1566 := by decide +kernel

theorem keyMomentRowsAt1567 : keyMomentRows (1567 : Fin 2886) =
    keyMomentRow1567 := by decide +kernel

theorem keyMomentChunkSound48_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 48) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1536 ∨ k.val = 1537 ∨ k.val = 1538 ∨ k.val = 1539 ∨ k.val = 1540 ∨ k.val = 1541 ∨ k.val = 1542 ∨ k.val = 1543 ∨ k.val = 1544 ∨ k.val = 1545 ∨ k.val = 1546 ∨ k.val = 1547 ∨ k.val = 1548 ∨ k.val = 1549 ∨ k.val = 1550 ∨ k.val = 1551 ∨ k.val = 1552 ∨ k.val = 1553 ∨ k.val = 1554 ∨ k.val = 1555 ∨ k.val = 1556 ∨ k.val = 1557 ∨ k.val = 1558 ∨ k.val = 1559 ∨ k.val = 1560 ∨ k.val = 1561 ∨ k.val = 1562 ∨ k.val = 1563 ∨ k.val = 1564 ∨ k.val = 1565 ∨ k.val = 1566 ∨ k.val = 1567 := by omega
  rcases heq with h1536 | h1537 | h1538 | h1539 | h1540 | h1541 | h1542 | h1543 | h1544 | h1545 | h1546 | h1547 | h1548 | h1549 | h1550 | h1551 | h1552 | h1553 | h1554 | h1555 | h1556 | h1557 | h1558 | h1559 | h1560 | h1561 | h1562 | h1563 | h1564 | h1565 | h1566 | h1567
  · have he : k = (1536 : Fin 2886) := Fin.ext h1536
    subst k
    rw [keyMomentRowsAt1536]
    exact keyMoment1536 B hB
  · have he : k = (1537 : Fin 2886) := Fin.ext h1537
    subst k
    rw [keyMomentRowsAt1537]
    exact keyMoment1537 B hB
  · have he : k = (1538 : Fin 2886) := Fin.ext h1538
    subst k
    rw [keyMomentRowsAt1538]
    exact keyMoment1538 B hB
  · have he : k = (1539 : Fin 2886) := Fin.ext h1539
    subst k
    rw [keyMomentRowsAt1539]
    exact keyMoment1539 B hB
  · have he : k = (1540 : Fin 2886) := Fin.ext h1540
    subst k
    rw [keyMomentRowsAt1540]
    exact keyMoment1540 B hB
  · have he : k = (1541 : Fin 2886) := Fin.ext h1541
    subst k
    rw [keyMomentRowsAt1541]
    exact keyMoment1541 B hB
  · have he : k = (1542 : Fin 2886) := Fin.ext h1542
    subst k
    rw [keyMomentRowsAt1542]
    exact keyMoment1542 B hB
  · have he : k = (1543 : Fin 2886) := Fin.ext h1543
    subst k
    rw [keyMomentRowsAt1543]
    exact keyMoment1543 B hB
  · have he : k = (1544 : Fin 2886) := Fin.ext h1544
    subst k
    rw [keyMomentRowsAt1544]
    exact keyMoment1544 B hB
  · have he : k = (1545 : Fin 2886) := Fin.ext h1545
    subst k
    rw [keyMomentRowsAt1545]
    exact keyMoment1545 B hB
  · have he : k = (1546 : Fin 2886) := Fin.ext h1546
    subst k
    rw [keyMomentRowsAt1546]
    exact keyMoment1546 B hB
  · have he : k = (1547 : Fin 2886) := Fin.ext h1547
    subst k
    rw [keyMomentRowsAt1547]
    exact keyMoment1547 B hB
  · have he : k = (1548 : Fin 2886) := Fin.ext h1548
    subst k
    rw [keyMomentRowsAt1548]
    exact keyMoment1548 B hB
  · have he : k = (1549 : Fin 2886) := Fin.ext h1549
    subst k
    rw [keyMomentRowsAt1549]
    exact keyMoment1549 B hB
  · have he : k = (1550 : Fin 2886) := Fin.ext h1550
    subst k
    rw [keyMomentRowsAt1550]
    exact keyMoment1550 B hB
  · have he : k = (1551 : Fin 2886) := Fin.ext h1551
    subst k
    rw [keyMomentRowsAt1551]
    exact keyMoment1551 B hB
  · have he : k = (1552 : Fin 2886) := Fin.ext h1552
    subst k
    rw [keyMomentRowsAt1552]
    exact keyMoment1552 B hB
  · have he : k = (1553 : Fin 2886) := Fin.ext h1553
    subst k
    rw [keyMomentRowsAt1553]
    exact keyMoment1553 B hB
  · have he : k = (1554 : Fin 2886) := Fin.ext h1554
    subst k
    rw [keyMomentRowsAt1554]
    exact keyMoment1554 B hB
  · have he : k = (1555 : Fin 2886) := Fin.ext h1555
    subst k
    rw [keyMomentRowsAt1555]
    exact keyMoment1555 B hB
  · have he : k = (1556 : Fin 2886) := Fin.ext h1556
    subst k
    rw [keyMomentRowsAt1556]
    exact keyMoment1556 B hB
  · have he : k = (1557 : Fin 2886) := Fin.ext h1557
    subst k
    rw [keyMomentRowsAt1557]
    exact keyMoment1557 B hB
  · have he : k = (1558 : Fin 2886) := Fin.ext h1558
    subst k
    rw [keyMomentRowsAt1558]
    exact keyMoment1558 B hB
  · have he : k = (1559 : Fin 2886) := Fin.ext h1559
    subst k
    rw [keyMomentRowsAt1559]
    exact keyMoment1559 B hB
  · have he : k = (1560 : Fin 2886) := Fin.ext h1560
    subst k
    rw [keyMomentRowsAt1560]
    exact keyMoment1560 B hB
  · have he : k = (1561 : Fin 2886) := Fin.ext h1561
    subst k
    rw [keyMomentRowsAt1561]
    exact keyMoment1561 B hB
  · have he : k = (1562 : Fin 2886) := Fin.ext h1562
    subst k
    rw [keyMomentRowsAt1562]
    exact keyMoment1562 B hB
  · have he : k = (1563 : Fin 2886) := Fin.ext h1563
    subst k
    rw [keyMomentRowsAt1563]
    exact keyMoment1563 B hB
  · have he : k = (1564 : Fin 2886) := Fin.ext h1564
    subst k
    rw [keyMomentRowsAt1564]
    exact keyMoment1564 B hB
  · have he : k = (1565 : Fin 2886) := Fin.ext h1565
    subst k
    rw [keyMomentRowsAt1565]
    exact keyMoment1565 B hB
  · have he : k = (1566 : Fin 2886) := Fin.ext h1566
    subst k
    rw [keyMomentRowsAt1566]
    exact keyMoment1566 B hB
  · have he : k = (1567 : Fin 2886) := Fin.ext h1567
    subst k
    rw [keyMomentRowsAt1567]
    exact keyMoment1567 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound48_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound48_e_oai
