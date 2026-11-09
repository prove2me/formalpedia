-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound23_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:48:56.749884+00:00
-- url     : https://prove2.me/submissions/4e8e16aa-dd48-4c94-829b-88d6aaedc754

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E110
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical298
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical38154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38154 raw38154Labels = mixedMoment B node531 node531Labels := by
  calc
    _ = mixedMoment B node531 node531Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical40184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40184 raw40184Labels = mixedMoment B node407 node407Labels := by
  calc
    mixedMoment B raw40184 raw40184Labels = mixedMoment B raw40184step0 raw40184step0Labels := by
      have hz : ∀ j, raw40184 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40184step0 = (fun i j => raw40184 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40184step0 raw40184; decide +kernel
      have hl : raw40184step0Labels = raw40184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40184 raw40184Labels permutation520 hz
    mixedMoment B raw40184step0 raw40184step0Labels = mixedMoment B raw40184step1 raw40184step1Labels := by
      have hz : ∀ j, raw40184step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40184step1 = (fun i j => raw40184step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40184step1 raw40184step0; decide +kernel
      have hl : raw40184step1Labels = raw40184step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40184step0 raw40184step0Labels permutation104 hz
    mixedMoment B raw40184step1 raw40184step1Labels = mixedMoment B raw40184step2 raw40184step2Labels := by
      have hz : ∀ j, raw40184step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40184step2 = (fun i j => raw40184step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40184step2 raw40184step1; decide +kernel
      have hl : raw40184step2Labels = raw40184step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40184step1 raw40184step1Labels permutation20 hz
    mixedMoment B raw40184step2 raw40184step2Labels = mixedMoment B raw40184step3 raw40184step3Labels := by
      have ha : raw40184step3 = (fun i j => raw40184step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40184step3 raw40184step2; decide +kernel
      have hl : raw40184step3Labels = raw40184step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40184step2 raw40184step2Labels permutation4 permutation6
    mixedMoment B raw40184step3 raw40184step3Labels = mixedMoment B raw40184step4 raw40184step4Labels := by
      have ha : raw40184step4 = -raw40184step3 := by apply Matrix.ext; change ∀ i j, raw40184step4 i j = -(raw40184step3 i j); unfold raw40184step4 raw40184step3; decide +kernel
      have hl : raw40184step4Labels = raw40184step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node407 node407Labels := by rfl

theorem canonical40185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40185 raw40185Labels = mixedMoment B node379 node379Labels := by
  calc
    mixedMoment B raw40185 raw40185Labels = mixedMoment B raw40185step0 raw40185step0Labels := by
      have hz : ∀ j, raw40185 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40185step0 = (fun i j => raw40185 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40185step0 raw40185; decide +kernel
      have hl : raw40185step0Labels = raw40185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40185 raw40185Labels permutation434 hz
    mixedMoment B raw40185step0 raw40185step0Labels = mixedMoment B raw40185step1 raw40185step1Labels := by
      have hz : ∀ j, raw40185step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40185step1 = (fun i j => raw40185step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40185step1 raw40185step0; decide +kernel
      have hl : raw40185step1Labels = raw40185step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40185step0 raw40185step0Labels permutation80 hz
    mixedMoment B raw40185step1 raw40185step1Labels = mixedMoment B raw40185step2 raw40185step2Labels := by
      have ha : raw40185step2 = (fun i j => raw40185step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40185step2 raw40185step1; decide +kernel
      have hl : raw40185step2Labels = raw40185step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40185step1 raw40185step1Labels permutation21 permutation6
    _ = mixedMoment B node379 node379Labels := by rfl

theorem canonical40186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40186 raw40186Labels = mixedMoment B node303 node303Labels := by
  calc
    mixedMoment B raw40186 raw40186Labels = mixedMoment B raw40186step0 raw40186step0Labels := by
      have hz : ∀ j, raw40186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40186step0 = (fun i j => raw40186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40186step0 raw40186; decide +kernel
      have hl : raw40186step0Labels = raw40186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40186 raw40186Labels permutation346 hz
    mixedMoment B raw40186step0 raw40186step0Labels = mixedMoment B raw40186step1 raw40186step1Labels := by
      have ha : raw40186step1 = (fun i j => raw40186step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40186step1 raw40186step0; decide +kernel
      have hl : raw40186step1Labels = raw40186step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40186step0 raw40186step0Labels permutation63 permutation6
    mixedMoment B raw40186step1 raw40186step1Labels = mixedMoment B raw40186step2 raw40186step2Labels := by
      have ha : raw40186step2 = -raw40186step1 := by apply Matrix.ext; change ∀ i j, raw40186step2 i j = -(raw40186step1 i j); unfold raw40186step2 raw40186step1; decide +kernel
      have hl : raw40186step2Labels = raw40186step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node303 node303Labels := by rfl

theorem canonical40187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40187 raw40187Labels = mixedMoment B node98 node98Labels := by
  calc
    mixedMoment B raw40187 raw40187Labels = mixedMoment B raw40187step0 raw40187step0Labels := by
      have hz : ∀ j, raw40187 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40187step0 = (fun i j => raw40187 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40187step0 raw40187; decide +kernel
      have hl : raw40187step0Labels = raw40187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40187 raw40187Labels permutation520 hz
    mixedMoment B raw40187step0 raw40187step0Labels = mixedMoment B raw40187step1 raw40187step1Labels := by
      have hz : ∀ j, raw40187step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40187step1 = (fun i j => raw40187step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40187step1 raw40187step0; decide +kernel
      have hl : raw40187step1Labels = raw40187step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40187step0 raw40187step0Labels permutation104 hz
    mixedMoment B raw40187step1 raw40187step1Labels = mixedMoment B raw40187step2 raw40187step2Labels := by
      have ha : raw40187step2 = (fun i j => raw40187step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40187step2 raw40187step1; decide +kernel
      have hl : raw40187step2Labels = raw40187step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40187step1 raw40187step1Labels permutation15 permutation6
    mixedMoment B raw40187step2 raw40187step2Labels = mixedMoment B raw40187step3 raw40187step3Labels := by
      have ha : raw40187step3 = -raw40187step2 := by apply Matrix.ext; change ∀ i j, raw40187step3 i j = -(raw40187step2 i j); unfold raw40187step3 raw40187step2; decide +kernel
      have hl : raw40187step3Labels = raw40187step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node98 node98Labels := by rfl

theorem canonical40188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40188 raw40188Labels = mixedMoment B node100 node100Labels := by
  calc
    mixedMoment B raw40188 raw40188Labels = mixedMoment B raw40188step0 raw40188step0Labels := by
      have hz : ∀ j, raw40188 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40188step0 = (fun i j => raw40188 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40188step0 raw40188; decide +kernel
      have hl : raw40188step0Labels = raw40188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40188 raw40188Labels permutation520 hz
    mixedMoment B raw40188step0 raw40188step0Labels = mixedMoment B raw40188step1 raw40188step1Labels := by
      have hz : ∀ j, raw40188step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40188step1 = (fun i j => raw40188step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40188step1 raw40188step0; decide +kernel
      have hl : raw40188step1Labels = raw40188step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40188step0 raw40188step0Labels permutation104 hz
    mixedMoment B raw40188step1 raw40188step1Labels = mixedMoment B raw40188step2 raw40188step2Labels := by
      have hz : ∀ j, raw40188step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40188step2 = (fun i j => raw40188step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40188step2 raw40188step1; decide +kernel
      have hl : raw40188step2Labels = raw40188step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40188step1 raw40188step1Labels permutation20 hz
    mixedMoment B raw40188step2 raw40188step2Labels = mixedMoment B raw40188step3 raw40188step3Labels := by
      have ha : raw40188step3 = (fun i j => raw40188step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40188step3 raw40188step2; decide +kernel
      have hl : raw40188step3Labels = raw40188step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40188step2 raw40188step2Labels permutation4 permutation6
    mixedMoment B raw40188step3 raw40188step3Labels = mixedMoment B raw40188step4 raw40188step4Labels := by
      have ha : raw40188step4 = -raw40188step3 := by apply Matrix.ext; change ∀ i j, raw40188step4 i j = -(raw40188step3 i j); unfold raw40188step4 raw40188step3; decide +kernel
      have hl : raw40188step4Labels = raw40188step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node100 node100Labels := by rfl

theorem canonical40189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40189 raw40189Labels = mixedMoment B node257 node257Labels := by
  calc
    mixedMoment B raw40189 raw40189Labels = mixedMoment B raw40189step0 raw40189step0Labels := by
      have ha : raw40189step0 = (fun i j => raw40189 (permutation434 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40189step0 raw40189; decide +kernel
      have hl : raw40189step0Labels = raw40189Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40189 raw40189Labels permutation434 permutation4
    mixedMoment B raw40189step0 raw40189step0Labels = mixedMoment B raw40189step1 raw40189step1Labels := by
      have ha : raw40189step1 = -raw40189step0 := by apply Matrix.ext; change ∀ i j, raw40189step1 i j = -(raw40189step0 i j); unfold raw40189step1 raw40189step0; decide +kernel
      have hl : raw40189step1Labels = raw40189step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node257 node257Labels := by rfl

theorem canonical40190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40190 raw40190Labels = mixedMoment B node242 node242Labels := by
  calc
    mixedMoment B raw40190 raw40190Labels = mixedMoment B raw40190step0 raw40190step0Labels := by
      have ha : raw40190step0 = (fun i j => raw40190 (permutation505 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40190step0 raw40190; decide +kernel
      have hl : raw40190step0Labels = raw40190Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40190 raw40190Labels permutation505 permutation6
    _ = mixedMoment B node242 node242Labels := by rfl

theorem canonical40191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40191 raw40191Labels = mixedMoment B node21 node21Labels := by
  calc
    mixedMoment B raw40191 raw40191Labels = mixedMoment B raw40191step0 raw40191step0Labels := by
      have ha : raw40191step0 = (fun i j => raw40191 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40191step0 raw40191; decide +kernel
      have hl : raw40191step0Labels = raw40191Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40191 raw40191Labels permutation590 permutation6
    _ = mixedMoment B node21 node21Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical40192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40192 raw40192Labels = mixedMoment B node8 node8Labels := by
  calc
    mixedMoment B raw40192 raw40192Labels = mixedMoment B raw40192step0 raw40192step0Labels := by
      have ha : raw40192step0 = (fun i j => raw40192 (permutation665 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40192step0 raw40192; decide +kernel
      have hl : raw40192step0Labels = raw40192Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40192 raw40192Labels permutation665 permutation6
    _ = mixedMoment B node8 node8Labels := by rfl

theorem canonical40193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40193 raw40193Labels = mixedMoment B node172 node172Labels := by
  calc
    mixedMoment B raw40193 raw40193Labels = mixedMoment B raw40193step0 raw40193step0Labels := by
      have ha : raw40193step0 = (fun i j => raw40193 (permutation506 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40193step0 raw40193; decide +kernel
      have hl : raw40193step0Labels = raw40193Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40193 raw40193Labels permutation506 permutation6
    _ = mixedMoment B node172 node172Labels := by rfl

theorem canonical40194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40194 raw40194Labels = mixedMoment B node321 node321Labels := by
  calc
    mixedMoment B raw40194 raw40194Labels = mixedMoment B raw40194step0 raw40194step0Labels := by
      have ha : raw40194step0 = (fun i j => raw40194 (permutation659 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40194step0 raw40194; decide +kernel
      have hl : raw40194step0Labels = raw40194Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40194 raw40194Labels permutation659 permutation7
    _ = mixedMoment B node321 node321Labels := by rfl

theorem canonical40195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40195 raw40195Labels = mixedMoment B node24 node24Labels := by
  calc
    mixedMoment B raw40195 raw40195Labels = mixedMoment B raw40195step0 raw40195step0Labels := by
      have hz : ∀ j, raw40195 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40195step0 = (fun i j => raw40195 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40195step0 raw40195; decide +kernel
      have hl : raw40195step0Labels = raw40195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40195 raw40195Labels permutation434 hz
    mixedMoment B raw40195step0 raw40195step0Labels = mixedMoment B raw40195step1 raw40195step1Labels := by
      have ha : raw40195step1 = (fun i j => raw40195step0 (permutation129 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40195step1 raw40195step0; decide +kernel
      have hl : raw40195step1Labels = raw40195step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40195step0 raw40195step0Labels permutation129 permutation6
    _ = mixedMoment B node24 node24Labels := by rfl

theorem canonical40196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40196 raw40196Labels = mixedMoment B node163 node163Labels := by
  calc
    mixedMoment B raw40196 raw40196Labels = mixedMoment B raw40196step0 raw40196step0Labels := by
      have ha : raw40196step0 = (fun i j => raw40196 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40196step0 raw40196; decide +kernel
      have hl : raw40196step0Labels = raw40196Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40196 raw40196Labels permutation514 permutation6
    _ = mixedMoment B node163 node163Labels := by rfl

theorem canonical40197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40197 raw40197Labels = mixedMoment B node9 node9Labels := by
  calc
    mixedMoment B raw40197 raw40197Labels = mixedMoment B raw40197step0 raw40197step0Labels := by
      have hz : ∀ j, raw40197 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40197step0 = (fun i j => raw40197 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40197step0 raw40197; decide +kernel
      have hl : raw40197step0Labels = raw40197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40197 raw40197Labels permutation434 hz
    mixedMoment B raw40197step0 raw40197step0Labels = mixedMoment B raw40197step1 raw40197step1Labels := by
      have ha : raw40197step1 = (fun i j => raw40197step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40197step1 raw40197step0; decide +kernel
      have hl : raw40197step1Labels = raw40197step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40197step0 raw40197step0Labels permutation146 permutation6
    _ = mixedMoment B node9 node9Labels := by rfl

theorem canonical40198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40198 raw40198Labels = mixedMoment B node260 node260Labels := by
  calc
    mixedMoment B raw40198 raw40198Labels = mixedMoment B raw40198step0 raw40198step0Labels := by
      have hz : ∀ j, raw40198 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40198step0 = (fun i j => raw40198 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40198step0 raw40198; decide +kernel
      have hl : raw40198step0Labels = raw40198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40198 raw40198Labels permutation434 hz
    mixedMoment B raw40198step0 raw40198step0Labels = mixedMoment B raw40198step1 raw40198step1Labels := by
      have ha : raw40198step1 = (fun i j => raw40198step0 (permutation80 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40198step1 raw40198step0; decide +kernel
      have hl : raw40198step1Labels = raw40198step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40198step0 raw40198step0Labels permutation80 permutation4
    mixedMoment B raw40198step1 raw40198step1Labels = mixedMoment B raw40198step2 raw40198step2Labels := by
      have ha : raw40198step2 = -raw40198step1 := by apply Matrix.ext; change ∀ i j, raw40198step2 i j = -(raw40198step1 i j); unfold raw40198step2 raw40198step1; decide +kernel
      have hl : raw40198step2Labels = raw40198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node260 node260Labels := by rfl

theorem canonical40199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40199 raw40199Labels = mixedMoment B node243 node243Labels := by
  calc
    mixedMoment B raw40199 raw40199Labels = mixedMoment B raw40199step0 raw40199step0Labels := by
      have ha : raw40199step0 = (fun i j => raw40199 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40199step0 raw40199; decide +kernel
      have hl : raw40199step0Labels = raw40199Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40199 raw40199Labels permutation414 permutation6
    _ = mixedMoment B node243 node243Labels := by rfl

theorem canonical40200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40200 raw40200Labels = mixedMoment B node171 node171Labels := by
  calc
    mixedMoment B raw40200 raw40200Labels = mixedMoment B raw40200step0 raw40200step0Labels := by
      have ha : raw40200step0 = (fun i j => raw40200 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40200step0 raw40200; decide +kernel
      have hl : raw40200step0Labels = raw40200Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40200 raw40200Labels permutation414 permutation6
    _ = mixedMoment B node171 node171Labels := by rfl

theorem canonical40201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40201 raw40201Labels = mixedMoment B node232 node232Labels := by
  calc
    mixedMoment B raw40201 raw40201Labels = mixedMoment B raw40201step0 raw40201step0Labels := by
      have ha : raw40201step0 = (fun i j => raw40201 (permutation399 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40201step0 raw40201; decide +kernel
      have hl : raw40201step0Labels = raw40201Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40201 raw40201Labels permutation399 permutation6
    _ = mixedMoment B node232 node232Labels := by rfl

theorem canonical40202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40202 raw40202Labels = mixedMoment B node259 node259Labels := by
  calc
    mixedMoment B raw40202 raw40202Labels = mixedMoment B raw40202step0 raw40202step0Labels := by
      have ha : raw40202step0 = (fun i j => raw40202 (permutation349 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40202step0 raw40202; decide +kernel
      have hl : raw40202step0Labels = raw40202Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40202 raw40202Labels permutation349 permutation4
    mixedMoment B raw40202step0 raw40202step0Labels = mixedMoment B raw40202step1 raw40202step1Labels := by
      have ha : raw40202step1 = -raw40202step0 := by apply Matrix.ext; change ∀ i j, raw40202step1 i j = -(raw40202step0 i j); unfold raw40202step1 raw40202step0; decide +kernel
      have hl : raw40202step1Labels = raw40202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node259 node259Labels := by rfl

theorem canonical40203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40203 raw40203Labels = mixedMoment B node220 node220Labels := by
  calc
    mixedMoment B raw40203 raw40203Labels = mixedMoment B raw40203step0 raw40203step0Labels := by
      have ha : raw40203step0 = (fun i j => raw40203 (permutation409 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40203step0 raw40203; decide +kernel
      have hl : raw40203step0Labels = raw40203Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40203 raw40203Labels permutation409 permutation6
    _ = mixedMoment B node220 node220Labels := by rfl

theorem canonical40204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40204 raw40204Labels = mixedMoment B node505 node505Labels := by
  calc
    mixedMoment B raw40204 raw40204Labels = mixedMoment B raw40204step0 raw40204step0Labels := by
      have hz : ∀ j, raw40204 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40204step0 = (fun i j => raw40204 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40204step0 raw40204; decide +kernel
      have hl : raw40204step0Labels = raw40204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40204 raw40204Labels permutation520 hz
    mixedMoment B raw40204step0 raw40204step0Labels = mixedMoment B raw40204step1 raw40204step1Labels := by
      have hz : ∀ j, raw40204step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40204step1 = (fun i j => raw40204step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40204step1 raw40204step0; decide +kernel
      have hl : raw40204step1Labels = raw40204step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40204step0 raw40204step0Labels permutation104 hz
    mixedMoment B raw40204step1 raw40204step1Labels = mixedMoment B raw40204step2 raw40204step2Labels := by
      have ha : raw40204step2 = (fun i j => raw40204step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40204step2 raw40204step1; decide +kernel
      have hl : raw40204step2Labels = raw40204step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40204step1 raw40204step1Labels permutation20 permutation4
    mixedMoment B raw40204step2 raw40204step2Labels = mixedMoment B raw40204step3 raw40204step3Labels := by
      have ha : raw40204step3 = -raw40204step2 := by apply Matrix.ext; change ∀ i j, raw40204step3 i j = -(raw40204step2 i j); unfold raw40204step3 raw40204step2; decide +kernel
      have hl : raw40204step3Labels = raw40204step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node505 node505Labels := by rfl

theorem canonical40205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40205 raw40205Labels = mixedMoment B node502 node502Labels := by
  calc
    mixedMoment B raw40205 raw40205Labels = mixedMoment B raw40205step0 raw40205step0Labels := by
      have hz : ∀ j, raw40205 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40205step0 = (fun i j => raw40205 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40205step0 raw40205; decide +kernel
      have hl : raw40205step0Labels = raw40205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40205 raw40205Labels permutation434 hz
    mixedMoment B raw40205step0 raw40205step0Labels = mixedMoment B raw40205step1 raw40205step1Labels := by
      have ha : raw40205step1 = (fun i j => raw40205step0 (permutation98 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40205step1 raw40205step0; decide +kernel
      have hl : raw40205step1Labels = raw40205step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40205step0 raw40205step0Labels permutation98 permutation6
    _ = mixedMoment B node502 node502Labels := by rfl

theorem canonical40206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40206 raw40206Labels = mixedMoment B node449 node449Labels := by
  calc
    mixedMoment B raw40206 raw40206Labels = mixedMoment B raw40206step0 raw40206step0Labels := by
      have hz : ∀ j, raw40206 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40206step0 = (fun i j => raw40206 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40206step0 raw40206; decide +kernel
      have hl : raw40206step0Labels = raw40206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40206 raw40206Labels permutation434 hz
    mixedMoment B raw40206step0 raw40206step0Labels = mixedMoment B raw40206step1 raw40206step1Labels := by
      have ha : raw40206step1 = (fun i j => raw40206step0 (permutation98 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40206step1 raw40206step0; decide +kernel
      have hl : raw40206step1Labels = raw40206step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40206step0 raw40206step0Labels permutation98 permutation6
    _ = mixedMoment B node449 node449Labels := by rfl

theorem canonical40207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40207 raw40207Labels = mixedMoment B node448 node448Labels := by
  calc
    mixedMoment B raw40207 raw40207Labels = mixedMoment B raw40207step0 raw40207step0Labels := by
      have ha : raw40207step0 = (fun i j => raw40207 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40207step0 raw40207; decide +kernel
      have hl : raw40207step0Labels = raw40207Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40207 raw40207Labels permutation414 permutation6
    _ = mixedMoment B node448 node448Labels := by rfl

theorem canonical40208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40208 raw40208Labels = mixedMoment B node436 node436Labels := by
  calc
    mixedMoment B raw40208 raw40208Labels = mixedMoment B raw40208step0 raw40208step0Labels := by
      have ha : raw40208step0 = (fun i j => raw40208 (permutation399 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40208step0 raw40208; decide +kernel
      have hl : raw40208step0Labels = raw40208Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40208 raw40208Labels permutation399 permutation6
    _ = mixedMoment B node436 node436Labels := by rfl

theorem canonical40209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40209 raw40209Labels = mixedMoment B node429 node429Labels := by
  calc
    mixedMoment B raw40209 raw40209Labels = mixedMoment B raw40209step0 raw40209step0Labels := by
      have ha : raw40209step0 = (fun i j => raw40209 (permutation409 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40209step0 raw40209; decide +kernel
      have hl : raw40209step0Labels = raw40209Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40209 raw40209Labels permutation409 permutation6
    _ = mixedMoment B node429 node429Labels := by rfl

theorem canonical40210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40210 raw40210Labels = mixedMoment B node504 node504Labels := by
  calc
    mixedMoment B raw40210 raw40210Labels = mixedMoment B raw40210step0 raw40210step0Labels := by
      have hz : ∀ j, raw40210 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40210step0 = (fun i j => raw40210 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40210step0 raw40210; decide +kernel
      have hl : raw40210step0Labels = raw40210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40210 raw40210Labels permutation520 hz
    mixedMoment B raw40210step0 raw40210step0Labels = mixedMoment B raw40210step1 raw40210step1Labels := by
      have ha : raw40210step1 = (fun i j => raw40210step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40210step1 raw40210step0; decide +kernel
      have hl : raw40210step1Labels = raw40210step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40210step0 raw40210step0Labels permutation144 permutation3
    mixedMoment B raw40210step1 raw40210step1Labels = mixedMoment B raw40210step2 raw40210step2Labels := by
      have ha : raw40210step2 = -raw40210step1 := by apply Matrix.ext; change ∀ i j, raw40210step2 i j = -(raw40210step1 i j); unfold raw40210step2 raw40210step1; decide +kernel
      have hl : raw40210step2Labels = raw40210step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node504 node504Labels := by rfl

theorem canonical40211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40211 raw40211Labels = mixedMoment B node525 node525Labels := by
  calc
    mixedMoment B raw40211 raw40211Labels = mixedMoment B raw40211step0 raw40211step0Labels := by
      have ha : raw40211step0 = (fun i j => raw40211 (permutation639 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40211step0 raw40211; decide +kernel
      have hl : raw40211step0Labels = raw40211Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40211 raw40211Labels permutation639 permutation2
    mixedMoment B raw40211step0 raw40211step0Labels = mixedMoment B raw40211step1 raw40211step1Labels := by
      have ha : raw40211step1 = -raw40211step0 := by apply Matrix.ext; change ∀ i j, raw40211step1 i j = -(raw40211step0 i j); unfold raw40211step1 raw40211step0; decide +kernel
      have hl : raw40211step1Labels = raw40211step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node525 node525Labels := by rfl

theorem canonical40212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40212 raw40212Labels = mixedMoment B node207 node207Labels := by
  calc
    mixedMoment B raw40212 raw40212Labels = mixedMoment B raw40212step0 raw40212step0Labels := by
      have ha : raw40212step0 = (fun i j => raw40212 (permutation520 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40212step0 raw40212; decide +kernel
      have hl : raw40212step0Labels = raw40212Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40212 raw40212Labels permutation520 permutation6
    mixedMoment B raw40212step0 raw40212step0Labels = mixedMoment B raw40212step1 raw40212step1Labels := by
      have ha : raw40212step1 = -raw40212step0 := by apply Matrix.ext; change ∀ i j, raw40212step1 i j = -(raw40212step0 i j); unfold raw40212step1 raw40212step0; decide +kernel
      have hl : raw40212step1Labels = raw40212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node207 node207Labels := by rfl

theorem canonical40213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40213 raw40213Labels = mixedMoment B node371 node371Labels := by
  calc
    mixedMoment B raw40213 raw40213Labels = mixedMoment B raw40213step0 raw40213step0Labels := by
      have ha : raw40213step0 = (fun i j => raw40213 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40213step0 raw40213; decide +kernel
      have hl : raw40213step0Labels = raw40213Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40213 raw40213Labels permutation590 permutation4
    _ = mixedMoment B node371 node371Labels := by rfl

theorem canonical40214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40214 raw40214Labels = mixedMoment B node339 node339Labels := by
  calc
    mixedMoment B raw40214 raw40214Labels = mixedMoment B raw40214step0 raw40214step0Labels := by
      have hz : ∀ j, raw40214 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40214step0 = (fun i j => raw40214 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40214step0 raw40214; decide +kernel
      have hl : raw40214step0Labels = raw40214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40214 raw40214Labels permutation434 hz
    mixedMoment B raw40214step0 raw40214step0Labels = mixedMoment B raw40214step1 raw40214step1Labels := by
      have ha : raw40214step1 = (fun i j => raw40214step0 (permutation140 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40214step1 raw40214step0; decide +kernel
      have hl : raw40214step1Labels = raw40214step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40214step0 raw40214step0Labels permutation140 permutation7
    _ = mixedMoment B node339 node339Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment736 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 736) =
      Integer.Sparse.eval keyMomentRow736 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 736).leftCharge (GramAssembly.key 736).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 407) := by
    have ha : gramCharges (GramAssembly.key 736).leftCharge (GramAssembly.key 736).rightCharge = raw40184 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40184Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40184 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 736).leftCharge (GramAssembly.key 736).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow736, Integer.Sparse.eval]

theorem keyMoment737 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 737) =
      Integer.Sparse.eval keyMomentRow737 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 737).leftCharge (GramAssembly.key 737).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 379) := by
    have ha : gramCharges (GramAssembly.key 737).leftCharge (GramAssembly.key 737).rightCharge = raw40185 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40185Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40185 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 737).leftCharge (GramAssembly.key 737).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow737, Integer.Sparse.eval]

theorem keyMoment738 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 738) =
      Integer.Sparse.eval keyMomentRow738 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 738).leftCharge (GramAssembly.key 738).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 303) := by
    have ha : gramCharges (GramAssembly.key 738).leftCharge (GramAssembly.key 738).rightCharge = raw40186 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40186Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40186 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 738).leftCharge (GramAssembly.key 738).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow738, Integer.Sparse.eval]

theorem keyMoment739 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 739) =
      Integer.Sparse.eval keyMomentRow739 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 739).leftCharge (GramAssembly.key 739).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 98) := by
    have ha : gramCharges (GramAssembly.key 739).leftCharge (GramAssembly.key 739).rightCharge = raw40187 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40187Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40187 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 739).leftCharge (GramAssembly.key 739).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow739, Integer.Sparse.eval]

theorem keyMoment740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 740) =
      Integer.Sparse.eval keyMomentRow740 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 740).leftCharge (GramAssembly.key 740).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 100) := by
    have ha : gramCharges (GramAssembly.key 740).leftCharge (GramAssembly.key 740).rightCharge = raw40188 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40188Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40188 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 740).leftCharge (GramAssembly.key 740).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow740, Integer.Sparse.eval]

theorem keyMoment741 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 741) =
      Integer.Sparse.eval keyMomentRow741 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 741).leftCharge (GramAssembly.key 741).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 257) := by
    have ha : gramCharges (GramAssembly.key 741).leftCharge (GramAssembly.key 741).rightCharge = raw40189 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40189Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40189 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 741).leftCharge (GramAssembly.key 741).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow741, Integer.Sparse.eval]

theorem keyMoment742 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 742) =
      Integer.Sparse.eval keyMomentRow742 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 742).leftCharge (GramAssembly.key 742).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 242) := by
    have ha : gramCharges (GramAssembly.key 742).leftCharge (GramAssembly.key 742).rightCharge = raw40190 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40190Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40190 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 742).leftCharge (GramAssembly.key 742).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow742, Integer.Sparse.eval]

theorem keyMoment743 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 743) =
      Integer.Sparse.eval keyMomentRow743 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 743).leftCharge (GramAssembly.key 743).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 21) := by
    have ha : gramCharges (GramAssembly.key 743).leftCharge (GramAssembly.key 743).rightCharge = raw40191 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40191Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40191 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 743).leftCharge (GramAssembly.key 743).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow743, Integer.Sparse.eval]

theorem keyMoment744 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 744) =
      Integer.Sparse.eval keyMomentRow744 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 744).leftCharge (GramAssembly.key 744).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 8) := by
    have ha : gramCharges (GramAssembly.key 744).leftCharge (GramAssembly.key 744).rightCharge = raw40192 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40192Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40192 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 744).leftCharge (GramAssembly.key 744).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow744, Integer.Sparse.eval]

theorem keyMoment745 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 745) =
      Integer.Sparse.eval keyMomentRow745 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 745).leftCharge (GramAssembly.key 745).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 172) := by
    have ha : gramCharges (GramAssembly.key 745).leftCharge (GramAssembly.key 745).rightCharge = raw40193 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40193Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40193 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 745).leftCharge (GramAssembly.key 745).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow745, Integer.Sparse.eval]

theorem keyMoment746 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 746) =
      Integer.Sparse.eval keyMomentRow746 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 746).leftCharge (GramAssembly.key 746).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 321) := by
    have ha : gramCharges (GramAssembly.key 746).leftCharge (GramAssembly.key 746).rightCharge = raw40194 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40194Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40194 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 746).leftCharge (GramAssembly.key 746).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow746, Integer.Sparse.eval]

theorem keyMoment747 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 747) =
      Integer.Sparse.eval keyMomentRow747 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 747).leftCharge (GramAssembly.key 747).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 24) := by
    have ha : gramCharges (GramAssembly.key 747).leftCharge (GramAssembly.key 747).rightCharge = raw40195 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40195Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40195 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 747).leftCharge (GramAssembly.key 747).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow747, Integer.Sparse.eval]

theorem keyMoment748 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 748) =
      Integer.Sparse.eval keyMomentRow748 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 748).leftCharge (GramAssembly.key 748).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 163) := by
    have ha : gramCharges (GramAssembly.key 748).leftCharge (GramAssembly.key 748).rightCharge = raw40196 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40196Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40196 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 748).leftCharge (GramAssembly.key 748).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow748, Integer.Sparse.eval]

theorem keyMoment749 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 749) =
      Integer.Sparse.eval keyMomentRow749 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 749).leftCharge (GramAssembly.key 749).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 9) := by
    have ha : gramCharges (GramAssembly.key 749).leftCharge (GramAssembly.key 749).rightCharge = raw40197 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40197Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40197 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 749).leftCharge (GramAssembly.key 749).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow749, Integer.Sparse.eval]

theorem keyMoment750 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 750) =
      Integer.Sparse.eval keyMomentRow750 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 750).leftCharge (GramAssembly.key 750).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 260) := by
    have ha : gramCharges (GramAssembly.key 750).leftCharge (GramAssembly.key 750).rightCharge = raw40198 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40198Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40198 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 750).leftCharge (GramAssembly.key 750).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow750, Integer.Sparse.eval]

theorem keyMoment751 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 751) =
      Integer.Sparse.eval keyMomentRow751 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 751).leftCharge (GramAssembly.key 751).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 243) := by
    have ha : gramCharges (GramAssembly.key 751).leftCharge (GramAssembly.key 751).rightCharge = raw40199 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40199Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40199 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 751).leftCharge (GramAssembly.key 751).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow751, Integer.Sparse.eval]

theorem keyMoment752 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 752) =
      Integer.Sparse.eval keyMomentRow752 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 752).leftCharge (GramAssembly.key 752).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 171) := by
    have ha : gramCharges (GramAssembly.key 752).leftCharge (GramAssembly.key 752).rightCharge = raw40200 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40200Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40200 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 752).leftCharge (GramAssembly.key 752).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow752, Integer.Sparse.eval]

theorem keyMoment753 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 753) =
      Integer.Sparse.eval keyMomentRow753 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 753).leftCharge (GramAssembly.key 753).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 232) := by
    have ha : gramCharges (GramAssembly.key 753).leftCharge (GramAssembly.key 753).rightCharge = raw40201 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40201Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40201 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 753).leftCharge (GramAssembly.key 753).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow753, Integer.Sparse.eval]

theorem keyMoment754 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 754) =
      Integer.Sparse.eval keyMomentRow754 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 754).leftCharge (GramAssembly.key 754).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 259) := by
    have ha : gramCharges (GramAssembly.key 754).leftCharge (GramAssembly.key 754).rightCharge = raw40202 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40202Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40202 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 754).leftCharge (GramAssembly.key 754).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow754, Integer.Sparse.eval]

theorem keyMoment755 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 755) =
      Integer.Sparse.eval keyMomentRow755 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 755).leftCharge (GramAssembly.key 755).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 220) := by
    have ha : gramCharges (GramAssembly.key 755).leftCharge (GramAssembly.key 755).rightCharge = raw40203 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40203Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40203 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 755).leftCharge (GramAssembly.key 755).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow755, Integer.Sparse.eval]

theorem keyMoment756 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 756) =
      Integer.Sparse.eval keyMomentRow756 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 756).leftCharge (GramAssembly.key 756).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 505) := by
    have ha : gramCharges (GramAssembly.key 756).leftCharge (GramAssembly.key 756).rightCharge = raw40204 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40204Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40204 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 756).leftCharge (GramAssembly.key 756).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow756, Integer.Sparse.eval]

theorem keyMoment757 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 757) =
      Integer.Sparse.eval keyMomentRow757 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 757).leftCharge (GramAssembly.key 757).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 502) := by
    have ha : gramCharges (GramAssembly.key 757).leftCharge (GramAssembly.key 757).rightCharge = raw40205 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40205Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40205 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 757).leftCharge (GramAssembly.key 757).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow757, Integer.Sparse.eval]

theorem keyMoment758 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 758) =
      Integer.Sparse.eval keyMomentRow758 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 758).leftCharge (GramAssembly.key 758).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 449) := by
    have ha : gramCharges (GramAssembly.key 758).leftCharge (GramAssembly.key 758).rightCharge = raw40206 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40206Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40206 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 758).leftCharge (GramAssembly.key 758).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow758, Integer.Sparse.eval]

theorem keyMoment759 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 759) =
      Integer.Sparse.eval keyMomentRow759 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 759).leftCharge (GramAssembly.key 759).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 448) := by
    have ha : gramCharges (GramAssembly.key 759).leftCharge (GramAssembly.key 759).rightCharge = raw40207 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40207Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40207 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 759).leftCharge (GramAssembly.key 759).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow759, Integer.Sparse.eval]

theorem keyMoment760 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 760) =
      Integer.Sparse.eval keyMomentRow760 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 760).leftCharge (GramAssembly.key 760).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 436) := by
    have ha : gramCharges (GramAssembly.key 760).leftCharge (GramAssembly.key 760).rightCharge = raw40208 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40208Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40208 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 760).leftCharge (GramAssembly.key 760).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow760, Integer.Sparse.eval]

theorem keyMoment761 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 761) =
      Integer.Sparse.eval keyMomentRow761 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 761).leftCharge (GramAssembly.key 761).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 429) := by
    have ha : gramCharges (GramAssembly.key 761).leftCharge (GramAssembly.key 761).rightCharge = raw40209 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40209Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40209 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 761).leftCharge (GramAssembly.key 761).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow761, Integer.Sparse.eval]

theorem keyMoment762 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 762) =
      Integer.Sparse.eval keyMomentRow762 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 762).leftCharge (GramAssembly.key 762).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 504) := by
    have ha : gramCharges (GramAssembly.key 762).leftCharge (GramAssembly.key 762).rightCharge = raw40210 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40210Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40210 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 762).leftCharge (GramAssembly.key 762).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow762, Integer.Sparse.eval]

theorem keyMoment763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 763) =
      Integer.Sparse.eval keyMomentRow763 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 763).leftCharge (GramAssembly.key 763).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 525) := by
    have ha : gramCharges (GramAssembly.key 763).leftCharge (GramAssembly.key 763).rightCharge = raw40211 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40211Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40211 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 763).leftCharge (GramAssembly.key 763).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow763, Integer.Sparse.eval]

theorem keyMoment764 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 764) =
      Integer.Sparse.eval keyMomentRow764 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 764).leftCharge (GramAssembly.key 764).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 207) := by
    have ha : gramCharges (GramAssembly.key 764).leftCharge (GramAssembly.key 764).rightCharge = raw40212 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40212Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40212 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 764).leftCharge (GramAssembly.key 764).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow764, Integer.Sparse.eval]

theorem keyMoment765 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 765) =
      Integer.Sparse.eval keyMomentRow765 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 765).leftCharge (GramAssembly.key 765).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 371) := by
    have ha : gramCharges (GramAssembly.key 765).leftCharge (GramAssembly.key 765).rightCharge = raw40213 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40213Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40213 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 765).leftCharge (GramAssembly.key 765).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow765, Integer.Sparse.eval]

theorem keyMoment766 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 766) =
      Integer.Sparse.eval keyMomentRow766 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 766).leftCharge (GramAssembly.key 766).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 531) := by
    have ha : gramCharges (GramAssembly.key 766).leftCharge (GramAssembly.key 766).rightCharge = raw38154 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw38154Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical38154 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 766).leftCharge (GramAssembly.key 766).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow766, Integer.Sparse.eval]

theorem keyMoment767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 767) =
      Integer.Sparse.eval keyMomentRow767 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 767).leftCharge (GramAssembly.key 767).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 339) := by
    have ha : gramCharges (GramAssembly.key 767).leftCharge (GramAssembly.key 767).rightCharge = raw40214 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40214Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40214 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 767).leftCharge (GramAssembly.key 767).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow767, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt736 : keyMomentRows (736 : Fin 2886) =
    keyMomentRow736 := by decide +kernel

theorem keyMomentRowsAt737 : keyMomentRows (737 : Fin 2886) =
    keyMomentRow737 := by decide +kernel

theorem keyMomentRowsAt738 : keyMomentRows (738 : Fin 2886) =
    keyMomentRow738 := by decide +kernel

theorem keyMomentRowsAt739 : keyMomentRows (739 : Fin 2886) =
    keyMomentRow739 := by decide +kernel

theorem keyMomentRowsAt740 : keyMomentRows (740 : Fin 2886) =
    keyMomentRow740 := by decide +kernel

theorem keyMomentRowsAt741 : keyMomentRows (741 : Fin 2886) =
    keyMomentRow741 := by decide +kernel

theorem keyMomentRowsAt742 : keyMomentRows (742 : Fin 2886) =
    keyMomentRow742 := by decide +kernel

theorem keyMomentRowsAt743 : keyMomentRows (743 : Fin 2886) =
    keyMomentRow743 := by decide +kernel

theorem keyMomentRowsAt744 : keyMomentRows (744 : Fin 2886) =
    keyMomentRow744 := by decide +kernel

theorem keyMomentRowsAt745 : keyMomentRows (745 : Fin 2886) =
    keyMomentRow745 := by decide +kernel

theorem keyMomentRowsAt746 : keyMomentRows (746 : Fin 2886) =
    keyMomentRow746 := by decide +kernel

theorem keyMomentRowsAt747 : keyMomentRows (747 : Fin 2886) =
    keyMomentRow747 := by decide +kernel

theorem keyMomentRowsAt748 : keyMomentRows (748 : Fin 2886) =
    keyMomentRow748 := by decide +kernel

theorem keyMomentRowsAt749 : keyMomentRows (749 : Fin 2886) =
    keyMomentRow749 := by decide +kernel

theorem keyMomentRowsAt750 : keyMomentRows (750 : Fin 2886) =
    keyMomentRow750 := by decide +kernel

theorem keyMomentRowsAt751 : keyMomentRows (751 : Fin 2886) =
    keyMomentRow751 := by decide +kernel

theorem keyMomentRowsAt752 : keyMomentRows (752 : Fin 2886) =
    keyMomentRow752 := by decide +kernel

theorem keyMomentRowsAt753 : keyMomentRows (753 : Fin 2886) =
    keyMomentRow753 := by decide +kernel

theorem keyMomentRowsAt754 : keyMomentRows (754 : Fin 2886) =
    keyMomentRow754 := by decide +kernel

theorem keyMomentRowsAt755 : keyMomentRows (755 : Fin 2886) =
    keyMomentRow755 := by decide +kernel

theorem keyMomentRowsAt756 : keyMomentRows (756 : Fin 2886) =
    keyMomentRow756 := by decide +kernel

theorem keyMomentRowsAt757 : keyMomentRows (757 : Fin 2886) =
    keyMomentRow757 := by decide +kernel

theorem keyMomentRowsAt758 : keyMomentRows (758 : Fin 2886) =
    keyMomentRow758 := by decide +kernel

theorem keyMomentRowsAt759 : keyMomentRows (759 : Fin 2886) =
    keyMomentRow759 := by decide +kernel

theorem keyMomentRowsAt760 : keyMomentRows (760 : Fin 2886) =
    keyMomentRow760 := by decide +kernel

theorem keyMomentRowsAt761 : keyMomentRows (761 : Fin 2886) =
    keyMomentRow761 := by decide +kernel

theorem keyMomentRowsAt762 : keyMomentRows (762 : Fin 2886) =
    keyMomentRow762 := by decide +kernel

theorem keyMomentRowsAt763 : keyMomentRows (763 : Fin 2886) =
    keyMomentRow763 := by decide +kernel

theorem keyMomentRowsAt764 : keyMomentRows (764 : Fin 2886) =
    keyMomentRow764 := by decide +kernel

theorem keyMomentRowsAt765 : keyMomentRows (765 : Fin 2886) =
    keyMomentRow765 := by decide +kernel

theorem keyMomentRowsAt766 : keyMomentRows (766 : Fin 2886) =
    keyMomentRow766 := by decide +kernel

theorem keyMomentRowsAt767 : keyMomentRows (767 : Fin 2886) =
    keyMomentRow767 := by decide +kernel

theorem keyMomentChunkSound23_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 23) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 736 ∨ k.val = 737 ∨ k.val = 738 ∨ k.val = 739 ∨ k.val = 740 ∨ k.val = 741 ∨ k.val = 742 ∨ k.val = 743 ∨ k.val = 744 ∨ k.val = 745 ∨ k.val = 746 ∨ k.val = 747 ∨ k.val = 748 ∨ k.val = 749 ∨ k.val = 750 ∨ k.val = 751 ∨ k.val = 752 ∨ k.val = 753 ∨ k.val = 754 ∨ k.val = 755 ∨ k.val = 756 ∨ k.val = 757 ∨ k.val = 758 ∨ k.val = 759 ∨ k.val = 760 ∨ k.val = 761 ∨ k.val = 762 ∨ k.val = 763 ∨ k.val = 764 ∨ k.val = 765 ∨ k.val = 766 ∨ k.val = 767 := by omega
  rcases heq with h736 | h737 | h738 | h739 | h740 | h741 | h742 | h743 | h744 | h745 | h746 | h747 | h748 | h749 | h750 | h751 | h752 | h753 | h754 | h755 | h756 | h757 | h758 | h759 | h760 | h761 | h762 | h763 | h764 | h765 | h766 | h767
  · have he : k = (736 : Fin 2886) := Fin.ext h736
    subst k
    rw [keyMomentRowsAt736]
    exact keyMoment736 B hB
  · have he : k = (737 : Fin 2886) := Fin.ext h737
    subst k
    rw [keyMomentRowsAt737]
    exact keyMoment737 B hB
  · have he : k = (738 : Fin 2886) := Fin.ext h738
    subst k
    rw [keyMomentRowsAt738]
    exact keyMoment738 B hB
  · have he : k = (739 : Fin 2886) := Fin.ext h739
    subst k
    rw [keyMomentRowsAt739]
    exact keyMoment739 B hB
  · have he : k = (740 : Fin 2886) := Fin.ext h740
    subst k
    rw [keyMomentRowsAt740]
    exact keyMoment740 B hB
  · have he : k = (741 : Fin 2886) := Fin.ext h741
    subst k
    rw [keyMomentRowsAt741]
    exact keyMoment741 B hB
  · have he : k = (742 : Fin 2886) := Fin.ext h742
    subst k
    rw [keyMomentRowsAt742]
    exact keyMoment742 B hB
  · have he : k = (743 : Fin 2886) := Fin.ext h743
    subst k
    rw [keyMomentRowsAt743]
    exact keyMoment743 B hB
  · have he : k = (744 : Fin 2886) := Fin.ext h744
    subst k
    rw [keyMomentRowsAt744]
    exact keyMoment744 B hB
  · have he : k = (745 : Fin 2886) := Fin.ext h745
    subst k
    rw [keyMomentRowsAt745]
    exact keyMoment745 B hB
  · have he : k = (746 : Fin 2886) := Fin.ext h746
    subst k
    rw [keyMomentRowsAt746]
    exact keyMoment746 B hB
  · have he : k = (747 : Fin 2886) := Fin.ext h747
    subst k
    rw [keyMomentRowsAt747]
    exact keyMoment747 B hB
  · have he : k = (748 : Fin 2886) := Fin.ext h748
    subst k
    rw [keyMomentRowsAt748]
    exact keyMoment748 B hB
  · have he : k = (749 : Fin 2886) := Fin.ext h749
    subst k
    rw [keyMomentRowsAt749]
    exact keyMoment749 B hB
  · have he : k = (750 : Fin 2886) := Fin.ext h750
    subst k
    rw [keyMomentRowsAt750]
    exact keyMoment750 B hB
  · have he : k = (751 : Fin 2886) := Fin.ext h751
    subst k
    rw [keyMomentRowsAt751]
    exact keyMoment751 B hB
  · have he : k = (752 : Fin 2886) := Fin.ext h752
    subst k
    rw [keyMomentRowsAt752]
    exact keyMoment752 B hB
  · have he : k = (753 : Fin 2886) := Fin.ext h753
    subst k
    rw [keyMomentRowsAt753]
    exact keyMoment753 B hB
  · have he : k = (754 : Fin 2886) := Fin.ext h754
    subst k
    rw [keyMomentRowsAt754]
    exact keyMoment754 B hB
  · have he : k = (755 : Fin 2886) := Fin.ext h755
    subst k
    rw [keyMomentRowsAt755]
    exact keyMoment755 B hB
  · have he : k = (756 : Fin 2886) := Fin.ext h756
    subst k
    rw [keyMomentRowsAt756]
    exact keyMoment756 B hB
  · have he : k = (757 : Fin 2886) := Fin.ext h757
    subst k
    rw [keyMomentRowsAt757]
    exact keyMoment757 B hB
  · have he : k = (758 : Fin 2886) := Fin.ext h758
    subst k
    rw [keyMomentRowsAt758]
    exact keyMoment758 B hB
  · have he : k = (759 : Fin 2886) := Fin.ext h759
    subst k
    rw [keyMomentRowsAt759]
    exact keyMoment759 B hB
  · have he : k = (760 : Fin 2886) := Fin.ext h760
    subst k
    rw [keyMomentRowsAt760]
    exact keyMoment760 B hB
  · have he : k = (761 : Fin 2886) := Fin.ext h761
    subst k
    rw [keyMomentRowsAt761]
    exact keyMoment761 B hB
  · have he : k = (762 : Fin 2886) := Fin.ext h762
    subst k
    rw [keyMomentRowsAt762]
    exact keyMoment762 B hB
  · have he : k = (763 : Fin 2886) := Fin.ext h763
    subst k
    rw [keyMomentRowsAt763]
    exact keyMoment763 B hB
  · have he : k = (764 : Fin 2886) := Fin.ext h764
    subst k
    rw [keyMomentRowsAt764]
    exact keyMoment764 B hB
  · have he : k = (765 : Fin 2886) := Fin.ext h765
    subst k
    rw [keyMomentRowsAt765]
    exact keyMoment765 B hB
  · have he : k = (766 : Fin 2886) := Fin.ext h766
    subst k
    rw [keyMomentRowsAt766]
    exact keyMoment766 B hB
  · have he : k = (767 : Fin 2886) := Fin.ext h767
    subst k
    rw [keyMomentRowsAt767]
    exact keyMoment767 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound23_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound23_e_oai
