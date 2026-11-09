-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound11_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:46:15.49721+00:00
-- url     : https://prove2.me/submissions/823ba554-e43a-4ec9-8911-6fff43a38323

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical297
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical38091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38091 raw38091Labels = mixedMoment B node492 node492Labels := by
  calc
    _ = mixedMoment B node492 node492Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical310
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39801 raw39801Labels = mixedMoment B node346 node346Labels := by
  calc
    mixedMoment B raw39801 raw39801Labels = mixedMoment B raw39801step0 raw39801step0Labels := by
      have hz : ∀ j, raw39801 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39801step0 = (fun i j => raw39801 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39801step0 raw39801; decide +kernel
      have hl : raw39801step0Labels = raw39801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39801 raw39801Labels permutation346 hz
    mixedMoment B raw39801step0 raw39801step0Labels = mixedMoment B raw39801step1 raw39801step1Labels := by
      have ha : raw39801step1 = (fun i j => raw39801step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39801step1 raw39801step0; decide +kernel
      have hl : raw39801step1Labels = raw39801step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39801step0 raw39801step0Labels permutation139 permutation7
    _ = mixedMoment B node346 node346Labels := by rfl

theorem canonical39802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39802 raw39802Labels = mixedMoment B node476 node476Labels := by
  calc
    mixedMoment B raw39802 raw39802Labels = mixedMoment B raw39802step0 raw39802step0Labels := by
      have ha : raw39802step0 = (fun i j => raw39802 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39802step0 raw39802; decide +kernel
      have hl : raw39802step0Labels = raw39802Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39802 raw39802Labels permutation195 permutation7
    mixedMoment B raw39802step0 raw39802step0Labels = mixedMoment B raw39802step1 raw39802step1Labels := by
      have ha : raw39802step1 = -raw39802step0 := by apply Matrix.ext; change ∀ i j, raw39802step1 i j = -(raw39802step0 i j); unfold raw39802step1 raw39802step0; decide +kernel
      have hl : raw39802step1Labels = raw39802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node476 node476Labels := by rfl

theorem canonical39803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39803 raw39803Labels = mixedMoment B node484 node484Labels := by
  calc
    mixedMoment B raw39803 raw39803Labels = mixedMoment B raw39803step0 raw39803step0Labels := by
      have ha : raw39803step0 = (fun i j => raw39803 (permutation192 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39803step0 raw39803; decide +kernel
      have hl : raw39803step0Labels = raw39803Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39803 raw39803Labels permutation192 permutation7
    mixedMoment B raw39803step0 raw39803step0Labels = mixedMoment B raw39803step1 raw39803step1Labels := by
      have ha : raw39803step1 = -raw39803step0 := by apply Matrix.ext; change ∀ i j, raw39803step1 i j = -(raw39803step0 i j); unfold raw39803step1 raw39803step0; decide +kernel
      have hl : raw39803step1Labels = raw39803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node484 node484Labels := by rfl

theorem canonical39804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39804 raw39804Labels = mixedMoment B node269 node269Labels := by
  calc
    mixedMoment B raw39804 raw39804Labels = mixedMoment B raw39804step0 raw39804step0Labels := by
      have hz : ∀ j, raw39804 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39804step0 = (fun i j => raw39804 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39804step0 raw39804; decide +kernel
      have hl : raw39804step0Labels = raw39804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39804 raw39804Labels permutation520 hz
    mixedMoment B raw39804step0 raw39804step0Labels = mixedMoment B raw39804step1 raw39804step1Labels := by
      have hz : ∀ j, raw39804step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39804step1 = (fun i j => raw39804step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39804step1 raw39804step0; decide +kernel
      have hl : raw39804step1Labels = raw39804step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39804step0 raw39804step0Labels permutation104 hz
    mixedMoment B raw39804step1 raw39804step1Labels = mixedMoment B raw39804step2 raw39804step2Labels := by
      have ha : raw39804step2 = (fun i j => raw39804step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39804step2 raw39804step1; decide +kernel
      have hl : raw39804step2Labels = raw39804step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39804step1 raw39804step1Labels permutation31 permutation3
    mixedMoment B raw39804step2 raw39804step2Labels = mixedMoment B raw39804step3 raw39804step3Labels := by
      have ha : raw39804step3 = -raw39804step2 := by apply Matrix.ext; change ∀ i j, raw39804step3 i j = -(raw39804step2 i j); unfold raw39804step3 raw39804step2; decide +kernel
      have hl : raw39804step3Labels = raw39804step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node269 node269Labels := by rfl

theorem canonical39805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39805 raw39805Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39805 raw39805Labels = mixedMoment B raw39805step0 raw39805step0Labels := by
      have hz : ∀ j, raw39805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39805step0 = (fun i j => raw39805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39805step0 raw39805; decide +kernel
      have hl : raw39805step0Labels = raw39805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39805 raw39805Labels permutation434 hz
    mixedMoment B raw39805step0 raw39805step0Labels = mixedMoment B raw39805step1 raw39805step1Labels := by
      have ha : raw39805step1 = (fun i j => raw39805step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39805step1 raw39805step0; decide +kernel
      have hl : raw39805step1Labels = raw39805step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39805step0 raw39805step0Labels permutation146 permutation5
    _ = mixedMoment B node384 node384Labels := by rfl

theorem canonical39806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39806 raw39806Labels = mixedMoment B node468 node468Labels := by
  calc
    mixedMoment B raw39806 raw39806Labels = mixedMoment B raw39806step0 raw39806step0Labels := by
      have hz : ∀ j, raw39806 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39806step0 = (fun i j => raw39806 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39806step0 raw39806; decide +kernel
      have hl : raw39806step0Labels = raw39806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39806 raw39806Labels permutation434 hz
    mixedMoment B raw39806step0 raw39806step0Labels = mixedMoment B raw39806step1 raw39806step1Labels := by
      have ha : raw39806step1 = (fun i j => raw39806step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39806step1 raw39806step0; decide +kernel
      have hl : raw39806step1Labels = raw39806step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39806step0 raw39806step0Labels permutation151 permutation3
    mixedMoment B raw39806step1 raw39806step1Labels = mixedMoment B raw39806step2 raw39806step2Labels := by
      have ha : raw39806step2 = -raw39806step1 := by apply Matrix.ext; change ∀ i j, raw39806step2 i j = -(raw39806step1 i j); unfold raw39806step2 raw39806step1; decide +kernel
      have hl : raw39806step2Labels = raw39806step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node468 node468Labels := by rfl

theorem canonical39807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39807 raw39807Labels = mixedMoment B node491 node491Labels := by
  calc
    mixedMoment B raw39807 raw39807Labels = mixedMoment B raw39807step0 raw39807step0Labels := by
      have hz : ∀ j, raw39807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39807step0 = (fun i j => raw39807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39807step0 raw39807; decide +kernel
      have hl : raw39807step0Labels = raw39807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39807 raw39807Labels permutation434 hz
    _ = mixedMoment B node491 node491Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical311
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39808 raw39808Labels = mixedMoment B node364 node364Labels := by
  calc
    mixedMoment B raw39808 raw39808Labels = mixedMoment B raw39808step0 raw39808step0Labels := by
      have hz : ∀ j, raw39808 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39808step0 = (fun i j => raw39808 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39808step0 raw39808; decide +kernel
      have hl : raw39808step0Labels = raw39808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39808 raw39808Labels permutation434 hz
    mixedMoment B raw39808step0 raw39808step0Labels = mixedMoment B raw39808step1 raw39808step1Labels := by
      have ha : raw39808step1 = (fun i j => raw39808step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39808step1 raw39808step0; decide +kernel
      have hl : raw39808step1Labels = raw39808step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39808step0 raw39808step0Labels permutation108 permutation4
    _ = mixedMoment B node364 node364Labels := by rfl

theorem canonical39809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39809 raw39809Labels = mixedMoment B node481 node481Labels := by
  calc
    mixedMoment B raw39809 raw39809Labels = mixedMoment B raw39809step0 raw39809step0Labels := by
      have ha : raw39809step0 = (fun i j => raw39809 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39809step0 raw39809; decide +kernel
      have hl : raw39809step0Labels = raw39809Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39809 raw39809Labels permutation158 permutation2
    _ = mixedMoment B node481 node481Labels := by rfl

theorem canonical39810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39810 raw39810Labels = mixedMoment B node443 node443Labels := by
  calc
    mixedMoment B raw39810 raw39810Labels = mixedMoment B raw39810step0 raw39810step0Labels := by
      have ha : raw39810step0 = (fun i j => raw39810 (permutation421 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39810step0 raw39810; decide +kernel
      have hl : raw39810step0Labels = raw39810Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39810 raw39810Labels permutation421 permutation6
    _ = mixedMoment B node443 node443Labels := by rfl

theorem canonical39811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39811 raw39811Labels = mixedMoment B node440 node440Labels := by
  calc
    mixedMoment B raw39811 raw39811Labels = mixedMoment B raw39811step0 raw39811step0Labels := by
      have ha : raw39811step0 = (fun i j => raw39811 (permutation422 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39811step0 raw39811; decide +kernel
      have hl : raw39811step0Labels = raw39811Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39811 raw39811Labels permutation422 permutation6
    _ = mixedMoment B node440 node440Labels := by rfl

theorem canonical39812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39812 raw39812Labels = mixedMoment B node480 node480Labels := by
  calc
    mixedMoment B raw39812 raw39812Labels = mixedMoment B raw39812step0 raw39812step0Labels := by
      have ha : raw39812step0 = (fun i j => raw39812 (permutation387 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39812step0 raw39812; decide +kernel
      have hl : raw39812step0Labels = raw39812Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39812 raw39812Labels permutation387 permutation6
    _ = mixedMoment B node480 node480Labels := by rfl

theorem canonical39813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39813 raw39813Labels = mixedMoment B node489 node489Labels := by
  calc
    mixedMoment B raw39813 raw39813Labels = mixedMoment B raw39813step0 raw39813step0Labels := by
      have hz : ∀ j, raw39813 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39813step0 = (fun i j => raw39813 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39813step0 raw39813; decide +kernel
      have hl : raw39813step0Labels = raw39813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39813 raw39813Labels permutation434 hz
    _ = mixedMoment B node489 node489Labels := by rfl

theorem canonical39814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39814 raw39814Labels = mixedMoment B node478 node478Labels := by
  calc
    mixedMoment B raw39814 raw39814Labels = mixedMoment B raw39814step0 raw39814step0Labels := by
      have ha : raw39814step0 = (fun i j => raw39814 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39814step0 raw39814; decide +kernel
      have hl : raw39814step0Labels = raw39814Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39814 raw39814Labels permutation158 permutation2
    _ = mixedMoment B node478 node478Labels := by rfl

theorem canonical39815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39815 raw39815Labels = mixedMoment B node391 node391Labels := by
  calc
    mixedMoment B raw39815 raw39815Labels = mixedMoment B raw39815step0 raw39815step0Labels := by
      have hz : ∀ j, raw39815 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39815step0 = (fun i j => raw39815 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39815step0 raw39815; decide +kernel
      have hl : raw39815step0Labels = raw39815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39815 raw39815Labels permutation434 hz
    mixedMoment B raw39815step0 raw39815step0Labels = mixedMoment B raw39815step1 raw39815step1Labels := by
      have hz : ∀ j, raw39815step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39815step1 = (fun i j => raw39815step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39815step1 raw39815step0; decide +kernel
      have hl : raw39815step1Labels = raw39815step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39815step0 raw39815step0Labels permutation80 hz
    mixedMoment B raw39815step1 raw39815step1Labels = mixedMoment B raw39815step2 raw39815step2Labels := by
      have ha : raw39815step2 = (fun i j => raw39815step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39815step2 raw39815step1; decide +kernel
      have hl : raw39815step2Labels = raw39815step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39815step1 raw39815step1Labels permutation23 permutation6
    _ = mixedMoment B node391 node391Labels := by rfl

theorem canonical39816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39816 raw39816Labels = mixedMoment B node148 node148Labels := by
  calc
    mixedMoment B raw39816 raw39816Labels = mixedMoment B raw39816step0 raw39816step0Labels := by
      have hz : ∀ j, raw39816 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39816step0 = (fun i j => raw39816 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39816step0 raw39816; decide +kernel
      have hl : raw39816step0Labels = raw39816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39816 raw39816Labels permutation434 hz
    mixedMoment B raw39816step0 raw39816step0Labels = mixedMoment B raw39816step1 raw39816step1Labels := by
      have hz : ∀ j, raw39816step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39816step1 = (fun i j => raw39816step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39816step1 raw39816step0; decide +kernel
      have hl : raw39816step1Labels = raw39816step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39816step0 raw39816step0Labels permutation80 hz
    mixedMoment B raw39816step1 raw39816step1Labels = mixedMoment B raw39816step2 raw39816step2Labels := by
      have ha : raw39816step2 = (fun i j => raw39816step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39816step2 raw39816step1; decide +kernel
      have hl : raw39816step2Labels = raw39816step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39816step1 raw39816step1Labels permutation28 permutation6
    _ = mixedMoment B node148 node148Labels := by rfl

theorem canonical39817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39817 raw39817Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39817 raw39817Labels = mixedMoment B raw39817step0 raw39817step0Labels := by
      have hz : ∀ j, raw39817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39817step0 = (fun i j => raw39817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39817step0 raw39817; decide +kernel
      have hl : raw39817step0Labels = raw39817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39817 raw39817Labels permutation346 hz
    mixedMoment B raw39817step0 raw39817step0Labels = mixedMoment B raw39817step1 raw39817step1Labels := by
      have ha : raw39817step1 = (fun i j => raw39817step0 (permutation115 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39817step1 raw39817step0; decide +kernel
      have hl : raw39817step1Labels = raw39817step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39817step0 raw39817step0Labels permutation115 permutation6
    _ = mixedMoment B node384 node384Labels := by rfl

theorem canonical39818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39818 raw39818Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw39818 raw39818Labels = mixedMoment B raw39818step0 raw39818step0Labels := by
      have hz : ∀ j, raw39818 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39818step0 = (fun i j => raw39818 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39818step0 raw39818; decide +kernel
      have hl : raw39818step0Labels = raw39818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39818 raw39818Labels permutation346 hz
    mixedMoment B raw39818step0 raw39818step0Labels = mixedMoment B raw39818step1 raw39818step1Labels := by
      have ha : raw39818step1 = (fun i j => raw39818step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39818step1 raw39818step0; decide +kernel
      have hl : raw39818step1Labels = raw39818step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39818step0 raw39818step0Labels permutation149 permutation7
    _ = mixedMoment B node377 node377Labels := by rfl

theorem canonical39819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39819 raw39819Labels = mixedMoment B node145 node145Labels := by
  calc
    mixedMoment B raw39819 raw39819Labels = mixedMoment B raw39819step0 raw39819step0Labels := by
      have hz : ∀ j, raw39819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39819step0 = (fun i j => raw39819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39819step0 raw39819; decide +kernel
      have hl : raw39819step0Labels = raw39819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39819 raw39819Labels permutation346 hz
    mixedMoment B raw39819step0 raw39819step0Labels = mixedMoment B raw39819step1 raw39819step1Labels := by
      have ha : raw39819step1 = (fun i j => raw39819step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39819step1 raw39819step0; decide +kernel
      have hl : raw39819step1Labels = raw39819step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39819step0 raw39819step0Labels permutation137 permutation6
    _ = mixedMoment B node145 node145Labels := by rfl

theorem canonical39820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39820 raw39820Labels = mixedMoment B node139 node139Labels := by
  calc
    mixedMoment B raw39820 raw39820Labels = mixedMoment B raw39820step0 raw39820step0Labels := by
      have hz : ∀ j, raw39820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39820step0 = (fun i j => raw39820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39820step0 raw39820; decide +kernel
      have hl : raw39820step0Labels = raw39820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39820 raw39820Labels permutation346 hz
    mixedMoment B raw39820step0 raw39820step0Labels = mixedMoment B raw39820step1 raw39820step1Labels := by
      have ha : raw39820step1 = (fun i j => raw39820step0 (permutation138 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39820step1 raw39820step0; decide +kernel
      have hl : raw39820step1Labels = raw39820step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39820step0 raw39820step0Labels permutation138 permutation6
    _ = mixedMoment B node139 node139Labels := by rfl

theorem canonical39821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39821 raw39821Labels = mixedMoment B node322 node322Labels := by
  calc
    mixedMoment B raw39821 raw39821Labels = mixedMoment B raw39821step0 raw39821step0Labels := by
      have ha : raw39821step0 = (fun i j => raw39821 (permutation492 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39821step0 raw39821; decide +kernel
      have hl : raw39821step0Labels = raw39821Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39821 raw39821Labels permutation492 permutation6
    _ = mixedMoment B node322 node322Labels := by rfl

theorem canonical39822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39822 raw39822Labels = mixedMoment B node373 node373Labels := by
  calc
    mixedMoment B raw39822 raw39822Labels = mixedMoment B raw39822step0 raw39822step0Labels := by
      have ha : raw39822step0 = (fun i j => raw39822 (permutation463 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39822step0 raw39822; decide +kernel
      have hl : raw39822step0Labels = raw39822Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39822 raw39822Labels permutation463 permutation6
    _ = mixedMoment B node373 node373Labels := by rfl

theorem canonical39823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39823 raw39823Labels = mixedMoment B node264 node264Labels := by
  calc
    mixedMoment B raw39823 raw39823Labels = mixedMoment B raw39823step0 raw39823step0Labels := by
      have hz : ∀ j, raw39823 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39823step0 = (fun i j => raw39823 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39823step0 raw39823; decide +kernel
      have hl : raw39823step0Labels = raw39823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39823 raw39823Labels permutation520 hz
    mixedMoment B raw39823step0 raw39823step0Labels = mixedMoment B raw39823step1 raw39823step1Labels := by
      have hz : ∀ j, raw39823step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39823step1 = (fun i j => raw39823step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39823step1 raw39823step0; decide +kernel
      have hl : raw39823step1Labels = raw39823step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39823step0 raw39823step0Labels permutation104 hz
    mixedMoment B raw39823step1 raw39823step1Labels = mixedMoment B raw39823step2 raw39823step2Labels := by
      have ha : raw39823step2 = (fun i j => raw39823step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39823step2 raw39823step1; decide +kernel
      have hl : raw39823step2Labels = raw39823step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39823step1 raw39823step1Labels permutation22 permutation4
    mixedMoment B raw39823step2 raw39823step2Labels = mixedMoment B raw39823step3 raw39823step3Labels := by
      have ha : raw39823step3 = -raw39823step2 := by apply Matrix.ext; change ∀ i j, raw39823step3 i j = -(raw39823step2 i j); unfold raw39823step3 raw39823step2; decide +kernel
      have hl : raw39823step3Labels = raw39823step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node264 node264Labels := by rfl

theorem canonical39824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39824 raw39824Labels = mixedMoment B node263 node263Labels := by
  calc
    mixedMoment B raw39824 raw39824Labels = mixedMoment B raw39824step0 raw39824step0Labels := by
      have hz : ∀ j, raw39824 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39824step0 = (fun i j => raw39824 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39824step0 raw39824; decide +kernel
      have hl : raw39824step0Labels = raw39824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39824 raw39824Labels permutation434 hz
    mixedMoment B raw39824step0 raw39824step0Labels = mixedMoment B raw39824step1 raw39824step1Labels := by
      have ha : raw39824step1 = (fun i j => raw39824step0 (permutation86 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39824step1 raw39824step0; decide +kernel
      have hl : raw39824step1Labels = raw39824step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39824step0 raw39824step0Labels permutation86 permutation4
    mixedMoment B raw39824step1 raw39824step1Labels = mixedMoment B raw39824step2 raw39824step2Labels := by
      have ha : raw39824step2 = -raw39824step1 := by apply Matrix.ext; change ∀ i j, raw39824step2 i j = -(raw39824step1 i j); unfold raw39824step2 raw39824step1; decide +kernel
      have hl : raw39824step2Labels = raw39824step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node263 node263Labels := by rfl

theorem canonical39825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39825 raw39825Labels = mixedMoment B node246 node246Labels := by
  calc
    mixedMoment B raw39825 raw39825Labels = mixedMoment B raw39825step0 raw39825step0Labels := by
      have hz : ∀ j, raw39825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39825step0 = (fun i j => raw39825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39825step0 raw39825; decide +kernel
      have hl : raw39825step0Labels = raw39825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39825 raw39825Labels permutation434 hz
    mixedMoment B raw39825step0 raw39825step0Labels = mixedMoment B raw39825step1 raw39825step1Labels := by
      have ha : raw39825step1 = (fun i j => raw39825step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39825step1 raw39825step0; decide +kernel
      have hl : raw39825step1Labels = raw39825step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39825step0 raw39825step0Labels permutation101 permutation6
    _ = mixedMoment B node246 node246Labels := by rfl

theorem canonical39826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39826 raw39826Labels = mixedMoment B node177 node177Labels := by
  calc
    mixedMoment B raw39826 raw39826Labels = mixedMoment B raw39826step0 raw39826step0Labels := by
      have hz : ∀ j, raw39826 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39826step0 = (fun i j => raw39826 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39826step0 raw39826; decide +kernel
      have hl : raw39826step0Labels = raw39826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39826 raw39826Labels permutation434 hz
    mixedMoment B raw39826step0 raw39826step0Labels = mixedMoment B raw39826step1 raw39826step1Labels := by
      have ha : raw39826step1 = (fun i j => raw39826step0 (permutation100 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39826step1 raw39826step0; decide +kernel
      have hl : raw39826step1Labels = raw39826step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39826step0 raw39826step0Labels permutation100 permutation6
    _ = mixedMoment B node177 node177Labels := by rfl

theorem canonical39827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39827 raw39827Labels = mixedMoment B node238 node238Labels := by
  calc
    mixedMoment B raw39827 raw39827Labels = mixedMoment B raw39827step0 raw39827step0Labels := by
      have ha : raw39827step0 = (fun i j => raw39827 (permutation431 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39827step0 raw39827; decide +kernel
      have hl : raw39827step0Labels = raw39827Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39827 raw39827Labels permutation431 permutation6
    _ = mixedMoment B node238 node238Labels := by rfl

theorem canonical39828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39828 raw39828Labels = mixedMoment B node165 node165Labels := by
  calc
    mixedMoment B raw39828 raw39828Labels = mixedMoment B raw39828step0 raw39828step0Labels := by
      have ha : raw39828step0 = (fun i j => raw39828 (permutation430 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39828step0 raw39828; decide +kernel
      have hl : raw39828step0Labels = raw39828Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39828 raw39828Labels permutation430 permutation6
    _ = mixedMoment B node165 node165Labels := by rfl

theorem canonical39829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39829 raw39829Labels = mixedMoment B node263 node263Labels := by
  calc
    mixedMoment B raw39829 raw39829Labels = mixedMoment B raw39829step0 raw39829step0Labels := by
      have hz : ∀ j, raw39829 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39829step0 = (fun i j => raw39829 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39829step0 raw39829; decide +kernel
      have hl : raw39829step0Labels = raw39829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39829 raw39829Labels permutation520 hz
    mixedMoment B raw39829step0 raw39829step0Labels = mixedMoment B raw39829step1 raw39829step1Labels := by
      have ha : raw39829step1 = (fun i j => raw39829step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39829step1 raw39829step0; decide +kernel
      have hl : raw39829step1Labels = raw39829step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39829step0 raw39829step0Labels permutation151 permutation3
    mixedMoment B raw39829step1 raw39829step1Labels = mixedMoment B raw39829step2 raw39829step2Labels := by
      have ha : raw39829step2 = -raw39829step1 := by apply Matrix.ext; change ∀ i j, raw39829step2 i j = -(raw39829step1 i j); unfold raw39829step2 raw39829step1; decide +kernel
      have hl : raw39829step2Labels = raw39829step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node263 node263Labels := by rfl

theorem canonical39830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39830 raw39830Labels = mixedMoment B node463 node463Labels := by
  calc
    mixedMoment B raw39830 raw39830Labels = mixedMoment B raw39830step0 raw39830step0Labels := by
      have ha : raw39830step0 = (fun i j => raw39830 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39830step0 raw39830; decide +kernel
      have hl : raw39830step0Labels = raw39830Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39830 raw39830Labels permutation158 permutation2
    _ = mixedMoment B node463 node463Labels := by rfl

theorem canonical39831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39831 raw39831Labels = mixedMoment B node458 node458Labels := by
  calc
    mixedMoment B raw39831 raw39831Labels = mixedMoment B raw39831step0 raw39831step0Labels := by
      have ha : raw39831step0 = (fun i j => raw39831 (permutation397 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39831step0 raw39831; decide +kernel
      have hl : raw39831step0Labels = raw39831Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39831 raw39831Labels permutation397 permutation6
    _ = mixedMoment B node458 node458Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 352) =
      Integer.Sparse.eval keyMomentRow352 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 352).leftCharge (GramAssembly.key 352).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 346) := by
    have ha : gramCharges (GramAssembly.key 352).leftCharge (GramAssembly.key 352).rightCharge = raw39801 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39801Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39801 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 352).leftCharge (GramAssembly.key 352).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow352, Integer.Sparse.eval]

theorem keyMoment353 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 353) =
      Integer.Sparse.eval keyMomentRow353 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 353).leftCharge (GramAssembly.key 353).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 476) := by
    have ha : gramCharges (GramAssembly.key 353).leftCharge (GramAssembly.key 353).rightCharge = raw39802 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39802Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39802 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 353).leftCharge (GramAssembly.key 353).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow353, Integer.Sparse.eval]

theorem keyMoment354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 354) =
      Integer.Sparse.eval keyMomentRow354 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 354).leftCharge (GramAssembly.key 354).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 484) := by
    have ha : gramCharges (GramAssembly.key 354).leftCharge (GramAssembly.key 354).rightCharge = raw39803 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39803Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39803 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 354).leftCharge (GramAssembly.key 354).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow354, Integer.Sparse.eval]

theorem keyMoment355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 355) =
      Integer.Sparse.eval keyMomentRow355 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 355).leftCharge (GramAssembly.key 355).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 269) := by
    have ha : gramCharges (GramAssembly.key 355).leftCharge (GramAssembly.key 355).rightCharge = raw39804 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39804Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39804 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 355).leftCharge (GramAssembly.key 355).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow355, Integer.Sparse.eval]

theorem keyMoment356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 356) =
      Integer.Sparse.eval keyMomentRow356 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 356).leftCharge (GramAssembly.key 356).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 356).leftCharge (GramAssembly.key 356).rightCharge = raw39805 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39805Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39805 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 356).leftCharge (GramAssembly.key 356).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow356, Integer.Sparse.eval]

theorem keyMoment357 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 357) =
      Integer.Sparse.eval keyMomentRow357 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 357).leftCharge (GramAssembly.key 357).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 468) := by
    have ha : gramCharges (GramAssembly.key 357).leftCharge (GramAssembly.key 357).rightCharge = raw39806 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39806Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39806 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 357).leftCharge (GramAssembly.key 357).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow357, Integer.Sparse.eval]

theorem keyMoment358 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 358) =
      Integer.Sparse.eval keyMomentRow358 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 358).leftCharge (GramAssembly.key 358).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 491) := by
    have ha : gramCharges (GramAssembly.key 358).leftCharge (GramAssembly.key 358).rightCharge = raw39807 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39807Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39807 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 358).leftCharge (GramAssembly.key 358).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow358, Integer.Sparse.eval]

theorem keyMoment359 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 359) =
      Integer.Sparse.eval keyMomentRow359 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 359).leftCharge (GramAssembly.key 359).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 364) := by
    have ha : gramCharges (GramAssembly.key 359).leftCharge (GramAssembly.key 359).rightCharge = raw39808 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39808Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39808 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 359).leftCharge (GramAssembly.key 359).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow359, Integer.Sparse.eval]

theorem keyMoment360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 360) =
      Integer.Sparse.eval keyMomentRow360 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 360).leftCharge (GramAssembly.key 360).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 481) := by
    have ha : gramCharges (GramAssembly.key 360).leftCharge (GramAssembly.key 360).rightCharge = raw39809 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39809Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39809 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 360).leftCharge (GramAssembly.key 360).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow360, Integer.Sparse.eval]

theorem keyMoment361 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 361) =
      Integer.Sparse.eval keyMomentRow361 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 361).leftCharge (GramAssembly.key 361).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 443) := by
    have ha : gramCharges (GramAssembly.key 361).leftCharge (GramAssembly.key 361).rightCharge = raw39810 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39810Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39810 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 361).leftCharge (GramAssembly.key 361).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow361, Integer.Sparse.eval]

theorem keyMoment362 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 362) =
      Integer.Sparse.eval keyMomentRow362 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 362).leftCharge (GramAssembly.key 362).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 440) := by
    have ha : gramCharges (GramAssembly.key 362).leftCharge (GramAssembly.key 362).rightCharge = raw39811 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39811Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39811 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 362).leftCharge (GramAssembly.key 362).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow362, Integer.Sparse.eval]

theorem keyMoment363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 363) =
      Integer.Sparse.eval keyMomentRow363 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 363).leftCharge (GramAssembly.key 363).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 480) := by
    have ha : gramCharges (GramAssembly.key 363).leftCharge (GramAssembly.key 363).rightCharge = raw39812 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39812Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39812 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 363).leftCharge (GramAssembly.key 363).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow363, Integer.Sparse.eval]

theorem keyMoment364 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 364) =
      Integer.Sparse.eval keyMomentRow364 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 364).leftCharge (GramAssembly.key 364).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 492) := by
    have ha : gramCharges (GramAssembly.key 364).leftCharge (GramAssembly.key 364).rightCharge = raw38091 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw38091Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical38091 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 364).leftCharge (GramAssembly.key 364).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow364, Integer.Sparse.eval]

theorem keyMoment365 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 365) =
      Integer.Sparse.eval keyMomentRow365 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 365).leftCharge (GramAssembly.key 365).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 489) := by
    have ha : gramCharges (GramAssembly.key 365).leftCharge (GramAssembly.key 365).rightCharge = raw39813 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39813Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39813 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 365).leftCharge (GramAssembly.key 365).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow365, Integer.Sparse.eval]

theorem keyMoment366 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 366) =
      Integer.Sparse.eval keyMomentRow366 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 366).leftCharge (GramAssembly.key 366).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 478) := by
    have ha : gramCharges (GramAssembly.key 366).leftCharge (GramAssembly.key 366).rightCharge = raw39814 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39814Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39814 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 366).leftCharge (GramAssembly.key 366).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow366, Integer.Sparse.eval]

theorem keyMoment367 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 367) =
      Integer.Sparse.eval keyMomentRow367 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 367).leftCharge (GramAssembly.key 367).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 391) := by
    have ha : gramCharges (GramAssembly.key 367).leftCharge (GramAssembly.key 367).rightCharge = raw39815 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39815Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39815 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 367).leftCharge (GramAssembly.key 367).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow367, Integer.Sparse.eval]

theorem keyMoment368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 368) =
      Integer.Sparse.eval keyMomentRow368 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 368).leftCharge (GramAssembly.key 368).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 148) := by
    have ha : gramCharges (GramAssembly.key 368).leftCharge (GramAssembly.key 368).rightCharge = raw39816 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39816Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39816 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 368).leftCharge (GramAssembly.key 368).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow368, Integer.Sparse.eval]

theorem keyMoment369 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 369) =
      Integer.Sparse.eval keyMomentRow369 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 369).leftCharge (GramAssembly.key 369).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 369).leftCharge (GramAssembly.key 369).rightCharge = raw39817 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39817Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39817 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 369).leftCharge (GramAssembly.key 369).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow369, Integer.Sparse.eval]

theorem keyMoment370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 370) =
      Integer.Sparse.eval keyMomentRow370 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 370).leftCharge (GramAssembly.key 370).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 377) := by
    have ha : gramCharges (GramAssembly.key 370).leftCharge (GramAssembly.key 370).rightCharge = raw39818 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39818Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39818 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 370).leftCharge (GramAssembly.key 370).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow370, Integer.Sparse.eval]

theorem keyMoment371 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 371) =
      Integer.Sparse.eval keyMomentRow371 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 371).leftCharge (GramAssembly.key 371).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 145) := by
    have ha : gramCharges (GramAssembly.key 371).leftCharge (GramAssembly.key 371).rightCharge = raw39819 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39819Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39819 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 371).leftCharge (GramAssembly.key 371).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow371, Integer.Sparse.eval]

theorem keyMoment372 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 372) =
      Integer.Sparse.eval keyMomentRow372 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 372).leftCharge (GramAssembly.key 372).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 139) := by
    have ha : gramCharges (GramAssembly.key 372).leftCharge (GramAssembly.key 372).rightCharge = raw39820 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39820Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39820 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 372).leftCharge (GramAssembly.key 372).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow372, Integer.Sparse.eval]

theorem keyMoment373 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 373) =
      Integer.Sparse.eval keyMomentRow373 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 373).leftCharge (GramAssembly.key 373).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 322) := by
    have ha : gramCharges (GramAssembly.key 373).leftCharge (GramAssembly.key 373).rightCharge = raw39821 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39821Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39821 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 373).leftCharge (GramAssembly.key 373).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow373, Integer.Sparse.eval]

theorem keyMoment374 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 374) =
      Integer.Sparse.eval keyMomentRow374 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 374).leftCharge (GramAssembly.key 374).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 373) := by
    have ha : gramCharges (GramAssembly.key 374).leftCharge (GramAssembly.key 374).rightCharge = raw39822 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39822Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39822 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 374).leftCharge (GramAssembly.key 374).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow374, Integer.Sparse.eval]

theorem keyMoment375 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 375) =
      Integer.Sparse.eval keyMomentRow375 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 375).leftCharge (GramAssembly.key 375).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 264) := by
    have ha : gramCharges (GramAssembly.key 375).leftCharge (GramAssembly.key 375).rightCharge = raw39823 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39823Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39823 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 375).leftCharge (GramAssembly.key 375).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow375, Integer.Sparse.eval]

theorem keyMoment376 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 376) =
      Integer.Sparse.eval keyMomentRow376 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 376).leftCharge (GramAssembly.key 376).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 263) := by
    have ha : gramCharges (GramAssembly.key 376).leftCharge (GramAssembly.key 376).rightCharge = raw39824 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39824Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39824 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 376).leftCharge (GramAssembly.key 376).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow376, Integer.Sparse.eval]

theorem keyMoment377 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 377) =
      Integer.Sparse.eval keyMomentRow377 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 377).leftCharge (GramAssembly.key 377).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 246) := by
    have ha : gramCharges (GramAssembly.key 377).leftCharge (GramAssembly.key 377).rightCharge = raw39825 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39825Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39825 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 377).leftCharge (GramAssembly.key 377).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow377, Integer.Sparse.eval]

theorem keyMoment378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 378) =
      Integer.Sparse.eval keyMomentRow378 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 378).leftCharge (GramAssembly.key 378).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 177) := by
    have ha : gramCharges (GramAssembly.key 378).leftCharge (GramAssembly.key 378).rightCharge = raw39826 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39826Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39826 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 378).leftCharge (GramAssembly.key 378).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow378, Integer.Sparse.eval]

theorem keyMoment379 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 379) =
      Integer.Sparse.eval keyMomentRow379 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 379).leftCharge (GramAssembly.key 379).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 238) := by
    have ha : gramCharges (GramAssembly.key 379).leftCharge (GramAssembly.key 379).rightCharge = raw39827 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39827Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39827 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 379).leftCharge (GramAssembly.key 379).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow379, Integer.Sparse.eval]

theorem keyMoment380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 380) =
      Integer.Sparse.eval keyMomentRow380 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 380).leftCharge (GramAssembly.key 380).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 165) := by
    have ha : gramCharges (GramAssembly.key 380).leftCharge (GramAssembly.key 380).rightCharge = raw39828 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39828Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39828 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 380).leftCharge (GramAssembly.key 380).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow380, Integer.Sparse.eval]

theorem keyMoment381 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 381) =
      Integer.Sparse.eval keyMomentRow381 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 381).leftCharge (GramAssembly.key 381).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 263) := by
    have ha : gramCharges (GramAssembly.key 381).leftCharge (GramAssembly.key 381).rightCharge = raw39829 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39829Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39829 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 381).leftCharge (GramAssembly.key 381).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow381, Integer.Sparse.eval]

theorem keyMoment382 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 382) =
      Integer.Sparse.eval keyMomentRow382 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 382).leftCharge (GramAssembly.key 382).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 463) := by
    have ha : gramCharges (GramAssembly.key 382).leftCharge (GramAssembly.key 382).rightCharge = raw39830 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39830Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39830 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 382).leftCharge (GramAssembly.key 382).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow382, Integer.Sparse.eval]

theorem keyMoment383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 383) =
      Integer.Sparse.eval keyMomentRow383 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 383).leftCharge (GramAssembly.key 383).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 458) := by
    have ha : gramCharges (GramAssembly.key 383).leftCharge (GramAssembly.key 383).rightCharge = raw39831 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39831Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39831 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 383).leftCharge (GramAssembly.key 383).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow383, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt352 : keyMomentRows (352 : Fin 2886) =
    keyMomentRow352 := by decide +kernel

theorem keyMomentRowsAt353 : keyMomentRows (353 : Fin 2886) =
    keyMomentRow353 := by decide +kernel

theorem keyMomentRowsAt354 : keyMomentRows (354 : Fin 2886) =
    keyMomentRow354 := by decide +kernel

theorem keyMomentRowsAt355 : keyMomentRows (355 : Fin 2886) =
    keyMomentRow355 := by decide +kernel

theorem keyMomentRowsAt356 : keyMomentRows (356 : Fin 2886) =
    keyMomentRow356 := by decide +kernel

theorem keyMomentRowsAt357 : keyMomentRows (357 : Fin 2886) =
    keyMomentRow357 := by decide +kernel

theorem keyMomentRowsAt358 : keyMomentRows (358 : Fin 2886) =
    keyMomentRow358 := by decide +kernel

theorem keyMomentRowsAt359 : keyMomentRows (359 : Fin 2886) =
    keyMomentRow359 := by decide +kernel

theorem keyMomentRowsAt360 : keyMomentRows (360 : Fin 2886) =
    keyMomentRow360 := by decide +kernel

theorem keyMomentRowsAt361 : keyMomentRows (361 : Fin 2886) =
    keyMomentRow361 := by decide +kernel

theorem keyMomentRowsAt362 : keyMomentRows (362 : Fin 2886) =
    keyMomentRow362 := by decide +kernel

theorem keyMomentRowsAt363 : keyMomentRows (363 : Fin 2886) =
    keyMomentRow363 := by decide +kernel

theorem keyMomentRowsAt364 : keyMomentRows (364 : Fin 2886) =
    keyMomentRow364 := by decide +kernel

theorem keyMomentRowsAt365 : keyMomentRows (365 : Fin 2886) =
    keyMomentRow365 := by decide +kernel

theorem keyMomentRowsAt366 : keyMomentRows (366 : Fin 2886) =
    keyMomentRow366 := by decide +kernel

theorem keyMomentRowsAt367 : keyMomentRows (367 : Fin 2886) =
    keyMomentRow367 := by decide +kernel

theorem keyMomentRowsAt368 : keyMomentRows (368 : Fin 2886) =
    keyMomentRow368 := by decide +kernel

theorem keyMomentRowsAt369 : keyMomentRows (369 : Fin 2886) =
    keyMomentRow369 := by decide +kernel

theorem keyMomentRowsAt370 : keyMomentRows (370 : Fin 2886) =
    keyMomentRow370 := by decide +kernel

theorem keyMomentRowsAt371 : keyMomentRows (371 : Fin 2886) =
    keyMomentRow371 := by decide +kernel

theorem keyMomentRowsAt372 : keyMomentRows (372 : Fin 2886) =
    keyMomentRow372 := by decide +kernel

theorem keyMomentRowsAt373 : keyMomentRows (373 : Fin 2886) =
    keyMomentRow373 := by decide +kernel

theorem keyMomentRowsAt374 : keyMomentRows (374 : Fin 2886) =
    keyMomentRow374 := by decide +kernel

theorem keyMomentRowsAt375 : keyMomentRows (375 : Fin 2886) =
    keyMomentRow375 := by decide +kernel

theorem keyMomentRowsAt376 : keyMomentRows (376 : Fin 2886) =
    keyMomentRow376 := by decide +kernel

theorem keyMomentRowsAt377 : keyMomentRows (377 : Fin 2886) =
    keyMomentRow377 := by decide +kernel

theorem keyMomentRowsAt378 : keyMomentRows (378 : Fin 2886) =
    keyMomentRow378 := by decide +kernel

theorem keyMomentRowsAt379 : keyMomentRows (379 : Fin 2886) =
    keyMomentRow379 := by decide +kernel

theorem keyMomentRowsAt380 : keyMomentRows (380 : Fin 2886) =
    keyMomentRow380 := by decide +kernel

theorem keyMomentRowsAt381 : keyMomentRows (381 : Fin 2886) =
    keyMomentRow381 := by decide +kernel

theorem keyMomentRowsAt382 : keyMomentRows (382 : Fin 2886) =
    keyMomentRow382 := by decide +kernel

theorem keyMomentRowsAt383 : keyMomentRows (383 : Fin 2886) =
    keyMomentRow383 := by decide +kernel

theorem keyMomentChunkSound11_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 11) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 352 ∨ k.val = 353 ∨ k.val = 354 ∨ k.val = 355 ∨ k.val = 356 ∨ k.val = 357 ∨ k.val = 358 ∨ k.val = 359 ∨ k.val = 360 ∨ k.val = 361 ∨ k.val = 362 ∨ k.val = 363 ∨ k.val = 364 ∨ k.val = 365 ∨ k.val = 366 ∨ k.val = 367 ∨ k.val = 368 ∨ k.val = 369 ∨ k.val = 370 ∨ k.val = 371 ∨ k.val = 372 ∨ k.val = 373 ∨ k.val = 374 ∨ k.val = 375 ∨ k.val = 376 ∨ k.val = 377 ∨ k.val = 378 ∨ k.val = 379 ∨ k.val = 380 ∨ k.val = 381 ∨ k.val = 382 ∨ k.val = 383 := by omega
  rcases heq with h352 | h353 | h354 | h355 | h356 | h357 | h358 | h359 | h360 | h361 | h362 | h363 | h364 | h365 | h366 | h367 | h368 | h369 | h370 | h371 | h372 | h373 | h374 | h375 | h376 | h377 | h378 | h379 | h380 | h381 | h382 | h383
  · have he : k = (352 : Fin 2886) := Fin.ext h352
    subst k
    rw [keyMomentRowsAt352]
    exact keyMoment352 B hB
  · have he : k = (353 : Fin 2886) := Fin.ext h353
    subst k
    rw [keyMomentRowsAt353]
    exact keyMoment353 B hB
  · have he : k = (354 : Fin 2886) := Fin.ext h354
    subst k
    rw [keyMomentRowsAt354]
    exact keyMoment354 B hB
  · have he : k = (355 : Fin 2886) := Fin.ext h355
    subst k
    rw [keyMomentRowsAt355]
    exact keyMoment355 B hB
  · have he : k = (356 : Fin 2886) := Fin.ext h356
    subst k
    rw [keyMomentRowsAt356]
    exact keyMoment356 B hB
  · have he : k = (357 : Fin 2886) := Fin.ext h357
    subst k
    rw [keyMomentRowsAt357]
    exact keyMoment357 B hB
  · have he : k = (358 : Fin 2886) := Fin.ext h358
    subst k
    rw [keyMomentRowsAt358]
    exact keyMoment358 B hB
  · have he : k = (359 : Fin 2886) := Fin.ext h359
    subst k
    rw [keyMomentRowsAt359]
    exact keyMoment359 B hB
  · have he : k = (360 : Fin 2886) := Fin.ext h360
    subst k
    rw [keyMomentRowsAt360]
    exact keyMoment360 B hB
  · have he : k = (361 : Fin 2886) := Fin.ext h361
    subst k
    rw [keyMomentRowsAt361]
    exact keyMoment361 B hB
  · have he : k = (362 : Fin 2886) := Fin.ext h362
    subst k
    rw [keyMomentRowsAt362]
    exact keyMoment362 B hB
  · have he : k = (363 : Fin 2886) := Fin.ext h363
    subst k
    rw [keyMomentRowsAt363]
    exact keyMoment363 B hB
  · have he : k = (364 : Fin 2886) := Fin.ext h364
    subst k
    rw [keyMomentRowsAt364]
    exact keyMoment364 B hB
  · have he : k = (365 : Fin 2886) := Fin.ext h365
    subst k
    rw [keyMomentRowsAt365]
    exact keyMoment365 B hB
  · have he : k = (366 : Fin 2886) := Fin.ext h366
    subst k
    rw [keyMomentRowsAt366]
    exact keyMoment366 B hB
  · have he : k = (367 : Fin 2886) := Fin.ext h367
    subst k
    rw [keyMomentRowsAt367]
    exact keyMoment367 B hB
  · have he : k = (368 : Fin 2886) := Fin.ext h368
    subst k
    rw [keyMomentRowsAt368]
    exact keyMoment368 B hB
  · have he : k = (369 : Fin 2886) := Fin.ext h369
    subst k
    rw [keyMomentRowsAt369]
    exact keyMoment369 B hB
  · have he : k = (370 : Fin 2886) := Fin.ext h370
    subst k
    rw [keyMomentRowsAt370]
    exact keyMoment370 B hB
  · have he : k = (371 : Fin 2886) := Fin.ext h371
    subst k
    rw [keyMomentRowsAt371]
    exact keyMoment371 B hB
  · have he : k = (372 : Fin 2886) := Fin.ext h372
    subst k
    rw [keyMomentRowsAt372]
    exact keyMoment372 B hB
  · have he : k = (373 : Fin 2886) := Fin.ext h373
    subst k
    rw [keyMomentRowsAt373]
    exact keyMoment373 B hB
  · have he : k = (374 : Fin 2886) := Fin.ext h374
    subst k
    rw [keyMomentRowsAt374]
    exact keyMoment374 B hB
  · have he : k = (375 : Fin 2886) := Fin.ext h375
    subst k
    rw [keyMomentRowsAt375]
    exact keyMoment375 B hB
  · have he : k = (376 : Fin 2886) := Fin.ext h376
    subst k
    rw [keyMomentRowsAt376]
    exact keyMoment376 B hB
  · have he : k = (377 : Fin 2886) := Fin.ext h377
    subst k
    rw [keyMomentRowsAt377]
    exact keyMoment377 B hB
  · have he : k = (378 : Fin 2886) := Fin.ext h378
    subst k
    rw [keyMomentRowsAt378]
    exact keyMoment378 B hB
  · have he : k = (379 : Fin 2886) := Fin.ext h379
    subst k
    rw [keyMomentRowsAt379]
    exact keyMoment379 B hB
  · have he : k = (380 : Fin 2886) := Fin.ext h380
    subst k
    rw [keyMomentRowsAt380]
    exact keyMoment380 B hB
  · have he : k = (381 : Fin 2886) := Fin.ext h381
    subst k
    rw [keyMomentRowsAt381]
    exact keyMoment381 B hB
  · have he : k = (382 : Fin 2886) := Fin.ext h382
    subst k
    rw [keyMomentRowsAt382]
    exact keyMoment382 B hB
  · have he : k = (383 : Fin 2886) := Fin.ext h383
    subst k
    rw [keyMomentRowsAt383]
    exact keyMoment383 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound11_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound11_e_oai
