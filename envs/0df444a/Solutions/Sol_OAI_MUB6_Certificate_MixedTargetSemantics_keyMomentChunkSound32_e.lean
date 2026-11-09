-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound32_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:52:07.074603+00:00
-- url     : https://prove2.me/submissions/5826a178-d333-4635-a17b-55e680e7ab56

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical316
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40463 raw40463Labels = mixedMoment B node3164 node3164Labels := by
  calc
    mixedMoment B raw40463 raw40463Labels = mixedMoment B raw40463step0 raw40463step0Labels := by
      have ha : raw40463step0 = (fun i j => raw40463 (permutation252 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40463step0 raw40463; decide +kernel
      have hl : raw40463step0Labels = raw40463Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40463 raw40463Labels permutation252 permutation6
    mixedMoment B raw40463step0 raw40463step0Labels = mixedMoment B raw40463step1 raw40463step1Labels := by
      have ha : raw40463step1 = -raw40463step0 := by apply Matrix.ext; change ∀ i j, raw40463step1 i j = -(raw40463step0 i j); unfold raw40463step1 raw40463step0; decide +kernel
      have hl : raw40463step1Labels = raw40463step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3164 node3164Labels := by rfl

theorem canonical40464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40464 raw40464Labels = mixedMoment B node2423 node2423Labels := by
  calc
    mixedMoment B raw40464 raw40464Labels = mixedMoment B raw40464step0 raw40464step0Labels := by
      have ha : raw40464step0 = (fun i j => raw40464 (permutation463 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40464step0 raw40464; decide +kernel
      have hl : raw40464step0Labels = raw40464Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40464 raw40464Labels permutation463 permutation6
    _ = mixedMoment B node2423 node2423Labels := by rfl

theorem canonical40465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40465 raw40465Labels = mixedMoment B node621 node621Labels := by
  calc
    mixedMoment B raw40465 raw40465Labels = mixedMoment B raw40465step0 raw40465step0Labels := by
      have hz : ∀ j, raw40465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40465step0 = (fun i j => raw40465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40465step0 raw40465; decide +kernel
      have hl : raw40465step0Labels = raw40465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40465 raw40465Labels permutation434 hz
    mixedMoment B raw40465step0 raw40465step0Labels = mixedMoment B raw40465step1 raw40465step1Labels := by
      have hz : ∀ j, raw40465step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40465step1 = (fun i j => raw40465step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40465step1 raw40465step0; decide +kernel
      have hl : raw40465step1Labels = raw40465step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40465step0 raw40465step0Labels permutation80 hz
    mixedMoment B raw40465step1 raw40465step1Labels = mixedMoment B raw40465step2 raw40465step2Labels := by
      have hz : ∀ j, raw40465step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40465step2 = (fun i j => raw40465step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40465step2 raw40465step1; decide +kernel
      have hl : raw40465step2Labels = raw40465step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40465step1 raw40465step1Labels permutation14 hz
    mixedMoment B raw40465step2 raw40465step2Labels = mixedMoment B raw40465step3 raw40465step3Labels := by
      have ha : raw40465step3 = (fun i j => raw40465step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40465step3 raw40465step2; decide +kernel
      have hl : raw40465step3Labels = raw40465step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40465step2 raw40465step2Labels permutation7 permutation6
    _ = mixedMoment B node621 node621Labels := by rfl

theorem canonical40466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40466 raw40466Labels = mixedMoment B node1061 node1061Labels := by
  calc
    mixedMoment B raw40466 raw40466Labels = mixedMoment B raw40466step0 raw40466step0Labels := by
      have hz : ∀ j, raw40466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40466step0 = (fun i j => raw40466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40466step0 raw40466; decide +kernel
      have hl : raw40466step0Labels = raw40466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40466 raw40466Labels permutation346 hz
    mixedMoment B raw40466step0 raw40466step0Labels = mixedMoment B raw40466step1 raw40466step1Labels := by
      have hz : ∀ j, raw40466step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40466step1 = (fun i j => raw40466step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40466step1 raw40466step0; decide +kernel
      have hl : raw40466step1Labels = raw40466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40466step0 raw40466step0Labels permutation56 hz
    mixedMoment B raw40466step1 raw40466step1Labels = mixedMoment B raw40466step2 raw40466step2Labels := by
      have ha : raw40466step2 = (fun i j => raw40466step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40466step2 raw40466step1; decide +kernel
      have hl : raw40466step2Labels = raw40466step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40466step1 raw40466step1Labels permutation25 permutation6
    _ = mixedMoment B node1061 node1061Labels := by rfl

theorem canonical40467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40467 raw40467Labels = mixedMoment B node612 node612Labels := by
  calc
    mixedMoment B raw40467 raw40467Labels = mixedMoment B raw40467step0 raw40467step0Labels := by
      have hz : ∀ j, raw40467 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40467step0 = (fun i j => raw40467 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40467step0 raw40467; decide +kernel
      have hl : raw40467step0Labels = raw40467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40467 raw40467Labels permutation346 hz
    mixedMoment B raw40467step0 raw40467step0Labels = mixedMoment B raw40467step1 raw40467step1Labels := by
      have hz : ∀ j, raw40467step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40467step1 = (fun i j => raw40467step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40467step1 raw40467step0; decide +kernel
      have hl : raw40467step1Labels = raw40467step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40467step0 raw40467step0Labels permutation56 hz
    mixedMoment B raw40467step1 raw40467step1Labels = mixedMoment B raw40467step2 raw40467step2Labels := by
      have ha : raw40467step2 = (fun i j => raw40467step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40467step2 raw40467step1; decide +kernel
      have hl : raw40467step2Labels = raw40467step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40467step1 raw40467step1Labels permutation29 permutation6
    _ = mixedMoment B node612 node612Labels := by rfl

theorem canonical40468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40468 raw40468Labels = mixedMoment B node954 node954Labels := by
  calc
    mixedMoment B raw40468 raw40468Labels = mixedMoment B raw40468step0 raw40468step0Labels := by
      have hz : ∀ j, raw40468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40468step0 = (fun i j => raw40468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40468step0 raw40468; decide +kernel
      have hl : raw40468step0Labels = raw40468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40468 raw40468Labels permutation346 hz
    mixedMoment B raw40468step0 raw40468step0Labels = mixedMoment B raw40468step1 raw40468step1Labels := by
      have hz : ∀ j, raw40468step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40468step1 = (fun i j => raw40468step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40468step1 raw40468step0; decide +kernel
      have hl : raw40468step1Labels = raw40468step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40468step0 raw40468step0Labels permutation56 hz
    mixedMoment B raw40468step1 raw40468step1Labels = mixedMoment B raw40468step2 raw40468step2Labels := by
      have ha : raw40468step2 = (fun i j => raw40468step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40468step2 raw40468step1; decide +kernel
      have hl : raw40468step2Labels = raw40468step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40468step1 raw40468step1Labels permutation25 permutation6
    _ = mixedMoment B node954 node954Labels := by rfl

theorem canonical40469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40469 raw40469Labels = mixedMoment B node590 node590Labels := by
  calc
    mixedMoment B raw40469 raw40469Labels = mixedMoment B raw40469step0 raw40469step0Labels := by
      have hz : ∀ j, raw40469 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40469step0 = (fun i j => raw40469 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40469step0 raw40469; decide +kernel
      have hl : raw40469step0Labels = raw40469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40469 raw40469Labels permutation346 hz
    mixedMoment B raw40469step0 raw40469step0Labels = mixedMoment B raw40469step1 raw40469step1Labels := by
      have hz : ∀ j, raw40469step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40469step1 = (fun i j => raw40469step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40469step1 raw40469step0; decide +kernel
      have hl : raw40469step1Labels = raw40469step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40469step0 raw40469step0Labels permutation56 hz
    mixedMoment B raw40469step1 raw40469step1Labels = mixedMoment B raw40469step2 raw40469step2Labels := by
      have ha : raw40469step2 = (fun i j => raw40469step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40469step2 raw40469step1; decide +kernel
      have hl : raw40469step2Labels = raw40469step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40469step1 raw40469step1Labels permutation31 permutation6
    _ = mixedMoment B node590 node590Labels := by rfl

theorem canonical40470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40470 raw40470Labels = mixedMoment B node940 node940Labels := by
  calc
    mixedMoment B raw40470 raw40470Labels = mixedMoment B raw40470step0 raw40470step0Labels := by
      have hz : ∀ j, raw40470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40470step0 = (fun i j => raw40470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40470step0 raw40470; decide +kernel
      have hl : raw40470step0Labels = raw40470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40470 raw40470Labels permutation346 hz
    mixedMoment B raw40470step0 raw40470step0Labels = mixedMoment B raw40470step1 raw40470step1Labels := by
      have hz : ∀ j, raw40470step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40470step1 = (fun i j => raw40470step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40470step1 raw40470step0; decide +kernel
      have hl : raw40470step1Labels = raw40470step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40470step0 raw40470step0Labels permutation56 hz
    mixedMoment B raw40470step1 raw40470step1Labels = mixedMoment B raw40470step2 raw40470step2Labels := by
      have ha : raw40470step2 = (fun i j => raw40470step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40470step2 raw40470step1; decide +kernel
      have hl : raw40470step2Labels = raw40470step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40470step1 raw40470step1Labels permutation17 permutation6
    _ = mixedMoment B node940 node940Labels := by rfl

theorem canonical40471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40471 raw40471Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw40471 raw40471Labels = mixedMoment B raw40471step0 raw40471step0Labels := by
      have hz : ∀ j, raw40471 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40471step0 = (fun i j => raw40471 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40471step0 raw40471; decide +kernel
      have hl : raw40471step0Labels = raw40471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40471 raw40471Labels permutation346 hz
    mixedMoment B raw40471step0 raw40471step0Labels = mixedMoment B raw40471step1 raw40471step1Labels := by
      have hz : ∀ j, raw40471step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40471step1 = (fun i j => raw40471step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40471step1 raw40471step0; decide +kernel
      have hl : raw40471step1Labels = raw40471step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40471step0 raw40471step0Labels permutation56 hz
    mixedMoment B raw40471step1 raw40471step1Labels = mixedMoment B raw40471step2 raw40471step2Labels := by
      have ha : raw40471step2 = (fun i j => raw40471step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40471step2 raw40471step1; decide +kernel
      have hl : raw40471step2Labels = raw40471step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40471step1 raw40471step1Labels permutation17 permutation6
    _ = mixedMoment B node1047 node1047Labels := by rfl

theorem canonical40472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40472 raw40472Labels = mixedMoment B node2346 node2346Labels := by
  calc
    mixedMoment B raw40472 raw40472Labels = mixedMoment B raw40472step0 raw40472step0Labels := by
      have hz : ∀ j, raw40472 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40472step0 = (fun i j => raw40472 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40472step0 raw40472; decide +kernel
      have hl : raw40472step0Labels = raw40472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40472 raw40472Labels permutation346 hz
    mixedMoment B raw40472step0 raw40472step0Labels = mixedMoment B raw40472step1 raw40472step1Labels := by
      have hz : ∀ j, raw40472step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40472step1 = (fun i j => raw40472step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40472step1 raw40472step0; decide +kernel
      have hl : raw40472step1Labels = raw40472step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40472step0 raw40472step0Labels permutation56 hz
    mixedMoment B raw40472step1 raw40472step1Labels = mixedMoment B raw40472step2 raw40472step2Labels := by
      have ha : raw40472step2 = (fun i j => raw40472step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40472step2 raw40472step1; decide +kernel
      have hl : raw40472step2Labels = raw40472step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40472step1 raw40472step1Labels permutation17 permutation6
    _ = mixedMoment B node2346 node2346Labels := by rfl

theorem canonical40473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40473 raw40473Labels = mixedMoment B node949 node949Labels := by
  calc
    mixedMoment B raw40473 raw40473Labels = mixedMoment B raw40473step0 raw40473step0Labels := by
      have hz : ∀ j, raw40473 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40473step0 = (fun i j => raw40473 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40473step0 raw40473; decide +kernel
      have hl : raw40473step0Labels = raw40473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40473 raw40473Labels permutation265 hz
    mixedMoment B raw40473step0 raw40473step0Labels = mixedMoment B raw40473step1 raw40473step1Labels := by
      have ha : raw40473step1 = (fun i j => raw40473step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40473step1 raw40473step0; decide +kernel
      have hl : raw40473step1Labels = raw40473step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40473step0 raw40473step0Labels permutation125 permutation6
    _ = mixedMoment B node949 node949Labels := by rfl

theorem canonical40474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40474 raw40474Labels = mixedMoment B node585 node585Labels := by
  calc
    mixedMoment B raw40474 raw40474Labels = mixedMoment B raw40474step0 raw40474step0Labels := by
      have hz : ∀ j, raw40474 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40474step0 = (fun i j => raw40474 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40474step0 raw40474; decide +kernel
      have hl : raw40474step0Labels = raw40474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40474 raw40474Labels permutation265 hz
    mixedMoment B raw40474step0 raw40474step0Labels = mixedMoment B raw40474step1 raw40474step1Labels := by
      have ha : raw40474step1 = (fun i j => raw40474step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40474step1 raw40474step0; decide +kernel
      have hl : raw40474step1Labels = raw40474step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40474step0 raw40474step0Labels permutation149 permutation6
    _ = mixedMoment B node585 node585Labels := by rfl

theorem canonical40475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40475 raw40475Labels = mixedMoment B node931 node931Labels := by
  calc
    mixedMoment B raw40475 raw40475Labels = mixedMoment B raw40475step0 raw40475step0Labels := by
      have hz : ∀ j, raw40475 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40475step0 = (fun i j => raw40475 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40475step0 raw40475; decide +kernel
      have hl : raw40475step0Labels = raw40475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40475 raw40475Labels permutation265 hz
    mixedMoment B raw40475step0 raw40475step0Labels = mixedMoment B raw40475step1 raw40475step1Labels := by
      have ha : raw40475step1 = (fun i j => raw40475step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40475step1 raw40475step0; decide +kernel
      have hl : raw40475step1Labels = raw40475step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40475step0 raw40475step0Labels permutation95 permutation6
    _ = mixedMoment B node931 node931Labels := by rfl

theorem canonical40476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40476 raw40476Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw40476 raw40476Labels = mixedMoment B raw40476step0 raw40476step0Labels := by
      have hz : ∀ j, raw40476 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40476step0 = (fun i j => raw40476 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40476step0 raw40476; decide +kernel
      have hl : raw40476step0Labels = raw40476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40476 raw40476Labels permutation265 hz
    mixedMoment B raw40476step0 raw40476step0Labels = mixedMoment B raw40476step1 raw40476step1Labels := by
      have ha : raw40476step1 = (fun i j => raw40476step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40476step1 raw40476step0; decide +kernel
      have hl : raw40476step1Labels = raw40476step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40476step0 raw40476step0Labels permutation97 permutation6
    _ = mixedMoment B node1024 node1024Labels := by rfl

theorem canonical40477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40477 raw40477Labels = mixedMoment B node2340 node2340Labels := by
  calc
    mixedMoment B raw40477 raw40477Labels = mixedMoment B raw40477step0 raw40477step0Labels := by
      have hz : ∀ j, raw40477 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40477step0 = (fun i j => raw40477 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40477step0 raw40477; decide +kernel
      have hl : raw40477step0Labels = raw40477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40477 raw40477Labels permutation265 hz
    mixedMoment B raw40477step0 raw40477step0Labels = mixedMoment B raw40477step1 raw40477step1Labels := by
      have ha : raw40477step1 = (fun i j => raw40477step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40477step1 raw40477step0; decide +kernel
      have hl : raw40477step1Labels = raw40477step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40477step0 raw40477step0Labels permutation95 permutation6
    _ = mixedMoment B node2340 node2340Labels := by rfl

theorem canonical40478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40478 raw40478Labels = mixedMoment B node914 node914Labels := by
  calc
    mixedMoment B raw40478 raw40478Labels = mixedMoment B raw40478step0 raw40478step0Labels := by
      have hz : ∀ j, raw40478 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40478step0 = (fun i j => raw40478 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40478step0 raw40478; decide +kernel
      have hl : raw40478step0Labels = raw40478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40478 raw40478Labels permutation265 hz
    mixedMoment B raw40478step0 raw40478step0Labels = mixedMoment B raw40478step1 raw40478step1Labels := by
      have ha : raw40478step1 = (fun i j => raw40478step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40478step1 raw40478step0; decide +kernel
      have hl : raw40478step1Labels = raw40478step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40478step0 raw40478step0Labels permutation97 permutation6
    _ = mixedMoment B node914 node914Labels := by rfl

theorem canonical40479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40479 raw40479Labels = mixedMoment B node2327 node2327Labels := by
  calc
    mixedMoment B raw40479 raw40479Labels = mixedMoment B raw40479step0 raw40479step0Labels := by
      have hz : ∀ j, raw40479 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40479step0 = (fun i j => raw40479 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40479step0 raw40479; decide +kernel
      have hl : raw40479step0Labels = raw40479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40479 raw40479Labels permutation265 hz
    mixedMoment B raw40479step0 raw40479step0Labels = mixedMoment B raw40479step1 raw40479step1Labels := by
      have ha : raw40479step1 = (fun i j => raw40479step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40479step1 raw40479step0; decide +kernel
      have hl : raw40479step1Labels = raw40479step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40479step0 raw40479step0Labels permutation97 permutation6
    _ = mixedMoment B node2327 node2327Labels := by rfl

theorem canonical40480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40480 raw40480Labels = mixedMoment B node909 node909Labels := by
  calc
    mixedMoment B raw40480 raw40480Labels = mixedMoment B raw40480step0 raw40480step0Labels := by
      have ha : raw40480step0 = (fun i j => raw40480 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40480step0 raw40480; decide +kernel
      have hl : raw40480step0Labels = raw40480Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40480 raw40480Labels permutation502 permutation6
    _ = mixedMoment B node909 node909Labels := by rfl

theorem canonical40481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40481 raw40481Labels = mixedMoment B node2323 node2323Labels := by
  calc
    mixedMoment B raw40481 raw40481Labels = mixedMoment B raw40481step0 raw40481step0Labels := by
      have ha : raw40481step0 = (fun i j => raw40481 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40481step0 raw40481; decide +kernel
      have hl : raw40481step0Labels = raw40481Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40481 raw40481Labels permutation502 permutation6
    _ = mixedMoment B node2323 node2323Labels := by rfl

theorem canonical40482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40482 raw40482Labels = mixedMoment B node1438 node1438Labels := by
  calc
    mixedMoment B raw40482 raw40482Labels = mixedMoment B raw40482step0 raw40482step0Labels := by
      have hz : ∀ j, raw40482 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40482step0 = (fun i j => raw40482 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40482step0 raw40482; decide +kernel
      have hl : raw40482step0Labels = raw40482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40482 raw40482Labels permutation520 hz
    mixedMoment B raw40482step0 raw40482step0Labels = mixedMoment B raw40482step1 raw40482step1Labels := by
      have hz : ∀ j, raw40482step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40482step1 = (fun i j => raw40482step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40482step1 raw40482step0; decide +kernel
      have hl : raw40482step1Labels = raw40482step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40482step0 raw40482step0Labels permutation104 hz
    mixedMoment B raw40482step1 raw40482step1Labels = mixedMoment B raw40482step2 raw40482step2Labels := by
      have hz : ∀ j, raw40482step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40482step2 = (fun i j => raw40482step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40482step2 raw40482step1; decide +kernel
      have hl : raw40482step2Labels = raw40482step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40482step1 raw40482step1Labels permutation20 hz
    mixedMoment B raw40482step2 raw40482step2Labels = mixedMoment B raw40482step3 raw40482step3Labels := by
      have ha : raw40482step3 = (fun i j => raw40482step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40482step3 raw40482step2; decide +kernel
      have hl : raw40482step3Labels = raw40482step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40482step2 raw40482step2Labels permutation3 permutation6
    mixedMoment B raw40482step3 raw40482step3Labels = mixedMoment B raw40482step4 raw40482step4Labels := by
      have ha : raw40482step4 = -raw40482step3 := by apply Matrix.ext; change ∀ i j, raw40482step4 i j = -(raw40482step3 i j); unfold raw40482step4 raw40482step3; decide +kernel
      have hl : raw40482step4Labels = raw40482step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1438 node1438Labels := by rfl

theorem canonical40483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40483 raw40483Labels = mixedMoment B node1348 node1348Labels := by
  calc
    mixedMoment B raw40483 raw40483Labels = mixedMoment B raw40483step0 raw40483step0Labels := by
      have hz : ∀ j, raw40483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40483step0 = (fun i j => raw40483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40483step0 raw40483; decide +kernel
      have hl : raw40483step0Labels = raw40483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40483 raw40483Labels permutation434 hz
    mixedMoment B raw40483step0 raw40483step0Labels = mixedMoment B raw40483step1 raw40483step1Labels := by
      have hz : ∀ j, raw40483step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40483step1 = (fun i j => raw40483step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40483step1 raw40483step0; decide +kernel
      have hl : raw40483step1Labels = raw40483step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40483step0 raw40483step0Labels permutation80 hz
    mixedMoment B raw40483step1 raw40483step1Labels = mixedMoment B raw40483step2 raw40483step2Labels := by
      have ha : raw40483step2 = (fun i j => raw40483step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40483step2 raw40483step1; decide +kernel
      have hl : raw40483step2Labels = raw40483step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40483step1 raw40483step1Labels permutation11 permutation6
    mixedMoment B raw40483step2 raw40483step2Labels = mixedMoment B raw40483step3 raw40483step3Labels := by
      have ha : raw40483step3 = -raw40483step2 := by apply Matrix.ext; change ∀ i j, raw40483step3 i j = -(raw40483step2 i j); unfold raw40483step3 raw40483step2; decide +kernel
      have hl : raw40483step3Labels = raw40483step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1348 node1348Labels := by rfl

theorem canonical40484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40484 raw40484Labels = mixedMoment B node1369 node1369Labels := by
  calc
    mixedMoment B raw40484 raw40484Labels = mixedMoment B raw40484step0 raw40484step0Labels := by
      have hz : ∀ j, raw40484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40484step0 = (fun i j => raw40484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40484step0 raw40484; decide +kernel
      have hl : raw40484step0Labels = raw40484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40484 raw40484Labels permutation434 hz
    mixedMoment B raw40484step0 raw40484step0Labels = mixedMoment B raw40484step1 raw40484step1Labels := by
      have hz : ∀ j, raw40484step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40484step1 = (fun i j => raw40484step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40484step1 raw40484step0; decide +kernel
      have hl : raw40484step1Labels = raw40484step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40484step0 raw40484step0Labels permutation80 hz
    mixedMoment B raw40484step1 raw40484step1Labels = mixedMoment B raw40484step2 raw40484step2Labels := by
      have ha : raw40484step2 = (fun i j => raw40484step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40484step2 raw40484step1; decide +kernel
      have hl : raw40484step2Labels = raw40484step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40484step1 raw40484step1Labels permutation13 permutation6
    mixedMoment B raw40484step2 raw40484step2Labels = mixedMoment B raw40484step3 raw40484step3Labels := by
      have ha : raw40484step3 = -raw40484step2 := by apply Matrix.ext; change ∀ i j, raw40484step3 i j = -(raw40484step2 i j); unfold raw40484step3 raw40484step2; decide +kernel
      have hl : raw40484step3Labels = raw40484step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1369 node1369Labels := by rfl

theorem canonical40485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40485 raw40485Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw40485 raw40485Labels = mixedMoment B raw40485step0 raw40485step0Labels := by
      have hz : ∀ j, raw40485 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40485step0 = (fun i j => raw40485 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40485step0 raw40485; decide +kernel
      have hl : raw40485step0Labels = raw40485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40485 raw40485Labels permutation434 hz
    mixedMoment B raw40485step0 raw40485step0Labels = mixedMoment B raw40485step1 raw40485step1Labels := by
      have hz : ∀ j, raw40485step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40485step1 = (fun i j => raw40485step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40485step1 raw40485step0; decide +kernel
      have hl : raw40485step1Labels = raw40485step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40485step0 raw40485step0Labels permutation80 hz
    mixedMoment B raw40485step1 raw40485step1Labels = mixedMoment B raw40485step2 raw40485step2Labels := by
      have ha : raw40485step2 = (fun i j => raw40485step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40485step2 raw40485step1; decide +kernel
      have hl : raw40485step2Labels = raw40485step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40485step1 raw40485step1Labels permutation11 permutation6
    mixedMoment B raw40485step2 raw40485step2Labels = mixedMoment B raw40485step3 raw40485step3Labels := by
      have ha : raw40485step3 = -raw40485step2 := by apply Matrix.ext; change ∀ i j, raw40485step3 i j = -(raw40485step2 i j); unfold raw40485step3 raw40485step2; decide +kernel
      have hl : raw40485step3Labels = raw40485step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1408 node1408Labels := by rfl

theorem canonical40486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40486 raw40486Labels = mixedMoment B node1323 node1323Labels := by
  calc
    mixedMoment B raw40486 raw40486Labels = mixedMoment B raw40486step0 raw40486step0Labels := by
      have hz : ∀ j, raw40486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40486step0 = (fun i j => raw40486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40486step0 raw40486; decide +kernel
      have hl : raw40486step0Labels = raw40486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40486 raw40486Labels permutation434 hz
    mixedMoment B raw40486step0 raw40486step0Labels = mixedMoment B raw40486step1 raw40486step1Labels := by
      have hz : ∀ j, raw40486step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40486step1 = (fun i j => raw40486step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40486step1 raw40486step0; decide +kernel
      have hl : raw40486step1Labels = raw40486step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40486step0 raw40486step0Labels permutation80 hz
    mixedMoment B raw40486step1 raw40486step1Labels = mixedMoment B raw40486step2 raw40486step2Labels := by
      have ha : raw40486step2 = (fun i j => raw40486step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40486step2 raw40486step1; decide +kernel
      have hl : raw40486step2Labels = raw40486step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40486step1 raw40486step1Labels permutation11 permutation6
    mixedMoment B raw40486step2 raw40486step2Labels = mixedMoment B raw40486step3 raw40486step3Labels := by
      have ha : raw40486step3 = -raw40486step2 := by apply Matrix.ext; change ∀ i j, raw40486step3 i j = -(raw40486step2 i j); unfold raw40486step3 raw40486step2; decide +kernel
      have hl : raw40486step3Labels = raw40486step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1323 node1323Labels := by rfl

theorem canonical40487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40487 raw40487Labels = mixedMoment B node1336 node1336Labels := by
  calc
    mixedMoment B raw40487 raw40487Labels = mixedMoment B raw40487step0 raw40487step0Labels := by
      have hz : ∀ j, raw40487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40487step0 = (fun i j => raw40487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40487step0 raw40487; decide +kernel
      have hl : raw40487step0Labels = raw40487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40487 raw40487Labels permutation346 hz
    mixedMoment B raw40487step0 raw40487step0Labels = mixedMoment B raw40487step1 raw40487step1Labels := by
      have ha : raw40487step1 = (fun i j => raw40487step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40487step1 raw40487step0; decide +kernel
      have hl : raw40487step1Labels = raw40487step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40487step0 raw40487step0Labels permutation43 permutation6
    mixedMoment B raw40487step1 raw40487step1Labels = mixedMoment B raw40487step2 raw40487step2Labels := by
      have ha : raw40487step2 = -raw40487step1 := by apply Matrix.ext; change ∀ i j, raw40487step2 i j = -(raw40487step1 i j); unfold raw40487step2 raw40487step1; decide +kernel
      have hl : raw40487step2Labels = raw40487step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1336 node1336Labels := by rfl

theorem canonical40488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40488 raw40488Labels = mixedMoment B node1332 node1332Labels := by
  calc
    mixedMoment B raw40488 raw40488Labels = mixedMoment B raw40488step0 raw40488step0Labels := by
      have hz : ∀ j, raw40488 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40488step0 = (fun i j => raw40488 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40488step0 raw40488; decide +kernel
      have hl : raw40488step0Labels = raw40488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40488 raw40488Labels permutation346 hz
    mixedMoment B raw40488step0 raw40488step0Labels = mixedMoment B raw40488step1 raw40488step1Labels := by
      have ha : raw40488step1 = (fun i j => raw40488step0 (permutation41 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40488step1 raw40488step0; decide +kernel
      have hl : raw40488step1Labels = raw40488step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40488step0 raw40488step0Labels permutation41 permutation6
    mixedMoment B raw40488step1 raw40488step1Labels = mixedMoment B raw40488step2 raw40488step2Labels := by
      have ha : raw40488step2 = -raw40488step1 := by apply Matrix.ext; change ∀ i j, raw40488step2 i j = -(raw40488step1 i j); unfold raw40488step2 raw40488step1; decide +kernel
      have hl : raw40488step2Labels = raw40488step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1332 node1332Labels := by rfl

theorem canonical40489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40489 raw40489Labels = mixedMoment B node1315 node1315Labels := by
  calc
    mixedMoment B raw40489 raw40489Labels = mixedMoment B raw40489step0 raw40489step0Labels := by
      have hz : ∀ j, raw40489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40489step0 = (fun i j => raw40489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40489step0 raw40489; decide +kernel
      have hl : raw40489step0Labels = raw40489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40489 raw40489Labels permutation346 hz
    mixedMoment B raw40489step0 raw40489step0Labels = mixedMoment B raw40489step1 raw40489step1Labels := by
      have ha : raw40489step1 = (fun i j => raw40489step0 (permutation53 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40489step1 raw40489step0; decide +kernel
      have hl : raw40489step1Labels = raw40489step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40489step0 raw40489step0Labels permutation53 permutation6
    mixedMoment B raw40489step1 raw40489step1Labels = mixedMoment B raw40489step2 raw40489step2Labels := by
      have ha : raw40489step2 = -raw40489step1 := by apply Matrix.ext; change ∀ i j, raw40489step2 i j = -(raw40489step1 i j); unfold raw40489step2 raw40489step1; decide +kernel
      have hl : raw40489step2Labels = raw40489step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1315 node1315Labels := by rfl

theorem canonical40490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40490 raw40490Labels = mixedMoment B node1385 node1385Labels := by
  calc
    mixedMoment B raw40490 raw40490Labels = mixedMoment B raw40490step0 raw40490step0Labels := by
      have hz : ∀ j, raw40490 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40490step0 = (fun i j => raw40490 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40490step0 raw40490; decide +kernel
      have hl : raw40490step0Labels = raw40490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40490 raw40490Labels permutation346 hz
    mixedMoment B raw40490step0 raw40490step0Labels = mixedMoment B raw40490step1 raw40490step1Labels := by
      have ha : raw40490step1 = (fun i j => raw40490step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40490step1 raw40490step0; decide +kernel
      have hl : raw40490step1Labels = raw40490step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40490step0 raw40490step0Labels permutation49 permutation6
    mixedMoment B raw40490step1 raw40490step1Labels = mixedMoment B raw40490step2 raw40490step2Labels := by
      have ha : raw40490step2 = -raw40490step1 := by apply Matrix.ext; change ∀ i j, raw40490step2 i j = -(raw40490step1 i j); unfold raw40490step2 raw40490step1; decide +kernel
      have hl : raw40490step2Labels = raw40490step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1385 node1385Labels := by rfl

theorem canonical40491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40491 raw40491Labels = mixedMoment B node1326 node1326Labels := by
  calc
    mixedMoment B raw40491 raw40491Labels = mixedMoment B raw40491step0 raw40491step0Labels := by
      have ha : raw40491step0 = (fun i j => raw40491 (permutation197 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40491step0 raw40491; decide +kernel
      have hl : raw40491step0Labels = raw40491Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40491 raw40491Labels permutation197 permutation6
    mixedMoment B raw40491step0 raw40491step0Labels = mixedMoment B raw40491step1 raw40491step1Labels := by
      have ha : raw40491step1 = -raw40491step0 := by apply Matrix.ext; change ∀ i j, raw40491step1 i j = -(raw40491step0 i j); unfold raw40491step1 raw40491step0; decide +kernel
      have hl : raw40491step1Labels = raw40491step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1326 node1326Labels := by rfl

theorem canonical40492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40492 raw40492Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw40492 raw40492Labels = mixedMoment B raw40492step0 raw40492step0Labels := by
      have hz : ∀ j, raw40492 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40492step0 = (fun i j => raw40492 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40492step0 raw40492; decide +kernel
      have hl : raw40492step0Labels = raw40492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40492 raw40492Labels permutation520 hz
    mixedMoment B raw40492step0 raw40492step0Labels = mixedMoment B raw40492step1 raw40492step1Labels := by
      have hz : ∀ j, raw40492step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40492step1 = (fun i j => raw40492step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40492step1 raw40492step0; decide +kernel
      have hl : raw40492step1Labels = raw40492step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40492step0 raw40492step0Labels permutation104 hz
    mixedMoment B raw40492step1 raw40492step1Labels = mixedMoment B raw40492step2 raw40492step2Labels := by
      have ha : raw40492step2 = (fun i j => raw40492step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40492step2 raw40492step1; decide +kernel
      have hl : raw40492step2Labels = raw40492step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40492step1 raw40492step1Labels permutation13 permutation6
    mixedMoment B raw40492step2 raw40492step2Labels = mixedMoment B raw40492step3 raw40492step3Labels := by
      have ha : raw40492step3 = -raw40492step2 := by apply Matrix.ext; change ∀ i j, raw40492step3 i j = -(raw40492step2 i j); unfold raw40492step3 raw40492step2; decide +kernel
      have hl : raw40492step3Labels = raw40492step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1436 node1436Labels := by rfl

theorem canonical40493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40493 raw40493Labels = mixedMoment B node1367 node1367Labels := by
  calc
    mixedMoment B raw40493 raw40493Labels = mixedMoment B raw40493step0 raw40493step0Labels := by
      have hz : ∀ j, raw40493 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40493step0 = (fun i j => raw40493 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40493step0 raw40493; decide +kernel
      have hl : raw40493step0Labels = raw40493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40493 raw40493Labels permutation434 hz
    mixedMoment B raw40493step0 raw40493step0Labels = mixedMoment B raw40493step1 raw40493step1Labels := by
      have ha : raw40493step1 = (fun i j => raw40493step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40493step1 raw40493step0; decide +kernel
      have hl : raw40493step1Labels = raw40493step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40493step0 raw40493step0Labels permutation55 permutation6
    mixedMoment B raw40493step1 raw40493step1Labels = mixedMoment B raw40493step2 raw40493step2Labels := by
      have ha : raw40493step2 = -raw40493step1 := by apply Matrix.ext; change ∀ i j, raw40493step2 i j = -(raw40493step1 i j); unfold raw40493step2 raw40493step1; decide +kernel
      have hl : raw40493step2Labels = raw40493step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1367 node1367Labels := by rfl

theorem canonical40494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40494 raw40494Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw40494 raw40494Labels = mixedMoment B raw40494step0 raw40494step0Labels := by
      have hz : ∀ j, raw40494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40494step0 = (fun i j => raw40494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40494step0 raw40494; decide +kernel
      have hl : raw40494step0Labels = raw40494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40494 raw40494Labels permutation434 hz
    mixedMoment B raw40494step0 raw40494step0Labels = mixedMoment B raw40494step1 raw40494step1Labels := by
      have ha : raw40494step1 = (fun i j => raw40494step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40494step1 raw40494step0; decide +kernel
      have hl : raw40494step1Labels = raw40494step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40494step0 raw40494step0Labels permutation49 permutation6
    mixedMoment B raw40494step1 raw40494step1Labels = mixedMoment B raw40494step2 raw40494step2Labels := by
      have ha : raw40494step2 = -raw40494step1 := by apply Matrix.ext; change ∀ i j, raw40494step2 i j = -(raw40494step1 i j); unfold raw40494step2 raw40494step1; decide +kernel
      have hl : raw40494step2Labels = raw40494step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1406 node1406Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1024 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1024) =
      Integer.Sparse.eval keyMomentRow1024 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1024).leftCharge (GramAssembly.key 1024).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3164) := by
    have ha : gramCharges (GramAssembly.key 1024).leftCharge (GramAssembly.key 1024).rightCharge = raw40463 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40463Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40463 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1024).leftCharge (GramAssembly.key 1024).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1024, Integer.Sparse.eval]

theorem keyMoment1025 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1025) =
      Integer.Sparse.eval keyMomentRow1025 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1025).leftCharge (GramAssembly.key 1025).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2423) := by
    have ha : gramCharges (GramAssembly.key 1025).leftCharge (GramAssembly.key 1025).rightCharge = raw40464 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40464Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40464 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1025).leftCharge (GramAssembly.key 1025).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1025, Integer.Sparse.eval]

theorem keyMoment1026 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1026) =
      Integer.Sparse.eval keyMomentRow1026 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1026).leftCharge (GramAssembly.key 1026).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 621) := by
    have ha : gramCharges (GramAssembly.key 1026).leftCharge (GramAssembly.key 1026).rightCharge = raw40465 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40465Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40465 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1026).leftCharge (GramAssembly.key 1026).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1026, Integer.Sparse.eval]

theorem keyMoment1027 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1027) =
      Integer.Sparse.eval keyMomentRow1027 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1027).leftCharge (GramAssembly.key 1027).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1061) := by
    have ha : gramCharges (GramAssembly.key 1027).leftCharge (GramAssembly.key 1027).rightCharge = raw40466 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40466Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40466 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1027).leftCharge (GramAssembly.key 1027).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1027, Integer.Sparse.eval]

theorem keyMoment1028 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1028) =
      Integer.Sparse.eval keyMomentRow1028 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1028).leftCharge (GramAssembly.key 1028).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 612) := by
    have ha : gramCharges (GramAssembly.key 1028).leftCharge (GramAssembly.key 1028).rightCharge = raw40467 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40467Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40467 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1028).leftCharge (GramAssembly.key 1028).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1028, Integer.Sparse.eval]

theorem keyMoment1029 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1029) =
      Integer.Sparse.eval keyMomentRow1029 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1029).leftCharge (GramAssembly.key 1029).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 954) := by
    have ha : gramCharges (GramAssembly.key 1029).leftCharge (GramAssembly.key 1029).rightCharge = raw40468 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40468Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40468 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1029).leftCharge (GramAssembly.key 1029).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1029, Integer.Sparse.eval]

theorem keyMoment1030 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1030) =
      Integer.Sparse.eval keyMomentRow1030 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1030).leftCharge (GramAssembly.key 1030).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 590) := by
    have ha : gramCharges (GramAssembly.key 1030).leftCharge (GramAssembly.key 1030).rightCharge = raw40469 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40469Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40469 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1030).leftCharge (GramAssembly.key 1030).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1030, Integer.Sparse.eval]

theorem keyMoment1031 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1031) =
      Integer.Sparse.eval keyMomentRow1031 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1031).leftCharge (GramAssembly.key 1031).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 940) := by
    have ha : gramCharges (GramAssembly.key 1031).leftCharge (GramAssembly.key 1031).rightCharge = raw40470 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40470Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40470 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1031).leftCharge (GramAssembly.key 1031).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1031, Integer.Sparse.eval]

theorem keyMoment1032 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1032) =
      Integer.Sparse.eval keyMomentRow1032 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1032).leftCharge (GramAssembly.key 1032).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1047) := by
    have ha : gramCharges (GramAssembly.key 1032).leftCharge (GramAssembly.key 1032).rightCharge = raw40471 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40471Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40471 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1032).leftCharge (GramAssembly.key 1032).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1032, Integer.Sparse.eval]

theorem keyMoment1033 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1033) =
      Integer.Sparse.eval keyMomentRow1033 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1033).leftCharge (GramAssembly.key 1033).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2346) := by
    have ha : gramCharges (GramAssembly.key 1033).leftCharge (GramAssembly.key 1033).rightCharge = raw40472 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40472Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40472 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1033).leftCharge (GramAssembly.key 1033).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1033, Integer.Sparse.eval]

theorem keyMoment1034 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1034) =
      Integer.Sparse.eval keyMomentRow1034 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1034).leftCharge (GramAssembly.key 1034).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 949) := by
    have ha : gramCharges (GramAssembly.key 1034).leftCharge (GramAssembly.key 1034).rightCharge = raw40473 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40473Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40473 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1034).leftCharge (GramAssembly.key 1034).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1034, Integer.Sparse.eval]

theorem keyMoment1035 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1035) =
      Integer.Sparse.eval keyMomentRow1035 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1035).leftCharge (GramAssembly.key 1035).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 585) := by
    have ha : gramCharges (GramAssembly.key 1035).leftCharge (GramAssembly.key 1035).rightCharge = raw40474 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40474Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40474 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1035).leftCharge (GramAssembly.key 1035).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1035, Integer.Sparse.eval]

theorem keyMoment1036 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1036) =
      Integer.Sparse.eval keyMomentRow1036 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1036).leftCharge (GramAssembly.key 1036).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 931) := by
    have ha : gramCharges (GramAssembly.key 1036).leftCharge (GramAssembly.key 1036).rightCharge = raw40475 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40475Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40475 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1036).leftCharge (GramAssembly.key 1036).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1036, Integer.Sparse.eval]

theorem keyMoment1037 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1037) =
      Integer.Sparse.eval keyMomentRow1037 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1037).leftCharge (GramAssembly.key 1037).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1024) := by
    have ha : gramCharges (GramAssembly.key 1037).leftCharge (GramAssembly.key 1037).rightCharge = raw40476 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40476Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40476 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1037).leftCharge (GramAssembly.key 1037).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1037, Integer.Sparse.eval]

theorem keyMoment1038 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1038) =
      Integer.Sparse.eval keyMomentRow1038 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1038).leftCharge (GramAssembly.key 1038).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2340) := by
    have ha : gramCharges (GramAssembly.key 1038).leftCharge (GramAssembly.key 1038).rightCharge = raw40477 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40477Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40477 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1038).leftCharge (GramAssembly.key 1038).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1038, Integer.Sparse.eval]

theorem keyMoment1039 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1039) =
      Integer.Sparse.eval keyMomentRow1039 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1039).leftCharge (GramAssembly.key 1039).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 914) := by
    have ha : gramCharges (GramAssembly.key 1039).leftCharge (GramAssembly.key 1039).rightCharge = raw40478 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40478Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40478 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1039).leftCharge (GramAssembly.key 1039).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1039, Integer.Sparse.eval]

theorem keyMoment1040 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1040) =
      Integer.Sparse.eval keyMomentRow1040 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1040).leftCharge (GramAssembly.key 1040).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2327) := by
    have ha : gramCharges (GramAssembly.key 1040).leftCharge (GramAssembly.key 1040).rightCharge = raw40479 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40479Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40479 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1040).leftCharge (GramAssembly.key 1040).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1040, Integer.Sparse.eval]

theorem keyMoment1041 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1041) =
      Integer.Sparse.eval keyMomentRow1041 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1041).leftCharge (GramAssembly.key 1041).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 909) := by
    have ha : gramCharges (GramAssembly.key 1041).leftCharge (GramAssembly.key 1041).rightCharge = raw40480 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40480Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40480 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1041).leftCharge (GramAssembly.key 1041).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1041, Integer.Sparse.eval]

theorem keyMoment1042 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1042) =
      Integer.Sparse.eval keyMomentRow1042 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1042).leftCharge (GramAssembly.key 1042).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2323) := by
    have ha : gramCharges (GramAssembly.key 1042).leftCharge (GramAssembly.key 1042).rightCharge = raw40481 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40481Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40481 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1042).leftCharge (GramAssembly.key 1042).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1042, Integer.Sparse.eval]

theorem keyMoment1043 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1043) =
      Integer.Sparse.eval keyMomentRow1043 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1043).leftCharge (GramAssembly.key 1043).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1438) := by
    have ha : gramCharges (GramAssembly.key 1043).leftCharge (GramAssembly.key 1043).rightCharge = raw40482 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40482Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40482 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1043).leftCharge (GramAssembly.key 1043).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1043, Integer.Sparse.eval]

theorem keyMoment1044 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1044) =
      Integer.Sparse.eval keyMomentRow1044 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1044).leftCharge (GramAssembly.key 1044).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1348) := by
    have ha : gramCharges (GramAssembly.key 1044).leftCharge (GramAssembly.key 1044).rightCharge = raw40483 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40483Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40483 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1044).leftCharge (GramAssembly.key 1044).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1044, Integer.Sparse.eval]

theorem keyMoment1045 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1045) =
      Integer.Sparse.eval keyMomentRow1045 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1045).leftCharge (GramAssembly.key 1045).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1369) := by
    have ha : gramCharges (GramAssembly.key 1045).leftCharge (GramAssembly.key 1045).rightCharge = raw40484 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40484Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40484 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1045).leftCharge (GramAssembly.key 1045).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1045, Integer.Sparse.eval]

theorem keyMoment1046 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1046) =
      Integer.Sparse.eval keyMomentRow1046 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1046).leftCharge (GramAssembly.key 1046).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1408) := by
    have ha : gramCharges (GramAssembly.key 1046).leftCharge (GramAssembly.key 1046).rightCharge = raw40485 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40485Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40485 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1046).leftCharge (GramAssembly.key 1046).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1046, Integer.Sparse.eval]

theorem keyMoment1047 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1047) =
      Integer.Sparse.eval keyMomentRow1047 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1047).leftCharge (GramAssembly.key 1047).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1323) := by
    have ha : gramCharges (GramAssembly.key 1047).leftCharge (GramAssembly.key 1047).rightCharge = raw40486 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40486Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40486 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1047).leftCharge (GramAssembly.key 1047).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1047, Integer.Sparse.eval]

theorem keyMoment1048 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1048) =
      Integer.Sparse.eval keyMomentRow1048 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1048).leftCharge (GramAssembly.key 1048).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1336) := by
    have ha : gramCharges (GramAssembly.key 1048).leftCharge (GramAssembly.key 1048).rightCharge = raw40487 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40487Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40487 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1048).leftCharge (GramAssembly.key 1048).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1048, Integer.Sparse.eval]

theorem keyMoment1049 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1049) =
      Integer.Sparse.eval keyMomentRow1049 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1049).leftCharge (GramAssembly.key 1049).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1332) := by
    have ha : gramCharges (GramAssembly.key 1049).leftCharge (GramAssembly.key 1049).rightCharge = raw40488 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40488Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40488 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1049).leftCharge (GramAssembly.key 1049).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1049, Integer.Sparse.eval]

theorem keyMoment1050 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1050) =
      Integer.Sparse.eval keyMomentRow1050 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1050).leftCharge (GramAssembly.key 1050).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1315) := by
    have ha : gramCharges (GramAssembly.key 1050).leftCharge (GramAssembly.key 1050).rightCharge = raw40489 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40489Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40489 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1050).leftCharge (GramAssembly.key 1050).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1050, Integer.Sparse.eval]

theorem keyMoment1051 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1051) =
      Integer.Sparse.eval keyMomentRow1051 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1051).leftCharge (GramAssembly.key 1051).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1385) := by
    have ha : gramCharges (GramAssembly.key 1051).leftCharge (GramAssembly.key 1051).rightCharge = raw40490 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40490Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40490 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1051).leftCharge (GramAssembly.key 1051).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1051, Integer.Sparse.eval]

theorem keyMoment1052 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1052) =
      Integer.Sparse.eval keyMomentRow1052 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1052).leftCharge (GramAssembly.key 1052).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1326) := by
    have ha : gramCharges (GramAssembly.key 1052).leftCharge (GramAssembly.key 1052).rightCharge = raw40491 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40491Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40491 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1052).leftCharge (GramAssembly.key 1052).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1052, Integer.Sparse.eval]

theorem keyMoment1053 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1053) =
      Integer.Sparse.eval keyMomentRow1053 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1053).leftCharge (GramAssembly.key 1053).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1436) := by
    have ha : gramCharges (GramAssembly.key 1053).leftCharge (GramAssembly.key 1053).rightCharge = raw40492 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40492Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40492 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1053).leftCharge (GramAssembly.key 1053).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1053, Integer.Sparse.eval]

theorem keyMoment1054 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1054) =
      Integer.Sparse.eval keyMomentRow1054 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1054).leftCharge (GramAssembly.key 1054).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1367) := by
    have ha : gramCharges (GramAssembly.key 1054).leftCharge (GramAssembly.key 1054).rightCharge = raw40493 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40493Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40493 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1054).leftCharge (GramAssembly.key 1054).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1054, Integer.Sparse.eval]

theorem keyMoment1055 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1055) =
      Integer.Sparse.eval keyMomentRow1055 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1055).leftCharge (GramAssembly.key 1055).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1406) := by
    have ha : gramCharges (GramAssembly.key 1055).leftCharge (GramAssembly.key 1055).rightCharge = raw40494 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40494Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40494 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1055).leftCharge (GramAssembly.key 1055).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1055, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1024 : keyMomentRows (1024 : Fin 2886) =
    keyMomentRow1024 := by decide +kernel

theorem keyMomentRowsAt1025 : keyMomentRows (1025 : Fin 2886) =
    keyMomentRow1025 := by decide +kernel

theorem keyMomentRowsAt1026 : keyMomentRows (1026 : Fin 2886) =
    keyMomentRow1026 := by decide +kernel

theorem keyMomentRowsAt1027 : keyMomentRows (1027 : Fin 2886) =
    keyMomentRow1027 := by decide +kernel

theorem keyMomentRowsAt1028 : keyMomentRows (1028 : Fin 2886) =
    keyMomentRow1028 := by decide +kernel

theorem keyMomentRowsAt1029 : keyMomentRows (1029 : Fin 2886) =
    keyMomentRow1029 := by decide +kernel

theorem keyMomentRowsAt1030 : keyMomentRows (1030 : Fin 2886) =
    keyMomentRow1030 := by decide +kernel

theorem keyMomentRowsAt1031 : keyMomentRows (1031 : Fin 2886) =
    keyMomentRow1031 := by decide +kernel

theorem keyMomentRowsAt1032 : keyMomentRows (1032 : Fin 2886) =
    keyMomentRow1032 := by decide +kernel

theorem keyMomentRowsAt1033 : keyMomentRows (1033 : Fin 2886) =
    keyMomentRow1033 := by decide +kernel

theorem keyMomentRowsAt1034 : keyMomentRows (1034 : Fin 2886) =
    keyMomentRow1034 := by decide +kernel

theorem keyMomentRowsAt1035 : keyMomentRows (1035 : Fin 2886) =
    keyMomentRow1035 := by decide +kernel

theorem keyMomentRowsAt1036 : keyMomentRows (1036 : Fin 2886) =
    keyMomentRow1036 := by decide +kernel

theorem keyMomentRowsAt1037 : keyMomentRows (1037 : Fin 2886) =
    keyMomentRow1037 := by decide +kernel

theorem keyMomentRowsAt1038 : keyMomentRows (1038 : Fin 2886) =
    keyMomentRow1038 := by decide +kernel

theorem keyMomentRowsAt1039 : keyMomentRows (1039 : Fin 2886) =
    keyMomentRow1039 := by decide +kernel

theorem keyMomentRowsAt1040 : keyMomentRows (1040 : Fin 2886) =
    keyMomentRow1040 := by decide +kernel

theorem keyMomentRowsAt1041 : keyMomentRows (1041 : Fin 2886) =
    keyMomentRow1041 := by decide +kernel

theorem keyMomentRowsAt1042 : keyMomentRows (1042 : Fin 2886) =
    keyMomentRow1042 := by decide +kernel

theorem keyMomentRowsAt1043 : keyMomentRows (1043 : Fin 2886) =
    keyMomentRow1043 := by decide +kernel

theorem keyMomentRowsAt1044 : keyMomentRows (1044 : Fin 2886) =
    keyMomentRow1044 := by decide +kernel

theorem keyMomentRowsAt1045 : keyMomentRows (1045 : Fin 2886) =
    keyMomentRow1045 := by decide +kernel

theorem keyMomentRowsAt1046 : keyMomentRows (1046 : Fin 2886) =
    keyMomentRow1046 := by decide +kernel

theorem keyMomentRowsAt1047 : keyMomentRows (1047 : Fin 2886) =
    keyMomentRow1047 := by decide +kernel

theorem keyMomentRowsAt1048 : keyMomentRows (1048 : Fin 2886) =
    keyMomentRow1048 := by decide +kernel

theorem keyMomentRowsAt1049 : keyMomentRows (1049 : Fin 2886) =
    keyMomentRow1049 := by decide +kernel

theorem keyMomentRowsAt1050 : keyMomentRows (1050 : Fin 2886) =
    keyMomentRow1050 := by decide +kernel

theorem keyMomentRowsAt1051 : keyMomentRows (1051 : Fin 2886) =
    keyMomentRow1051 := by decide +kernel

theorem keyMomentRowsAt1052 : keyMomentRows (1052 : Fin 2886) =
    keyMomentRow1052 := by decide +kernel

theorem keyMomentRowsAt1053 : keyMomentRows (1053 : Fin 2886) =
    keyMomentRow1053 := by decide +kernel

theorem keyMomentRowsAt1054 : keyMomentRows (1054 : Fin 2886) =
    keyMomentRow1054 := by decide +kernel

theorem keyMomentRowsAt1055 : keyMomentRows (1055 : Fin 2886) =
    keyMomentRow1055 := by decide +kernel

theorem keyMomentChunkSound32_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 32) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1024 ∨ k.val = 1025 ∨ k.val = 1026 ∨ k.val = 1027 ∨ k.val = 1028 ∨ k.val = 1029 ∨ k.val = 1030 ∨ k.val = 1031 ∨ k.val = 1032 ∨ k.val = 1033 ∨ k.val = 1034 ∨ k.val = 1035 ∨ k.val = 1036 ∨ k.val = 1037 ∨ k.val = 1038 ∨ k.val = 1039 ∨ k.val = 1040 ∨ k.val = 1041 ∨ k.val = 1042 ∨ k.val = 1043 ∨ k.val = 1044 ∨ k.val = 1045 ∨ k.val = 1046 ∨ k.val = 1047 ∨ k.val = 1048 ∨ k.val = 1049 ∨ k.val = 1050 ∨ k.val = 1051 ∨ k.val = 1052 ∨ k.val = 1053 ∨ k.val = 1054 ∨ k.val = 1055 := by omega
  rcases heq with h1024 | h1025 | h1026 | h1027 | h1028 | h1029 | h1030 | h1031 | h1032 | h1033 | h1034 | h1035 | h1036 | h1037 | h1038 | h1039 | h1040 | h1041 | h1042 | h1043 | h1044 | h1045 | h1046 | h1047 | h1048 | h1049 | h1050 | h1051 | h1052 | h1053 | h1054 | h1055
  · have he : k = (1024 : Fin 2886) := Fin.ext h1024
    subst k
    rw [keyMomentRowsAt1024]
    exact keyMoment1024 B hB
  · have he : k = (1025 : Fin 2886) := Fin.ext h1025
    subst k
    rw [keyMomentRowsAt1025]
    exact keyMoment1025 B hB
  · have he : k = (1026 : Fin 2886) := Fin.ext h1026
    subst k
    rw [keyMomentRowsAt1026]
    exact keyMoment1026 B hB
  · have he : k = (1027 : Fin 2886) := Fin.ext h1027
    subst k
    rw [keyMomentRowsAt1027]
    exact keyMoment1027 B hB
  · have he : k = (1028 : Fin 2886) := Fin.ext h1028
    subst k
    rw [keyMomentRowsAt1028]
    exact keyMoment1028 B hB
  · have he : k = (1029 : Fin 2886) := Fin.ext h1029
    subst k
    rw [keyMomentRowsAt1029]
    exact keyMoment1029 B hB
  · have he : k = (1030 : Fin 2886) := Fin.ext h1030
    subst k
    rw [keyMomentRowsAt1030]
    exact keyMoment1030 B hB
  · have he : k = (1031 : Fin 2886) := Fin.ext h1031
    subst k
    rw [keyMomentRowsAt1031]
    exact keyMoment1031 B hB
  · have he : k = (1032 : Fin 2886) := Fin.ext h1032
    subst k
    rw [keyMomentRowsAt1032]
    exact keyMoment1032 B hB
  · have he : k = (1033 : Fin 2886) := Fin.ext h1033
    subst k
    rw [keyMomentRowsAt1033]
    exact keyMoment1033 B hB
  · have he : k = (1034 : Fin 2886) := Fin.ext h1034
    subst k
    rw [keyMomentRowsAt1034]
    exact keyMoment1034 B hB
  · have he : k = (1035 : Fin 2886) := Fin.ext h1035
    subst k
    rw [keyMomentRowsAt1035]
    exact keyMoment1035 B hB
  · have he : k = (1036 : Fin 2886) := Fin.ext h1036
    subst k
    rw [keyMomentRowsAt1036]
    exact keyMoment1036 B hB
  · have he : k = (1037 : Fin 2886) := Fin.ext h1037
    subst k
    rw [keyMomentRowsAt1037]
    exact keyMoment1037 B hB
  · have he : k = (1038 : Fin 2886) := Fin.ext h1038
    subst k
    rw [keyMomentRowsAt1038]
    exact keyMoment1038 B hB
  · have he : k = (1039 : Fin 2886) := Fin.ext h1039
    subst k
    rw [keyMomentRowsAt1039]
    exact keyMoment1039 B hB
  · have he : k = (1040 : Fin 2886) := Fin.ext h1040
    subst k
    rw [keyMomentRowsAt1040]
    exact keyMoment1040 B hB
  · have he : k = (1041 : Fin 2886) := Fin.ext h1041
    subst k
    rw [keyMomentRowsAt1041]
    exact keyMoment1041 B hB
  · have he : k = (1042 : Fin 2886) := Fin.ext h1042
    subst k
    rw [keyMomentRowsAt1042]
    exact keyMoment1042 B hB
  · have he : k = (1043 : Fin 2886) := Fin.ext h1043
    subst k
    rw [keyMomentRowsAt1043]
    exact keyMoment1043 B hB
  · have he : k = (1044 : Fin 2886) := Fin.ext h1044
    subst k
    rw [keyMomentRowsAt1044]
    exact keyMoment1044 B hB
  · have he : k = (1045 : Fin 2886) := Fin.ext h1045
    subst k
    rw [keyMomentRowsAt1045]
    exact keyMoment1045 B hB
  · have he : k = (1046 : Fin 2886) := Fin.ext h1046
    subst k
    rw [keyMomentRowsAt1046]
    exact keyMoment1046 B hB
  · have he : k = (1047 : Fin 2886) := Fin.ext h1047
    subst k
    rw [keyMomentRowsAt1047]
    exact keyMoment1047 B hB
  · have he : k = (1048 : Fin 2886) := Fin.ext h1048
    subst k
    rw [keyMomentRowsAt1048]
    exact keyMoment1048 B hB
  · have he : k = (1049 : Fin 2886) := Fin.ext h1049
    subst k
    rw [keyMomentRowsAt1049]
    exact keyMoment1049 B hB
  · have he : k = (1050 : Fin 2886) := Fin.ext h1050
    subst k
    rw [keyMomentRowsAt1050]
    exact keyMoment1050 B hB
  · have he : k = (1051 : Fin 2886) := Fin.ext h1051
    subst k
    rw [keyMomentRowsAt1051]
    exact keyMoment1051 B hB
  · have he : k = (1052 : Fin 2886) := Fin.ext h1052
    subst k
    rw [keyMomentRowsAt1052]
    exact keyMoment1052 B hB
  · have he : k = (1053 : Fin 2886) := Fin.ext h1053
    subst k
    rw [keyMomentRowsAt1053]
    exact keyMoment1053 B hB
  · have he : k = (1054 : Fin 2886) := Fin.ext h1054
    subst k
    rw [keyMomentRowsAt1054]
    exact keyMoment1054 B hB
  · have he : k = (1055 : Fin 2886) := Fin.ext h1055
    subst k
    rw [keyMomentRowsAt1055]
    exact keyMoment1055 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound32_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound32_e_oai
