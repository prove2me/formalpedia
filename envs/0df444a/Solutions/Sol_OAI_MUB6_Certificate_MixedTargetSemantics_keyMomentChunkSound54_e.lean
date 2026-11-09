-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound54_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:58:08.143228+00:00
-- url     : https://prove2.me/submissions/676db978-1b39-4d6f-9f6f-8563f28b8a13

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical321
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41141 raw41141Labels = mixedMoment B node584 node584Labels := by
  calc
    mixedMoment B raw41141 raw41141Labels = mixedMoment B raw41141step0 raw41141step0Labels := by
      have hz : ∀ j, raw41141 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41141step0 = (fun i j => raw41141 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41141step0 raw41141; decide +kernel
      have hl : raw41141step0Labels = raw41141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41141 raw41141Labels permutation434 hz
    mixedMoment B raw41141step0 raw41141step0Labels = mixedMoment B raw41141step1 raw41141step1Labels := by
      have hz : ∀ j, raw41141step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41141step1 = (fun i j => raw41141step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41141step1 raw41141step0; decide +kernel
      have hl : raw41141step1Labels = raw41141step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41141step0 raw41141step0Labels permutation80 hz
    mixedMoment B raw41141step1 raw41141step1Labels = mixedMoment B raw41141step2 raw41141step2Labels := by
      have ha : raw41141step2 = (fun i j => raw41141step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41141step2 raw41141step1; decide +kernel
      have hl : raw41141step2Labels = raw41141step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41141step1 raw41141step1Labels permutation31 permutation6
    _ = mixedMoment B node584 node584Labels := by rfl

theorem canonical41142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41142 raw41142Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw41142 raw41142Labels = mixedMoment B raw41142step0 raw41142step0Labels := by
      have hz : ∀ j, raw41142 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41142step0 = (fun i j => raw41142 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41142step0 raw41142; decide +kernel
      have hl : raw41142step0Labels = raw41142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41142 raw41142Labels permutation520 hz
    mixedMoment B raw41142step0 raw41142step0Labels = mixedMoment B raw41142step1 raw41142step1Labels := by
      have hz : ∀ j, raw41142step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41142step1 = (fun i j => raw41142step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41142step1 raw41142step0; decide +kernel
      have hl : raw41142step1Labels = raw41142step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41142step0 raw41142step0Labels permutation104 hz
    mixedMoment B raw41142step1 raw41142step1Labels = mixedMoment B raw41142step2 raw41142step2Labels := by
      have hz : ∀ j, raw41142step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41142step2 = (fun i j => raw41142step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41142step2 raw41142step1; decide +kernel
      have hl : raw41142step2Labels = raw41142step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41142step1 raw41142step1Labels permutation20 hz
    mixedMoment B raw41142step2 raw41142step2Labels = mixedMoment B raw41142step3 raw41142step3Labels := by
      have ha : raw41142step3 = (fun i j => raw41142step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41142step3 raw41142step2; decide +kernel
      have hl : raw41142step3Labels = raw41142step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41142step2 raw41142step2Labels permutation3 permutation6
    mixedMoment B raw41142step3 raw41142step3Labels = mixedMoment B raw41142step4 raw41142step4Labels := by
      have ha : raw41142step4 = -raw41142step3 := by apply Matrix.ext; change ∀ i j, raw41142step4 i j = -(raw41142step3 i j); unfold raw41142step4 raw41142step3; decide +kernel
      have hl : raw41142step4Labels = raw41142step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1297 node1297Labels := by rfl

theorem canonical41143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41143 raw41143Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw41143 raw41143Labels = mixedMoment B raw41143step0 raw41143step0Labels := by
      have hz : ∀ j, raw41143 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41143step0 = (fun i j => raw41143 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41143step0 raw41143; decide +kernel
      have hl : raw41143step0Labels = raw41143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41143 raw41143Labels permutation434 hz
    mixedMoment B raw41143step0 raw41143step0Labels = mixedMoment B raw41143step1 raw41143step1Labels := by
      have hz : ∀ j, raw41143step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41143step1 = (fun i j => raw41143step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41143step1 raw41143step0; decide +kernel
      have hl : raw41143step1Labels = raw41143step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41143step0 raw41143step0Labels permutation80 hz
    mixedMoment B raw41143step1 raw41143step1Labels = mixedMoment B raw41143step2 raw41143step2Labels := by
      have ha : raw41143step2 = (fun i j => raw41143step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41143step2 raw41143step1; decide +kernel
      have hl : raw41143step2Labels = raw41143step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41143step1 raw41143step1Labels permutation11 permutation6
    mixedMoment B raw41143step2 raw41143step2Labels = mixedMoment B raw41143step3 raw41143step3Labels := by
      have ha : raw41143step3 = -raw41143step2 := by apply Matrix.ext; change ∀ i j, raw41143step3 i j = -(raw41143step2 i j); unfold raw41143step3 raw41143step2; decide +kernel
      have hl : raw41143step3Labels = raw41143step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1143 node1143Labels := by rfl

theorem canonical41144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41144 raw41144Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw41144 raw41144Labels = mixedMoment B raw41144step0 raw41144step0Labels := by
      have hz : ∀ j, raw41144 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41144step0 = (fun i j => raw41144 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41144step0 raw41144; decide +kernel
      have hl : raw41144step0Labels = raw41144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41144 raw41144Labels permutation434 hz
    mixedMoment B raw41144step0 raw41144step0Labels = mixedMoment B raw41144step1 raw41144step1Labels := by
      have hz : ∀ j, raw41144step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41144step1 = (fun i j => raw41144step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41144step1 raw41144step0; decide +kernel
      have hl : raw41144step1Labels = raw41144step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41144step0 raw41144step0Labels permutation80 hz
    mixedMoment B raw41144step1 raw41144step1Labels = mixedMoment B raw41144step2 raw41144step2Labels := by
      have ha : raw41144step2 = (fun i j => raw41144step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41144step2 raw41144step1; decide +kernel
      have hl : raw41144step2Labels = raw41144step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41144step1 raw41144step1Labels permutation13 permutation6
    mixedMoment B raw41144step2 raw41144step2Labels = mixedMoment B raw41144step3 raw41144step3Labels := by
      have ha : raw41144step3 = -raw41144step2 := by apply Matrix.ext; change ∀ i j, raw41144step3 i j = -(raw41144step2 i j); unfold raw41144step3 raw41144step2; decide +kernel
      have hl : raw41144step3Labels = raw41144step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1239 node1239Labels := by rfl

theorem canonical41145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41145 raw41145Labels = mixedMoment B node1128 node1128Labels := by
  calc
    mixedMoment B raw41145 raw41145Labels = mixedMoment B raw41145step0 raw41145step0Labels := by
      have hz : ∀ j, raw41145 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41145step0 = (fun i j => raw41145 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41145step0 raw41145; decide +kernel
      have hl : raw41145step0Labels = raw41145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41145 raw41145Labels permutation346 hz
    mixedMoment B raw41145step0 raw41145step0Labels = mixedMoment B raw41145step1 raw41145step1Labels := by
      have ha : raw41145step1 = (fun i j => raw41145step0 (permutation41 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41145step1 raw41145step0; decide +kernel
      have hl : raw41145step1Labels = raw41145step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41145step0 raw41145step0Labels permutation41 permutation6
    mixedMoment B raw41145step1 raw41145step1Labels = mixedMoment B raw41145step2 raw41145step2Labels := by
      have ha : raw41145step2 = -raw41145step1 := by apply Matrix.ext; change ∀ i j, raw41145step2 i j = -(raw41145step1 i j); unfold raw41145step2 raw41145step1; decide +kernel
      have hl : raw41145step2Labels = raw41145step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1128 node1128Labels := by rfl

theorem canonical41146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41146 raw41146Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw41146 raw41146Labels = mixedMoment B raw41146step0 raw41146step0Labels := by
      have hz : ∀ j, raw41146 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41146step0 = (fun i j => raw41146 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41146step0 raw41146; decide +kernel
      have hl : raw41146step0Labels = raw41146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41146 raw41146Labels permutation520 hz
    mixedMoment B raw41146step0 raw41146step0Labels = mixedMoment B raw41146step1 raw41146step1Labels := by
      have hz : ∀ j, raw41146step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41146step1 = (fun i j => raw41146step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41146step1 raw41146step0; decide +kernel
      have hl : raw41146step1Labels = raw41146step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41146step0 raw41146step0Labels permutation104 hz
    mixedMoment B raw41146step1 raw41146step1Labels = mixedMoment B raw41146step2 raw41146step2Labels := by
      have ha : raw41146step2 = (fun i j => raw41146step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41146step2 raw41146step1; decide +kernel
      have hl : raw41146step2Labels = raw41146step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41146step1 raw41146step1Labels permutation13 permutation6
    mixedMoment B raw41146step2 raw41146step2Labels = mixedMoment B raw41146step3 raw41146step3Labels := by
      have ha : raw41146step3 = -raw41146step2 := by apply Matrix.ext; change ∀ i j, raw41146step3 i j = -(raw41146step2 i j); unfold raw41146step3 raw41146step2; decide +kernel
      have hl : raw41146step3Labels = raw41146step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1294 node1294Labels := by rfl

theorem canonical41147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41147 raw41147Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw41147 raw41147Labels = mixedMoment B raw41147step0 raw41147step0Labels := by
      have hz : ∀ j, raw41147 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41147step0 = (fun i j => raw41147 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41147step0 raw41147; decide +kernel
      have hl : raw41147step0Labels = raw41147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41147 raw41147Labels permutation434 hz
    mixedMoment B raw41147step0 raw41147step0Labels = mixedMoment B raw41147step1 raw41147step1Labels := by
      have ha : raw41147step1 = (fun i j => raw41147step0 (permutation47 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41147step1 raw41147step0; decide +kernel
      have hl : raw41147step1Labels = raw41147step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41147step0 raw41147step0Labels permutation47 permutation6
    mixedMoment B raw41147step1 raw41147step1Labels = mixedMoment B raw41147step2 raw41147step2Labels := by
      have ha : raw41147step2 = -raw41147step1 := by apply Matrix.ext; change ∀ i j, raw41147step2 i j = -(raw41147step1 i j); unfold raw41147step2 raw41147step1; decide +kernel
      have hl : raw41147step2Labels = raw41147step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1138 node1138Labels := by rfl

theorem canonical41148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41148 raw41148Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw41148 raw41148Labels = mixedMoment B raw41148step0 raw41148step0Labels := by
      have hz : ∀ j, raw41148 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41148step0 = (fun i j => raw41148 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41148step0 raw41148; decide +kernel
      have hl : raw41148step0Labels = raw41148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41148 raw41148Labels permutation434 hz
    mixedMoment B raw41148step0 raw41148step0Labels = mixedMoment B raw41148step1 raw41148step1Labels := by
      have ha : raw41148step1 = (fun i j => raw41148step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41148step1 raw41148step0; decide +kernel
      have hl : raw41148step1Labels = raw41148step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41148step0 raw41148step0Labels permutation55 permutation6
    mixedMoment B raw41148step1 raw41148step1Labels = mixedMoment B raw41148step2 raw41148step2Labels := by
      have ha : raw41148step2 = -raw41148step1 := by apply Matrix.ext; change ∀ i j, raw41148step2 i j = -(raw41148step1 i j); unfold raw41148step2 raw41148step1; decide +kernel
      have hl : raw41148step2Labels = raw41148step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical41149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41149 raw41149Labels = mixedMoment B node1126 node1126Labels := by
  calc
    mixedMoment B raw41149 raw41149Labels = mixedMoment B raw41149step0 raw41149step0Labels := by
      have ha : raw41149step0 = (fun i j => raw41149 (permutation217 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41149step0 raw41149; decide +kernel
      have hl : raw41149step0Labels = raw41149Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41149 raw41149Labels permutation217 permutation6
    mixedMoment B raw41149step0 raw41149step0Labels = mixedMoment B raw41149step1 raw41149step1Labels := by
      have ha : raw41149step1 = -raw41149step0 := by apply Matrix.ext; change ∀ i j, raw41149step1 i j = -(raw41149step0 i j); unfold raw41149step1 raw41149step0; decide +kernel
      have hl : raw41149step1Labels = raw41149step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1126 node1126Labels := by rfl

theorem canonical41150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41150 raw41150Labels = mixedMoment B node1145 node1145Labels := by
  calc
    mixedMoment B raw41150 raw41150Labels = mixedMoment B raw41150step0 raw41150step0Labels := by
      have hz : ∀ j, raw41150 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41150step0 = (fun i j => raw41150 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41150step0 raw41150; decide +kernel
      have hl : raw41150step0Labels = raw41150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41150 raw41150Labels permutation434 hz
    mixedMoment B raw41150step0 raw41150step0Labels = mixedMoment B raw41150step1 raw41150step1Labels := by
      have hz : ∀ j, raw41150step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41150step1 = (fun i j => raw41150step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41150step1 raw41150step0; decide +kernel
      have hl : raw41150step1Labels = raw41150step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41150step0 raw41150step0Labels permutation80 hz
    mixedMoment B raw41150step1 raw41150step1Labels = mixedMoment B raw41150step2 raw41150step2Labels := by
      have ha : raw41150step2 = (fun i j => raw41150step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41150step2 raw41150step1; decide +kernel
      have hl : raw41150step2Labels = raw41150step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41150step1 raw41150step1Labels permutation10 permutation6
    mixedMoment B raw41150step2 raw41150step2Labels = mixedMoment B raw41150step3 raw41150step3Labels := by
      have ha : raw41150step3 = -raw41150step2 := by apply Matrix.ext; change ∀ i j, raw41150step3 i j = -(raw41150step2 i j); unfold raw41150step3 raw41150step2; decide +kernel
      have hl : raw41150step3Labels = raw41150step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1145 node1145Labels := by rfl

theorem canonical41151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41151 raw41151Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw41151 raw41151Labels = mixedMoment B raw41151step0 raw41151step0Labels := by
      have hz : ∀ j, raw41151 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41151step0 = (fun i j => raw41151 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41151step0 raw41151; decide +kernel
      have hl : raw41151step0Labels = raw41151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41151 raw41151Labels permutation434 hz
    mixedMoment B raw41151step0 raw41151step0Labels = mixedMoment B raw41151step1 raw41151step1Labels := by
      have hz : ∀ j, raw41151step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41151step1 = (fun i j => raw41151step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41151step1 raw41151step0; decide +kernel
      have hl : raw41151step1Labels = raw41151step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41151step0 raw41151step0Labels permutation80 hz
    mixedMoment B raw41151step1 raw41151step1Labels = mixedMoment B raw41151step2 raw41151step2Labels := by
      have ha : raw41151step2 = (fun i j => raw41151step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41151step2 raw41151step1; decide +kernel
      have hl : raw41151step2Labels = raw41151step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41151step1 raw41151step1Labels permutation13 permutation6
    mixedMoment B raw41151step2 raw41151step2Labels = mixedMoment B raw41151step3 raw41151step3Labels := by
      have ha : raw41151step3 = -raw41151step2 := by apply Matrix.ext; change ∀ i j, raw41151step3 i j = -(raw41151step2 i j); unfold raw41151step3 raw41151step2; decide +kernel
      have hl : raw41151step3Labels = raw41151step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1246 node1246Labels := by rfl

theorem canonical41152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41152 raw41152Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw41152 raw41152Labels = mixedMoment B raw41152step0 raw41152step0Labels := by
      have hz : ∀ j, raw41152 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41152step0 = (fun i j => raw41152 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41152step0 raw41152; decide +kernel
      have hl : raw41152step0Labels = raw41152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41152 raw41152Labels permutation346 hz
    mixedMoment B raw41152step0 raw41152step0Labels = mixedMoment B raw41152step1 raw41152step1Labels := by
      have ha : raw41152step1 = (fun i j => raw41152step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41152step1 raw41152step0; decide +kernel
      have hl : raw41152step1Labels = raw41152step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41152step0 raw41152step0Labels permutation43 permutation6
    mixedMoment B raw41152step1 raw41152step1Labels = mixedMoment B raw41152step2 raw41152step2Labels := by
      have ha : raw41152step2 = -raw41152step1 := by apply Matrix.ext; change ∀ i j, raw41152step2 i j = -(raw41152step1 i j); unfold raw41152step2 raw41152step1; decide +kernel
      have hl : raw41152step2Labels = raw41152step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1134 node1134Labels := by rfl

theorem canonical41153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41153 raw41153Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw41153 raw41153Labels = mixedMoment B raw41153step0 raw41153step0Labels := by
      have hz : ∀ j, raw41153 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41153step0 = (fun i j => raw41153 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41153step0 raw41153; decide +kernel
      have hl : raw41153step0Labels = raw41153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41153 raw41153Labels permutation520 hz
    mixedMoment B raw41153step0 raw41153step0Labels = mixedMoment B raw41153step1 raw41153step1Labels := by
      have ha : raw41153step1 = (fun i j => raw41153step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41153step1 raw41153step0; decide +kernel
      have hl : raw41153step1Labels = raw41153step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41153step0 raw41153step0Labels permutation50 permutation6
    mixedMoment B raw41153step1 raw41153step1Labels = mixedMoment B raw41153step2 raw41153step2Labels := by
      have ha : raw41153step2 = -raw41153step1 := by apply Matrix.ext; change ∀ i j, raw41153step2 i j = -(raw41153step1 i j); unfold raw41153step2 raw41153step1; decide +kernel
      have hl : raw41153step2Labels = raw41153step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1293 node1293Labels := by rfl

theorem canonical41154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41154 raw41154Labels = mixedMoment B node1135 node1135Labels := by
  calc
    mixedMoment B raw41154 raw41154Labels = mixedMoment B raw41154step0 raw41154step0Labels := by
      have ha : raw41154step0 = (fun i j => raw41154 (permutation224 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41154step0 raw41154; decide +kernel
      have hl : raw41154step0Labels = raw41154Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41154 raw41154Labels permutation224 permutation6
    mixedMoment B raw41154step0 raw41154step0Labels = mixedMoment B raw41154step1 raw41154step1Labels := by
      have ha : raw41154step1 = -raw41154step0 := by apply Matrix.ext; change ∀ i j, raw41154step1 i j = -(raw41154step0 i j); unfold raw41154step1 raw41154step0; decide +kernel
      have hl : raw41154step1Labels = raw41154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1135 node1135Labels := by rfl

theorem canonical41155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41155 raw41155Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw41155 raw41155Labels = mixedMoment B raw41155step0 raw41155step0Labels := by
      have ha : raw41155step0 = (fun i j => raw41155 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41155step0 raw41155; decide +kernel
      have hl : raw41155step0Labels = raw41155Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41155 raw41155Labels permutation260 permutation6
    mixedMoment B raw41155step0 raw41155step0Labels = mixedMoment B raw41155step1 raw41155step1Labels := by
      have ha : raw41155step1 = -raw41155step0 := by apply Matrix.ext; change ∀ i j, raw41155step1 i j = -(raw41155step0 i j); unfold raw41155step1 raw41155step0; decide +kernel
      have hl : raw41155step1Labels = raw41155step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1235 node1235Labels := by rfl

theorem canonical41156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41156 raw41156Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw41156 raw41156Labels = mixedMoment B raw41156step0 raw41156step0Labels := by
      have hz : ∀ j, raw41156 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41156step0 = (fun i j => raw41156 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41156step0 raw41156; decide +kernel
      have hl : raw41156step0Labels = raw41156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41156 raw41156Labels permutation434 hz
    mixedMoment B raw41156step0 raw41156step0Labels = mixedMoment B raw41156step1 raw41156step1Labels := by
      have ha : raw41156step1 = (fun i j => raw41156step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41156step1 raw41156step0; decide +kernel
      have hl : raw41156step1Labels = raw41156step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41156step0 raw41156step0Labels permutation50 permutation6
    mixedMoment B raw41156step1 raw41156step1Labels = mixedMoment B raw41156step2 raw41156step2Labels := by
      have ha : raw41156step2 = -raw41156step1 := by apply Matrix.ext; change ∀ i j, raw41156step2 i j = -(raw41156step1 i j); unfold raw41156step2 raw41156step1; decide +kernel
      have hl : raw41156step2Labels = raw41156step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical41157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41157 raw41157Labels = mixedMoment B node1129 node1129Labels := by
  calc
    mixedMoment B raw41157 raw41157Labels = mixedMoment B raw41157step0 raw41157step0Labels := by
      have ha : raw41157step0 = (fun i j => raw41157 (permutation218 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41157step0 raw41157; decide +kernel
      have hl : raw41157step0Labels = raw41157Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41157 raw41157Labels permutation218 permutation6
    mixedMoment B raw41157step0 raw41157step0Labels = mixedMoment B raw41157step1 raw41157step1Labels := by
      have ha : raw41157step1 = -raw41157step0 := by apply Matrix.ext; change ∀ i j, raw41157step1 i j = -(raw41157step0 i j); unfold raw41157step1 raw41157step0; decide +kernel
      have hl : raw41157step1Labels = raw41157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1129 node1129Labels := by rfl

theorem canonical41158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41158 raw41158Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw41158 raw41158Labels = mixedMoment B raw41158step0 raw41158step0Labels := by
      have hz : ∀ j, raw41158 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41158step0 = (fun i j => raw41158 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41158step0 raw41158; decide +kernel
      have hl : raw41158step0Labels = raw41158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41158 raw41158Labels permutation434 hz
    mixedMoment B raw41158step0 raw41158step0Labels = mixedMoment B raw41158step1 raw41158step1Labels := by
      have hz : ∀ j, raw41158step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41158step1 = (fun i j => raw41158step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41158step1 raw41158step0; decide +kernel
      have hl : raw41158step1Labels = raw41158step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41158step0 raw41158step0Labels permutation80 hz
    mixedMoment B raw41158step1 raw41158step1Labels = mixedMoment B raw41158step2 raw41158step2Labels := by
      have ha : raw41158step2 = (fun i j => raw41158step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41158step2 raw41158step1; decide +kernel
      have hl : raw41158step2Labels = raw41158step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41158step1 raw41158step1Labels permutation29 permutation6
    _ = mixedMoment B node1140 node1140Labels := by rfl

theorem canonical41159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41159 raw41159Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw41159 raw41159Labels = mixedMoment B raw41159step0 raw41159step0Labels := by
      have hz : ∀ j, raw41159 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41159step0 = (fun i j => raw41159 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41159step0 raw41159; decide +kernel
      have hl : raw41159step0Labels = raw41159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41159 raw41159Labels permutation434 hz
    mixedMoment B raw41159step0 raw41159step0Labels = mixedMoment B raw41159step1 raw41159step1Labels := by
      have hz : ∀ j, raw41159step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41159step1 = (fun i j => raw41159step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41159step1 raw41159step0; decide +kernel
      have hl : raw41159step1Labels = raw41159step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41159step0 raw41159step0Labels permutation80 hz
    mixedMoment B raw41159step1 raw41159step1Labels = mixedMoment B raw41159step2 raw41159step2Labels := by
      have ha : raw41159step2 = (fun i j => raw41159step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41159step2 raw41159step1; decide +kernel
      have hl : raw41159step2Labels = raw41159step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41159step1 raw41159step1Labels permutation12 permutation6
    mixedMoment B raw41159step2 raw41159step2Labels = mixedMoment B raw41159step3 raw41159step3Labels := by
      have ha : raw41159step3 = -raw41159step2 := by apply Matrix.ext; change ∀ i j, raw41159step3 i j = -(raw41159step2 i j); unfold raw41159step3 raw41159step2; decide +kernel
      have hl : raw41159step3Labels = raw41159step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1242 node1242Labels := by rfl

theorem canonical41160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41160 raw41160Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw41160 raw41160Labels = mixedMoment B raw41160step0 raw41160step0Labels := by
      have hz : ∀ j, raw41160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41160step0 = (fun i j => raw41160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41160step0 raw41160; decide +kernel
      have hl : raw41160step0Labels = raw41160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41160 raw41160Labels permutation346 hz
    mixedMoment B raw41160step0 raw41160step0Labels = mixedMoment B raw41160step1 raw41160step1Labels := by
      have ha : raw41160step1 = (fun i j => raw41160step0 (permutation42 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41160step1 raw41160step0; decide +kernel
      have hl : raw41160step1Labels = raw41160step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41160step0 raw41160step0Labels permutation42 permutation6
    mixedMoment B raw41160step1 raw41160step1Labels = mixedMoment B raw41160step2 raw41160step2Labels := by
      have ha : raw41160step2 = -raw41160step1 := by apply Matrix.ext; change ∀ i j, raw41160step2 i j = -(raw41160step1 i j); unfold raw41160step2 raw41160step1; decide +kernel
      have hl : raw41160step2Labels = raw41160step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1131 node1131Labels := by rfl

theorem canonical41161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41161 raw41161Labels = mixedMoment B node1139 node1139Labels := by
  calc
    mixedMoment B raw41161 raw41161Labels = mixedMoment B raw41161step0 raw41161step0Labels := by
      have hz : ∀ j, raw41161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41161step0 = (fun i j => raw41161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41161step0 raw41161; decide +kernel
      have hl : raw41161step0Labels = raw41161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41161 raw41161Labels permutation346 hz
    mixedMoment B raw41161step0 raw41161step0Labels = mixedMoment B raw41161step1 raw41161step1Labels := by
      have ha : raw41161step1 = (fun i j => raw41161step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41161step1 raw41161step0; decide +kernel
      have hl : raw41161step1Labels = raw41161step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41161step0 raw41161step0Labels permutation38 permutation6
    mixedMoment B raw41161step1 raw41161step1Labels = mixedMoment B raw41161step2 raw41161step2Labels := by
      have ha : raw41161step2 = -raw41161step1 := by apply Matrix.ext; change ∀ i j, raw41161step2 i j = -(raw41161step1 i j); unfold raw41161step2 raw41161step1; decide +kernel
      have hl : raw41161step2Labels = raw41161step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1139 node1139Labels := by rfl

theorem canonical41162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41162 raw41162Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw41162 raw41162Labels = mixedMoment B raw41162step0 raw41162step0Labels := by
      have hz : ∀ j, raw41162 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41162step0 = (fun i j => raw41162 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41162step0 raw41162; decide +kernel
      have hl : raw41162step0Labels = raw41162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41162 raw41162Labels permutation434 hz
    mixedMoment B raw41162step0 raw41162step0Labels = mixedMoment B raw41162step1 raw41162step1Labels := by
      have hz : ∀ j, raw41162step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41162step1 = (fun i j => raw41162step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41162step1 raw41162step0; decide +kernel
      have hl : raw41162step1Labels = raw41162step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41162step0 raw41162step0Labels permutation80 hz
    mixedMoment B raw41162step1 raw41162step1Labels = mixedMoment B raw41162step2 raw41162step2Labels := by
      have hz : ∀ j, raw41162step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41162step2 = (fun i j => raw41162step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41162step2 raw41162step1; decide +kernel
      have hl : raw41162step2Labels = raw41162step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41162step1 raw41162step1Labels permutation14 hz
    mixedMoment B raw41162step2 raw41162step2Labels = mixedMoment B raw41162step3 raw41162step3Labels := by
      have ha : raw41162step3 = (fun i j => raw41162step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41162step3 raw41162step2; decide +kernel
      have hl : raw41162step3Labels = raw41162step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41162step2 raw41162step2Labels permutation7 permutation6
    _ = mixedMoment B node615 node615Labels := by rfl

theorem canonical41163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41163 raw41163Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw41163 raw41163Labels = mixedMoment B raw41163step0 raw41163step0Labels := by
      have hz : ∀ j, raw41163 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41163step0 = (fun i j => raw41163 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41163step0 raw41163; decide +kernel
      have hl : raw41163step0Labels = raw41163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41163 raw41163Labels permutation434 hz
    mixedMoment B raw41163step0 raw41163step0Labels = mixedMoment B raw41163step1 raw41163step1Labels := by
      have hz : ∀ j, raw41163step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41163step1 = (fun i j => raw41163step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41163step1 raw41163step0; decide +kernel
      have hl : raw41163step1Labels = raw41163step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41163step0 raw41163step0Labels permutation80 hz
    mixedMoment B raw41163step1 raw41163step1Labels = mixedMoment B raw41163step2 raw41163step2Labels := by
      have hz : ∀ j, raw41163step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41163step2 = (fun i j => raw41163step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41163step2 raw41163step1; decide +kernel
      have hl : raw41163step2Labels = raw41163step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41163step1 raw41163step1Labels permutation14 hz
    mixedMoment B raw41163step2 raw41163step2Labels = mixedMoment B raw41163step3 raw41163step3Labels := by
      have ha : raw41163step3 = (fun i j => raw41163step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41163step3 raw41163step2; decide +kernel
      have hl : raw41163step3Labels = raw41163step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41163step2 raw41163step2Labels permutation5 permutation6
    _ = mixedMoment B node1051 node1051Labels := by rfl

theorem canonical41164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41164 raw41164Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw41164 raw41164Labels = mixedMoment B raw41164step0 raw41164step0Labels := by
      have hz : ∀ j, raw41164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41164step0 = (fun i j => raw41164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41164step0 raw41164; decide +kernel
      have hl : raw41164step0Labels = raw41164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41164 raw41164Labels permutation346 hz
    mixedMoment B raw41164step0 raw41164step0Labels = mixedMoment B raw41164step1 raw41164step1Labels := by
      have hz : ∀ j, raw41164step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41164step1 = (fun i j => raw41164step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41164step1 raw41164step0; decide +kernel
      have hl : raw41164step1Labels = raw41164step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41164step0 raw41164step0Labels permutation56 hz
    mixedMoment B raw41164step1 raw41164step1Labels = mixedMoment B raw41164step2 raw41164step2Labels := by
      have ha : raw41164step2 = (fun i j => raw41164step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41164step2 raw41164step1; decide +kernel
      have hl : raw41164step2Labels = raw41164step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41164step1 raw41164step1Labels permutation25 permutation6
    _ = mixedMoment B node934 node934Labels := by rfl

theorem canonical41165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41165 raw41165Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw41165 raw41165Labels = mixedMoment B raw41165step0 raw41165step0Labels := by
      have hz : ∀ j, raw41165 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41165step0 = (fun i j => raw41165 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41165step0 raw41165; decide +kernel
      have hl : raw41165step0Labels = raw41165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41165 raw41165Labels permutation346 hz
    mixedMoment B raw41165step0 raw41165step0Labels = mixedMoment B raw41165step1 raw41165step1Labels := by
      have hz : ∀ j, raw41165step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41165step1 = (fun i j => raw41165step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41165step1 raw41165step0; decide +kernel
      have hl : raw41165step1Labels = raw41165step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41165step0 raw41165step0Labels permutation56 hz
    mixedMoment B raw41165step1 raw41165step1Labels = mixedMoment B raw41165step2 raw41165step2Labels := by
      have ha : raw41165step2 = (fun i j => raw41165step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41165step2 raw41165step1; decide +kernel
      have hl : raw41165step2Labels = raw41165step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41165step1 raw41165step1Labels permutation9 permutation6
    mixedMoment B raw41165step2 raw41165step2Labels = mixedMoment B raw41165step3 raw41165step3Labels := by
      have ha : raw41165step3 = -raw41165step2 := by apply Matrix.ext; change ∀ i j, raw41165step3 i j = -(raw41165step2 i j); unfold raw41165step3 raw41165step2; decide +kernel
      have hl : raw41165step3Labels = raw41165step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1144 node1144Labels := by rfl

theorem canonical41166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41166 raw41166Labels = mixedMoment B node618 node618Labels := by
  calc
    mixedMoment B raw41166 raw41166Labels = mixedMoment B raw41166step0 raw41166step0Labels := by
      have hz : ∀ j, raw41166 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41166step0 = (fun i j => raw41166 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41166step0 raw41166; decide +kernel
      have hl : raw41166step0Labels = raw41166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41166 raw41166Labels permutation520 hz
    mixedMoment B raw41166step0 raw41166step0Labels = mixedMoment B raw41166step1 raw41166step1Labels := by
      have hz : ∀ j, raw41166step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41166step1 = (fun i j => raw41166step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41166step1 raw41166step0; decide +kernel
      have hl : raw41166step1Labels = raw41166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41166step0 raw41166step0Labels permutation104 hz
    mixedMoment B raw41166step1 raw41166step1Labels = mixedMoment B raw41166step2 raw41166step2Labels := by
      have hz : ∀ j, raw41166step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41166step2 = (fun i j => raw41166step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41166step2 raw41166step1; decide +kernel
      have hl : raw41166step2Labels = raw41166step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41166step1 raw41166step1Labels permutation20 hz
    mixedMoment B raw41166step2 raw41166step2Labels = mixedMoment B raw41166step3 raw41166step3Labels := by
      have ha : raw41166step3 = (fun i j => raw41166step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41166step3 raw41166step2; decide +kernel
      have hl : raw41166step3Labels = raw41166step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41166step2 raw41166step2Labels permutation3 permutation6
    mixedMoment B raw41166step3 raw41166step3Labels = mixedMoment B raw41166step4 raw41166step4Labels := by
      have ha : raw41166step4 = -raw41166step3 := by apply Matrix.ext; change ∀ i j, raw41166step4 i j = -(raw41166step3 i j); unfold raw41166step4 raw41166step3; decide +kernel
      have hl : raw41166step4Labels = raw41166step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node618 node618Labels := by rfl

theorem canonical41167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41167 raw41167Labels = mixedMoment B node613 node613Labels := by
  calc
    mixedMoment B raw41167 raw41167Labels = mixedMoment B raw41167step0 raw41167step0Labels := by
      have hz : ∀ j, raw41167 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41167step0 = (fun i j => raw41167 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41167step0 raw41167; decide +kernel
      have hl : raw41167step0Labels = raw41167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41167 raw41167Labels permutation520 hz
    mixedMoment B raw41167step0 raw41167step0Labels = mixedMoment B raw41167step1 raw41167step1Labels := by
      have hz : ∀ j, raw41167step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41167step1 = (fun i j => raw41167step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41167step1 raw41167step0; decide +kernel
      have hl : raw41167step1Labels = raw41167step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41167step0 raw41167step0Labels permutation104 hz
    mixedMoment B raw41167step1 raw41167step1Labels = mixedMoment B raw41167step2 raw41167step2Labels := by
      have ha : raw41167step2 = (fun i j => raw41167step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41167step2 raw41167step1; decide +kernel
      have hl : raw41167step2Labels = raw41167step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41167step1 raw41167step1Labels permutation11 permutation6
    mixedMoment B raw41167step2 raw41167step2Labels = mixedMoment B raw41167step3 raw41167step3Labels := by
      have ha : raw41167step3 = -raw41167step2 := by apply Matrix.ext; change ∀ i j, raw41167step3 i j = -(raw41167step2 i j); unfold raw41167step3 raw41167step2; decide +kernel
      have hl : raw41167step3Labels = raw41167step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node613 node613Labels := by rfl

theorem canonical41168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41168 raw41168Labels = mixedMoment B node600 node600Labels := by
  calc
    mixedMoment B raw41168 raw41168Labels = mixedMoment B raw41168step0 raw41168step0Labels := by
      have hz : ∀ j, raw41168 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41168step0 = (fun i j => raw41168 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41168step0 raw41168; decide +kernel
      have hl : raw41168step0Labels = raw41168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41168 raw41168Labels permutation434 hz
    mixedMoment B raw41168step0 raw41168step0Labels = mixedMoment B raw41168step1 raw41168step1Labels := by
      have ha : raw41168step1 = (fun i j => raw41168step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41168step1 raw41168step0; decide +kernel
      have hl : raw41168step1Labels = raw41168step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41168step0 raw41168step0Labels permutation49 permutation6
    mixedMoment B raw41168step1 raw41168step1Labels = mixedMoment B raw41168step2 raw41168step2Labels := by
      have ha : raw41168step2 = -raw41168step1 := by apply Matrix.ext; change ∀ i j, raw41168step2 i j = -(raw41168step1 i j); unfold raw41168step2 raw41168step1; decide +kernel
      have hl : raw41168step2Labels = raw41168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node600 node600Labels := by rfl

theorem canonical41169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41169 raw41169Labels = mixedMoment B node620 node620Labels := by
  calc
    mixedMoment B raw41169 raw41169Labels = mixedMoment B raw41169step0 raw41169step0Labels := by
      have hz : ∀ j, raw41169 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41169step0 = (fun i j => raw41169 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41169step0 raw41169; decide +kernel
      have hl : raw41169step0Labels = raw41169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41169 raw41169Labels permutation520 hz
    mixedMoment B raw41169step0 raw41169step0Labels = mixedMoment B raw41169step1 raw41169step1Labels := by
      have hz : ∀ j, raw41169step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41169step1 = (fun i j => raw41169step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41169step1 raw41169step0; decide +kernel
      have hl : raw41169step1Labels = raw41169step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41169step0 raw41169step0Labels permutation104 hz
    mixedMoment B raw41169step1 raw41169step1Labels = mixedMoment B raw41169step2 raw41169step2Labels := by
      have hz : ∀ j, raw41169step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41169step2 = (fun i j => raw41169step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41169step2 raw41169step1; decide +kernel
      have hl : raw41169step2Labels = raw41169step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41169step1 raw41169step1Labels permutation20 hz
    mixedMoment B raw41169step2 raw41169step2Labels = mixedMoment B raw41169step3 raw41169step3Labels := by
      have ha : raw41169step3 = (fun i j => raw41169step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41169step3 raw41169step2; decide +kernel
      have hl : raw41169step3Labels = raw41169step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41169step2 raw41169step2Labels permutation2 permutation6
    mixedMoment B raw41169step3 raw41169step3Labels = mixedMoment B raw41169step4 raw41169step4Labels := by
      have ha : raw41169step4 = -raw41169step3 := by apply Matrix.ext; change ∀ i j, raw41169step4 i j = -(raw41169step3 i j); unfold raw41169step4 raw41169step3; decide +kernel
      have hl : raw41169step4Labels = raw41169step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node620 node620Labels := by rfl

theorem canonical41170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41170 raw41170Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw41170 raw41170Labels = mixedMoment B raw41170step0 raw41170step0Labels := by
      have hz : ∀ j, raw41170 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41170step0 = (fun i j => raw41170 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41170step0 raw41170; decide +kernel
      have hl : raw41170step0Labels = raw41170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41170 raw41170Labels permutation434 hz
    mixedMoment B raw41170step0 raw41170step0Labels = mixedMoment B raw41170step1 raw41170step1Labels := by
      have hz : ∀ j, raw41170step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41170step1 = (fun i j => raw41170step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41170step1 raw41170step0; decide +kernel
      have hl : raw41170step1Labels = raw41170step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41170step0 raw41170step0Labels permutation80 hz
    mixedMoment B raw41170step1 raw41170step1Labels = mixedMoment B raw41170step2 raw41170step2Labels := by
      have ha : raw41170step2 = (fun i j => raw41170step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41170step2 raw41170step1; decide +kernel
      have hl : raw41170step2Labels = raw41170step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41170step1 raw41170step1Labels permutation13 permutation6
    mixedMoment B raw41170step2 raw41170step2Labels = mixedMoment B raw41170step3 raw41170step3Labels := by
      have ha : raw41170step3 = -raw41170step2 := by apply Matrix.ext; change ∀ i j, raw41170step3 i j = -(raw41170step2 i j); unfold raw41170step3 raw41170step2; decide +kernel
      have hl : raw41170step3Labels = raw41170step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node608 node608Labels := by rfl

theorem canonical41171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41171 raw41171Labels = mixedMoment B node610 node610Labels := by
  calc
    mixedMoment B raw41171 raw41171Labels = mixedMoment B raw41171step0 raw41171step0Labels := by
      have hz : ∀ j, raw41171 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41171step0 = (fun i j => raw41171 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41171step0 raw41171; decide +kernel
      have hl : raw41171step0Labels = raw41171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41171 raw41171Labels permutation520 hz
    mixedMoment B raw41171step0 raw41171step0Labels = mixedMoment B raw41171step1 raw41171step1Labels := by
      have ha : raw41171step1 = (fun i j => raw41171step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41171step1 raw41171step0; decide +kernel
      have hl : raw41171step1Labels = raw41171step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41171step0 raw41171step0Labels permutation32 permutation6
    mixedMoment B raw41171step1 raw41171step1Labels = mixedMoment B raw41171step2 raw41171step2Labels := by
      have ha : raw41171step2 = -raw41171step1 := by apply Matrix.ext; change ∀ i j, raw41171step2 i j = -(raw41171step1 i j); unfold raw41171step2 raw41171step1; decide +kernel
      have hl : raw41171step2Labels = raw41171step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node610 node610Labels := by rfl

theorem canonical41172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41172 raw41172Labels = mixedMoment B node599 node599Labels := by
  calc
    mixedMoment B raw41172 raw41172Labels = mixedMoment B raw41172step0 raw41172step0Labels := by
      have ha : raw41172step0 = (fun i j => raw41172 (permutation240 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41172step0 raw41172; decide +kernel
      have hl : raw41172step0Labels = raw41172Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41172 raw41172Labels permutation240 permutation6
    mixedMoment B raw41172step0 raw41172step0Labels = mixedMoment B raw41172step1 raw41172step1Labels := by
      have ha : raw41172step1 = -raw41172step0 := by apply Matrix.ext; change ∀ i j, raw41172step1 i j = -(raw41172step0 i j); unfold raw41172step1 raw41172step0; decide +kernel
      have hl : raw41172step1Labels = raw41172step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node599 node599Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1728 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1728) =
      Integer.Sparse.eval keyMomentRow1728 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1728).leftCharge (GramAssembly.key 1728).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 584) := by
    have ha : gramCharges (GramAssembly.key 1728).leftCharge (GramAssembly.key 1728).rightCharge = raw41141 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41141Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41141 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1728).leftCharge (GramAssembly.key 1728).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1728, Integer.Sparse.eval]

theorem keyMoment1729 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1729) =
      Integer.Sparse.eval keyMomentRow1729 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1729).leftCharge (GramAssembly.key 1729).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1297) := by
    have ha : gramCharges (GramAssembly.key 1729).leftCharge (GramAssembly.key 1729).rightCharge = raw41142 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41142Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41142 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1729).leftCharge (GramAssembly.key 1729).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1729, Integer.Sparse.eval]

theorem keyMoment1730 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1730) =
      Integer.Sparse.eval keyMomentRow1730 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1730).leftCharge (GramAssembly.key 1730).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1143) := by
    have ha : gramCharges (GramAssembly.key 1730).leftCharge (GramAssembly.key 1730).rightCharge = raw41143 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41143Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41143 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1730).leftCharge (GramAssembly.key 1730).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1730, Integer.Sparse.eval]

theorem keyMoment1731 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1731) =
      Integer.Sparse.eval keyMomentRow1731 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1731).leftCharge (GramAssembly.key 1731).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1239) := by
    have ha : gramCharges (GramAssembly.key 1731).leftCharge (GramAssembly.key 1731).rightCharge = raw41144 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41144Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41144 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1731).leftCharge (GramAssembly.key 1731).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1731, Integer.Sparse.eval]

theorem keyMoment1732 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1732) =
      Integer.Sparse.eval keyMomentRow1732 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1732).leftCharge (GramAssembly.key 1732).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1128) := by
    have ha : gramCharges (GramAssembly.key 1732).leftCharge (GramAssembly.key 1732).rightCharge = raw41145 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41145Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41145 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1732).leftCharge (GramAssembly.key 1732).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1732, Integer.Sparse.eval]

theorem keyMoment1733 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1733) =
      Integer.Sparse.eval keyMomentRow1733 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1733).leftCharge (GramAssembly.key 1733).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1294) := by
    have ha : gramCharges (GramAssembly.key 1733).leftCharge (GramAssembly.key 1733).rightCharge = raw41146 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41146Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41146 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1733).leftCharge (GramAssembly.key 1733).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1733, Integer.Sparse.eval]

theorem keyMoment1734 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1734) =
      Integer.Sparse.eval keyMomentRow1734 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1734).leftCharge (GramAssembly.key 1734).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1138) := by
    have ha : gramCharges (GramAssembly.key 1734).leftCharge (GramAssembly.key 1734).rightCharge = raw41147 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41147Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41147 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1734).leftCharge (GramAssembly.key 1734).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1734, Integer.Sparse.eval]

theorem keyMoment1735 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1735) =
      Integer.Sparse.eval keyMomentRow1735 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1735).leftCharge (GramAssembly.key 1735).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1236) := by
    have ha : gramCharges (GramAssembly.key 1735).leftCharge (GramAssembly.key 1735).rightCharge = raw41148 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41148Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41148 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1735).leftCharge (GramAssembly.key 1735).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1735, Integer.Sparse.eval]

theorem keyMoment1736 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1736) =
      Integer.Sparse.eval keyMomentRow1736 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1736).leftCharge (GramAssembly.key 1736).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1126) := by
    have ha : gramCharges (GramAssembly.key 1736).leftCharge (GramAssembly.key 1736).rightCharge = raw41149 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41149Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41149 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1736).leftCharge (GramAssembly.key 1736).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1736, Integer.Sparse.eval]

theorem keyMoment1737 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1737) =
      Integer.Sparse.eval keyMomentRow1737 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1737).leftCharge (GramAssembly.key 1737).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1145) := by
    have ha : gramCharges (GramAssembly.key 1737).leftCharge (GramAssembly.key 1737).rightCharge = raw41150 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41150Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41150 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1737).leftCharge (GramAssembly.key 1737).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1737, Integer.Sparse.eval]

theorem keyMoment1738 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1738) =
      Integer.Sparse.eval keyMomentRow1738 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1738).leftCharge (GramAssembly.key 1738).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1246) := by
    have ha : gramCharges (GramAssembly.key 1738).leftCharge (GramAssembly.key 1738).rightCharge = raw41151 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41151Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41151 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1738).leftCharge (GramAssembly.key 1738).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1738, Integer.Sparse.eval]

theorem keyMoment1739 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1739) =
      Integer.Sparse.eval keyMomentRow1739 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1739).leftCharge (GramAssembly.key 1739).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1134) := by
    have ha : gramCharges (GramAssembly.key 1739).leftCharge (GramAssembly.key 1739).rightCharge = raw41152 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41152Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41152 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1739).leftCharge (GramAssembly.key 1739).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1739, Integer.Sparse.eval]

theorem keyMoment1740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1740) =
      Integer.Sparse.eval keyMomentRow1740 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1740).leftCharge (GramAssembly.key 1740).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1293) := by
    have ha : gramCharges (GramAssembly.key 1740).leftCharge (GramAssembly.key 1740).rightCharge = raw41153 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41153Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41153 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1740).leftCharge (GramAssembly.key 1740).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1740, Integer.Sparse.eval]

theorem keyMoment1741 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1741) =
      Integer.Sparse.eval keyMomentRow1741 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1741).leftCharge (GramAssembly.key 1741).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1135) := by
    have ha : gramCharges (GramAssembly.key 1741).leftCharge (GramAssembly.key 1741).rightCharge = raw41154 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41154Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41154 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1741).leftCharge (GramAssembly.key 1741).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1741, Integer.Sparse.eval]

theorem keyMoment1742 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1742) =
      Integer.Sparse.eval keyMomentRow1742 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1742).leftCharge (GramAssembly.key 1742).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1235) := by
    have ha : gramCharges (GramAssembly.key 1742).leftCharge (GramAssembly.key 1742).rightCharge = raw41155 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41155Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41155 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1742).leftCharge (GramAssembly.key 1742).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1742, Integer.Sparse.eval]

theorem keyMoment1743 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1743) =
      Integer.Sparse.eval keyMomentRow1743 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1743).leftCharge (GramAssembly.key 1743).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1240) := by
    have ha : gramCharges (GramAssembly.key 1743).leftCharge (GramAssembly.key 1743).rightCharge = raw41156 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41156Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41156 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1743).leftCharge (GramAssembly.key 1743).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1743, Integer.Sparse.eval]

theorem keyMoment1744 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1744) =
      Integer.Sparse.eval keyMomentRow1744 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1744).leftCharge (GramAssembly.key 1744).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1129) := by
    have ha : gramCharges (GramAssembly.key 1744).leftCharge (GramAssembly.key 1744).rightCharge = raw41157 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41157Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41157 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1744).leftCharge (GramAssembly.key 1744).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1744, Integer.Sparse.eval]

theorem keyMoment1745 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1745) =
      Integer.Sparse.eval keyMomentRow1745 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1745).leftCharge (GramAssembly.key 1745).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1140) := by
    have ha : gramCharges (GramAssembly.key 1745).leftCharge (GramAssembly.key 1745).rightCharge = raw41158 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41158Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41158 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1745).leftCharge (GramAssembly.key 1745).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1745, Integer.Sparse.eval]

theorem keyMoment1746 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1746) =
      Integer.Sparse.eval keyMomentRow1746 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1746).leftCharge (GramAssembly.key 1746).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1242) := by
    have ha : gramCharges (GramAssembly.key 1746).leftCharge (GramAssembly.key 1746).rightCharge = raw41159 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41159Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41159 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1746).leftCharge (GramAssembly.key 1746).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1746, Integer.Sparse.eval]

theorem keyMoment1747 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1747) =
      Integer.Sparse.eval keyMomentRow1747 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1747).leftCharge (GramAssembly.key 1747).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1131) := by
    have ha : gramCharges (GramAssembly.key 1747).leftCharge (GramAssembly.key 1747).rightCharge = raw41160 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41160Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41160 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1747).leftCharge (GramAssembly.key 1747).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1747, Integer.Sparse.eval]

theorem keyMoment1748 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1748) =
      Integer.Sparse.eval keyMomentRow1748 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1748).leftCharge (GramAssembly.key 1748).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1139) := by
    have ha : gramCharges (GramAssembly.key 1748).leftCharge (GramAssembly.key 1748).rightCharge = raw41161 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41161Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41161 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1748).leftCharge (GramAssembly.key 1748).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1748, Integer.Sparse.eval]

theorem keyMoment1749 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1749) =
      Integer.Sparse.eval keyMomentRow1749 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1749).leftCharge (GramAssembly.key 1749).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 615) := by
    have ha : gramCharges (GramAssembly.key 1749).leftCharge (GramAssembly.key 1749).rightCharge = raw41162 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41162Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41162 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1749).leftCharge (GramAssembly.key 1749).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1749, Integer.Sparse.eval]

theorem keyMoment1750 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1750) =
      Integer.Sparse.eval keyMomentRow1750 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1750).leftCharge (GramAssembly.key 1750).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1051) := by
    have ha : gramCharges (GramAssembly.key 1750).leftCharge (GramAssembly.key 1750).rightCharge = raw41163 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41163Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41163 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1750).leftCharge (GramAssembly.key 1750).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1750, Integer.Sparse.eval]

theorem keyMoment1751 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1751) =
      Integer.Sparse.eval keyMomentRow1751 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1751).leftCharge (GramAssembly.key 1751).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 934) := by
    have ha : gramCharges (GramAssembly.key 1751).leftCharge (GramAssembly.key 1751).rightCharge = raw41164 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41164Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41164 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1751).leftCharge (GramAssembly.key 1751).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1751, Integer.Sparse.eval]

theorem keyMoment1752 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1752) =
      Integer.Sparse.eval keyMomentRow1752 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1752).leftCharge (GramAssembly.key 1752).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1144) := by
    have ha : gramCharges (GramAssembly.key 1752).leftCharge (GramAssembly.key 1752).rightCharge = raw41165 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41165Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41165 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1752).leftCharge (GramAssembly.key 1752).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1752, Integer.Sparse.eval]

theorem keyMoment1753 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1753) =
      Integer.Sparse.eval keyMomentRow1753 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1753).leftCharge (GramAssembly.key 1753).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 618) := by
    have ha : gramCharges (GramAssembly.key 1753).leftCharge (GramAssembly.key 1753).rightCharge = raw41166 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41166Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41166 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1753).leftCharge (GramAssembly.key 1753).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1753, Integer.Sparse.eval]

theorem keyMoment1754 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1754) =
      Integer.Sparse.eval keyMomentRow1754 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1754).leftCharge (GramAssembly.key 1754).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 613) := by
    have ha : gramCharges (GramAssembly.key 1754).leftCharge (GramAssembly.key 1754).rightCharge = raw41167 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41167Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41167 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1754).leftCharge (GramAssembly.key 1754).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1754, Integer.Sparse.eval]

theorem keyMoment1755 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1755) =
      Integer.Sparse.eval keyMomentRow1755 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1755).leftCharge (GramAssembly.key 1755).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 600) := by
    have ha : gramCharges (GramAssembly.key 1755).leftCharge (GramAssembly.key 1755).rightCharge = raw41168 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41168Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41168 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1755).leftCharge (GramAssembly.key 1755).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1755, Integer.Sparse.eval]

theorem keyMoment1756 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1756) =
      Integer.Sparse.eval keyMomentRow1756 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1756).leftCharge (GramAssembly.key 1756).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 620) := by
    have ha : gramCharges (GramAssembly.key 1756).leftCharge (GramAssembly.key 1756).rightCharge = raw41169 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41169Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41169 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1756).leftCharge (GramAssembly.key 1756).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1756, Integer.Sparse.eval]

theorem keyMoment1757 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1757) =
      Integer.Sparse.eval keyMomentRow1757 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1757).leftCharge (GramAssembly.key 1757).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 608) := by
    have ha : gramCharges (GramAssembly.key 1757).leftCharge (GramAssembly.key 1757).rightCharge = raw41170 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41170Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41170 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1757).leftCharge (GramAssembly.key 1757).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1757, Integer.Sparse.eval]

theorem keyMoment1758 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1758) =
      Integer.Sparse.eval keyMomentRow1758 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1758).leftCharge (GramAssembly.key 1758).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 610) := by
    have ha : gramCharges (GramAssembly.key 1758).leftCharge (GramAssembly.key 1758).rightCharge = raw41171 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41171Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41171 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1758).leftCharge (GramAssembly.key 1758).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1758, Integer.Sparse.eval]

theorem keyMoment1759 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1759) =
      Integer.Sparse.eval keyMomentRow1759 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1759).leftCharge (GramAssembly.key 1759).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 599) := by
    have ha : gramCharges (GramAssembly.key 1759).leftCharge (GramAssembly.key 1759).rightCharge = raw41172 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41172Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41172 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1759).leftCharge (GramAssembly.key 1759).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1759, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1728 : keyMomentRows (1728 : Fin 2886) =
    keyMomentRow1728 := by decide +kernel

theorem keyMomentRowsAt1729 : keyMomentRows (1729 : Fin 2886) =
    keyMomentRow1729 := by decide +kernel

theorem keyMomentRowsAt1730 : keyMomentRows (1730 : Fin 2886) =
    keyMomentRow1730 := by decide +kernel

theorem keyMomentRowsAt1731 : keyMomentRows (1731 : Fin 2886) =
    keyMomentRow1731 := by decide +kernel

theorem keyMomentRowsAt1732 : keyMomentRows (1732 : Fin 2886) =
    keyMomentRow1732 := by decide +kernel

theorem keyMomentRowsAt1733 : keyMomentRows (1733 : Fin 2886) =
    keyMomentRow1733 := by decide +kernel

theorem keyMomentRowsAt1734 : keyMomentRows (1734 : Fin 2886) =
    keyMomentRow1734 := by decide +kernel

theorem keyMomentRowsAt1735 : keyMomentRows (1735 : Fin 2886) =
    keyMomentRow1735 := by decide +kernel

theorem keyMomentRowsAt1736 : keyMomentRows (1736 : Fin 2886) =
    keyMomentRow1736 := by decide +kernel

theorem keyMomentRowsAt1737 : keyMomentRows (1737 : Fin 2886) =
    keyMomentRow1737 := by decide +kernel

theorem keyMomentRowsAt1738 : keyMomentRows (1738 : Fin 2886) =
    keyMomentRow1738 := by decide +kernel

theorem keyMomentRowsAt1739 : keyMomentRows (1739 : Fin 2886) =
    keyMomentRow1739 := by decide +kernel

theorem keyMomentRowsAt1740 : keyMomentRows (1740 : Fin 2886) =
    keyMomentRow1740 := by decide +kernel

theorem keyMomentRowsAt1741 : keyMomentRows (1741 : Fin 2886) =
    keyMomentRow1741 := by decide +kernel

theorem keyMomentRowsAt1742 : keyMomentRows (1742 : Fin 2886) =
    keyMomentRow1742 := by decide +kernel

theorem keyMomentRowsAt1743 : keyMomentRows (1743 : Fin 2886) =
    keyMomentRow1743 := by decide +kernel

theorem keyMomentRowsAt1744 : keyMomentRows (1744 : Fin 2886) =
    keyMomentRow1744 := by decide +kernel

theorem keyMomentRowsAt1745 : keyMomentRows (1745 : Fin 2886) =
    keyMomentRow1745 := by decide +kernel

theorem keyMomentRowsAt1746 : keyMomentRows (1746 : Fin 2886) =
    keyMomentRow1746 := by decide +kernel

theorem keyMomentRowsAt1747 : keyMomentRows (1747 : Fin 2886) =
    keyMomentRow1747 := by decide +kernel

theorem keyMomentRowsAt1748 : keyMomentRows (1748 : Fin 2886) =
    keyMomentRow1748 := by decide +kernel

theorem keyMomentRowsAt1749 : keyMomentRows (1749 : Fin 2886) =
    keyMomentRow1749 := by decide +kernel

theorem keyMomentRowsAt1750 : keyMomentRows (1750 : Fin 2886) =
    keyMomentRow1750 := by decide +kernel

theorem keyMomentRowsAt1751 : keyMomentRows (1751 : Fin 2886) =
    keyMomentRow1751 := by decide +kernel

theorem keyMomentRowsAt1752 : keyMomentRows (1752 : Fin 2886) =
    keyMomentRow1752 := by decide +kernel

theorem keyMomentRowsAt1753 : keyMomentRows (1753 : Fin 2886) =
    keyMomentRow1753 := by decide +kernel

theorem keyMomentRowsAt1754 : keyMomentRows (1754 : Fin 2886) =
    keyMomentRow1754 := by decide +kernel

theorem keyMomentRowsAt1755 : keyMomentRows (1755 : Fin 2886) =
    keyMomentRow1755 := by decide +kernel

theorem keyMomentRowsAt1756 : keyMomentRows (1756 : Fin 2886) =
    keyMomentRow1756 := by decide +kernel

theorem keyMomentRowsAt1757 : keyMomentRows (1757 : Fin 2886) =
    keyMomentRow1757 := by decide +kernel

theorem keyMomentRowsAt1758 : keyMomentRows (1758 : Fin 2886) =
    keyMomentRow1758 := by decide +kernel

theorem keyMomentRowsAt1759 : keyMomentRows (1759 : Fin 2886) =
    keyMomentRow1759 := by decide +kernel

theorem keyMomentChunkSound54_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 54) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1728 ∨ k.val = 1729 ∨ k.val = 1730 ∨ k.val = 1731 ∨ k.val = 1732 ∨ k.val = 1733 ∨ k.val = 1734 ∨ k.val = 1735 ∨ k.val = 1736 ∨ k.val = 1737 ∨ k.val = 1738 ∨ k.val = 1739 ∨ k.val = 1740 ∨ k.val = 1741 ∨ k.val = 1742 ∨ k.val = 1743 ∨ k.val = 1744 ∨ k.val = 1745 ∨ k.val = 1746 ∨ k.val = 1747 ∨ k.val = 1748 ∨ k.val = 1749 ∨ k.val = 1750 ∨ k.val = 1751 ∨ k.val = 1752 ∨ k.val = 1753 ∨ k.val = 1754 ∨ k.val = 1755 ∨ k.val = 1756 ∨ k.val = 1757 ∨ k.val = 1758 ∨ k.val = 1759 := by omega
  rcases heq with h1728 | h1729 | h1730 | h1731 | h1732 | h1733 | h1734 | h1735 | h1736 | h1737 | h1738 | h1739 | h1740 | h1741 | h1742 | h1743 | h1744 | h1745 | h1746 | h1747 | h1748 | h1749 | h1750 | h1751 | h1752 | h1753 | h1754 | h1755 | h1756 | h1757 | h1758 | h1759
  · have he : k = (1728 : Fin 2886) := Fin.ext h1728
    subst k
    rw [keyMomentRowsAt1728]
    exact keyMoment1728 B hB
  · have he : k = (1729 : Fin 2886) := Fin.ext h1729
    subst k
    rw [keyMomentRowsAt1729]
    exact keyMoment1729 B hB
  · have he : k = (1730 : Fin 2886) := Fin.ext h1730
    subst k
    rw [keyMomentRowsAt1730]
    exact keyMoment1730 B hB
  · have he : k = (1731 : Fin 2886) := Fin.ext h1731
    subst k
    rw [keyMomentRowsAt1731]
    exact keyMoment1731 B hB
  · have he : k = (1732 : Fin 2886) := Fin.ext h1732
    subst k
    rw [keyMomentRowsAt1732]
    exact keyMoment1732 B hB
  · have he : k = (1733 : Fin 2886) := Fin.ext h1733
    subst k
    rw [keyMomentRowsAt1733]
    exact keyMoment1733 B hB
  · have he : k = (1734 : Fin 2886) := Fin.ext h1734
    subst k
    rw [keyMomentRowsAt1734]
    exact keyMoment1734 B hB
  · have he : k = (1735 : Fin 2886) := Fin.ext h1735
    subst k
    rw [keyMomentRowsAt1735]
    exact keyMoment1735 B hB
  · have he : k = (1736 : Fin 2886) := Fin.ext h1736
    subst k
    rw [keyMomentRowsAt1736]
    exact keyMoment1736 B hB
  · have he : k = (1737 : Fin 2886) := Fin.ext h1737
    subst k
    rw [keyMomentRowsAt1737]
    exact keyMoment1737 B hB
  · have he : k = (1738 : Fin 2886) := Fin.ext h1738
    subst k
    rw [keyMomentRowsAt1738]
    exact keyMoment1738 B hB
  · have he : k = (1739 : Fin 2886) := Fin.ext h1739
    subst k
    rw [keyMomentRowsAt1739]
    exact keyMoment1739 B hB
  · have he : k = (1740 : Fin 2886) := Fin.ext h1740
    subst k
    rw [keyMomentRowsAt1740]
    exact keyMoment1740 B hB
  · have he : k = (1741 : Fin 2886) := Fin.ext h1741
    subst k
    rw [keyMomentRowsAt1741]
    exact keyMoment1741 B hB
  · have he : k = (1742 : Fin 2886) := Fin.ext h1742
    subst k
    rw [keyMomentRowsAt1742]
    exact keyMoment1742 B hB
  · have he : k = (1743 : Fin 2886) := Fin.ext h1743
    subst k
    rw [keyMomentRowsAt1743]
    exact keyMoment1743 B hB
  · have he : k = (1744 : Fin 2886) := Fin.ext h1744
    subst k
    rw [keyMomentRowsAt1744]
    exact keyMoment1744 B hB
  · have he : k = (1745 : Fin 2886) := Fin.ext h1745
    subst k
    rw [keyMomentRowsAt1745]
    exact keyMoment1745 B hB
  · have he : k = (1746 : Fin 2886) := Fin.ext h1746
    subst k
    rw [keyMomentRowsAt1746]
    exact keyMoment1746 B hB
  · have he : k = (1747 : Fin 2886) := Fin.ext h1747
    subst k
    rw [keyMomentRowsAt1747]
    exact keyMoment1747 B hB
  · have he : k = (1748 : Fin 2886) := Fin.ext h1748
    subst k
    rw [keyMomentRowsAt1748]
    exact keyMoment1748 B hB
  · have he : k = (1749 : Fin 2886) := Fin.ext h1749
    subst k
    rw [keyMomentRowsAt1749]
    exact keyMoment1749 B hB
  · have he : k = (1750 : Fin 2886) := Fin.ext h1750
    subst k
    rw [keyMomentRowsAt1750]
    exact keyMoment1750 B hB
  · have he : k = (1751 : Fin 2886) := Fin.ext h1751
    subst k
    rw [keyMomentRowsAt1751]
    exact keyMoment1751 B hB
  · have he : k = (1752 : Fin 2886) := Fin.ext h1752
    subst k
    rw [keyMomentRowsAt1752]
    exact keyMoment1752 B hB
  · have he : k = (1753 : Fin 2886) := Fin.ext h1753
    subst k
    rw [keyMomentRowsAt1753]
    exact keyMoment1753 B hB
  · have he : k = (1754 : Fin 2886) := Fin.ext h1754
    subst k
    rw [keyMomentRowsAt1754]
    exact keyMoment1754 B hB
  · have he : k = (1755 : Fin 2886) := Fin.ext h1755
    subst k
    rw [keyMomentRowsAt1755]
    exact keyMoment1755 B hB
  · have he : k = (1756 : Fin 2886) := Fin.ext h1756
    subst k
    rw [keyMomentRowsAt1756]
    exact keyMoment1756 B hB
  · have he : k = (1757 : Fin 2886) := Fin.ext h1757
    subst k
    rw [keyMomentRowsAt1757]
    exact keyMoment1757 B hB
  · have he : k = (1758 : Fin 2886) := Fin.ext h1758
    subst k
    rw [keyMomentRowsAt1758]
    exact keyMoment1758 B hB
  · have he : k = (1759 : Fin 2886) := Fin.ext h1759
    subst k
    rw [keyMomentRowsAt1759]
    exact keyMoment1759 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound54_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound54_e_oai
