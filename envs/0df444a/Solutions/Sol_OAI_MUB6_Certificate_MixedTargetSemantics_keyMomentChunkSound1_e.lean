-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:44:43.635805+00:00
-- url     : https://prove2.me/submissions/e05ff97d-a401-4747-839b-892756c611cd

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E110
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical308
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39482 raw39482Labels = mixedMoment B node414 node414Labels := by
  calc
    mixedMoment B raw39482 raw39482Labels = mixedMoment B raw39482step0 raw39482step0Labels := by
      have hz : ∀ j, raw39482 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39482step0 = (fun i j => raw39482 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39482step0 raw39482; decide +kernel
      have hl : raw39482step0Labels = raw39482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39482 raw39482Labels permutation346 hz
    mixedMoment B raw39482step0 raw39482step0Labels = mixedMoment B raw39482step1 raw39482step1Labels := by
      have hz : ∀ j, raw39482step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39482step1 = (fun i j => raw39482step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39482step1 raw39482step0; decide +kernel
      have hl : raw39482step1Labels = raw39482step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39482step0 raw39482step0Labels permutation56 hz
    mixedMoment B raw39482step1 raw39482step1Labels = mixedMoment B raw39482step2 raw39482step2Labels := by
      have ha : raw39482step2 = (fun i j => raw39482step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39482step2 raw39482step1; decide +kernel
      have hl : raw39482step2Labels = raw39482step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39482step1 raw39482step1Labels permutation8 permutation3
    _ = mixedMoment B node414 node414Labels := by rfl

theorem canonical39483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39483 raw39483Labels = mixedMoment B node400 node400Labels := by
  calc
    mixedMoment B raw39483 raw39483Labels = mixedMoment B raw39483step0 raw39483step0Labels := by
      have hz : ∀ j, raw39483 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39483step0 = (fun i j => raw39483 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39483step0 raw39483; decide +kernel
      have hl : raw39483step0Labels = raw39483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39483 raw39483Labels permutation265 hz
    mixedMoment B raw39483step0 raw39483step0Labels = mixedMoment B raw39483step1 raw39483step1Labels := by
      have ha : raw39483step1 = (fun i j => raw39483step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39483step1 raw39483step0; decide +kernel
      have hl : raw39483step1Labels = raw39483step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39483step0 raw39483step0Labels permutation32 permutation3
    _ = mixedMoment B node400 node400Labels := by rfl

theorem canonical39484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39484 raw39484Labels = mixedMoment B node409 node409Labels := by
  calc
    mixedMoment B raw39484 raw39484Labels = mixedMoment B raw39484step0 raw39484step0Labels := by
      have hz : ∀ j, raw39484 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39484step0 = (fun i j => raw39484 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39484step0 raw39484; decide +kernel
      have hl : raw39484step0Labels = raw39484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39484 raw39484Labels permutation265 hz
    mixedMoment B raw39484step0 raw39484step0Labels = mixedMoment B raw39484step1 raw39484step1Labels := by
      have ha : raw39484step1 = (fun i j => raw39484step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39484step1 raw39484step0; decide +kernel
      have hl : raw39484step1Labels = raw39484step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39484step0 raw39484step0Labels permutation32 permutation3
    _ = mixedMoment B node409 node409Labels := by rfl

theorem canonical39485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39485 raw39485Labels = mixedMoment B node270 node270Labels := by
  calc
    mixedMoment B raw39485 raw39485Labels = mixedMoment B raw39485step0 raw39485step0Labels := by
      have hz : ∀ j, raw39485 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39485step0 = (fun i j => raw39485 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39485step0 raw39485; decide +kernel
      have hl : raw39485step0Labels = raw39485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39485 raw39485Labels permutation520 hz
    mixedMoment B raw39485step0 raw39485step0Labels = mixedMoment B raw39485step1 raw39485step1Labels := by
      have hz : ∀ j, raw39485step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39485step1 = (fun i j => raw39485step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39485step1 raw39485step0; decide +kernel
      have hl : raw39485step1Labels = raw39485step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39485step0 raw39485step0Labels permutation104 hz
    mixedMoment B raw39485step1 raw39485step1Labels = mixedMoment B raw39485step2 raw39485step2Labels := by
      have hz : ∀ j, raw39485step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39485step2 = (fun i j => raw39485step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39485step2 raw39485step1; decide +kernel
      have hl : raw39485step2Labels = raw39485step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39485step1 raw39485step1Labels permutation20 hz
    mixedMoment B raw39485step2 raw39485step2Labels = mixedMoment B raw39485step3 raw39485step3Labels := by
      have ha : raw39485step3 = (fun i j => raw39485step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39485step3 raw39485step2; decide +kernel
      have hl : raw39485step3Labels = raw39485step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39485step2 raw39485step2Labels permutation7 permutation3
    mixedMoment B raw39485step3 raw39485step3Labels = mixedMoment B raw39485step4 raw39485step4Labels := by
      have ha : raw39485step4 = -raw39485step3 := by apply Matrix.ext; change ∀ i j, raw39485step4 i j = -(raw39485step3 i j); unfold raw39485step4 raw39485step3; decide +kernel
      have hl : raw39485step4Labels = raw39485step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node270 node270Labels := by rfl

theorem canonical39486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39486 raw39486Labels = mixedMoment B node391 node391Labels := by
  calc
    mixedMoment B raw39486 raw39486Labels = mixedMoment B raw39486step0 raw39486step0Labels := by
      have hz : ∀ j, raw39486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39486step0 = (fun i j => raw39486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39486step0 raw39486; decide +kernel
      have hl : raw39486step0Labels = raw39486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39486 raw39486Labels permutation434 hz
    mixedMoment B raw39486step0 raw39486step0Labels = mixedMoment B raw39486step1 raw39486step1Labels := by
      have hz : ∀ j, raw39486step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39486step1 = (fun i j => raw39486step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39486step1 raw39486step0; decide +kernel
      have hl : raw39486step1Labels = raw39486step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39486step0 raw39486step0Labels permutation80 hz
    mixedMoment B raw39486step1 raw39486step1Labels = mixedMoment B raw39486step2 raw39486step2Labels := by
      have ha : raw39486step2 = (fun i j => raw39486step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39486step2 raw39486step1; decide +kernel
      have hl : raw39486step2Labels = raw39486step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39486step1 raw39486step1Labels permutation30 permutation5
    _ = mixedMoment B node391 node391Labels := by rfl

theorem canonical39487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39487 raw39487Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw39487 raw39487Labels = mixedMoment B raw39487step0 raw39487step0Labels := by
      have hz : ∀ j, raw39487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39487step0 = (fun i j => raw39487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39487step0 raw39487; decide +kernel
      have hl : raw39487step0Labels = raw39487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39487 raw39487Labels permutation434 hz
    mixedMoment B raw39487step0 raw39487step0Labels = mixedMoment B raw39487step1 raw39487step1Labels := by
      have hz : ∀ j, raw39487step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39487step1 = (fun i j => raw39487step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39487step1 raw39487step0; decide +kernel
      have hl : raw39487step1Labels = raw39487step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39487step0 raw39487step0Labels permutation80 hz
    _ = mixedMoment B node412 node412Labels := by rfl

theorem canonical39488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39488 raw39488Labels = mixedMoment B node410 node410Labels := by
  calc
    mixedMoment B raw39488 raw39488Labels = mixedMoment B raw39488step0 raw39488step0Labels := by
      have hz : ∀ j, raw39488 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39488step0 = (fun i j => raw39488 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39488step0 raw39488; decide +kernel
      have hl : raw39488step0Labels = raw39488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39488 raw39488Labels permutation434 hz
    mixedMoment B raw39488step0 raw39488step0Labels = mixedMoment B raw39488step1 raw39488step1Labels := by
      have hz : ∀ j, raw39488step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39488step1 = (fun i j => raw39488step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39488step1 raw39488step0; decide +kernel
      have hl : raw39488step1Labels = raw39488step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39488step0 raw39488step0Labels permutation80 hz
    _ = mixedMoment B node410 node410Labels := by rfl

theorem canonical39489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39489 raw39489Labels = mixedMoment B node408 node408Labels := by
  calc
    mixedMoment B raw39489 raw39489Labels = mixedMoment B raw39489step0 raw39489step0Labels := by
      have hz : ∀ j, raw39489 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39489step0 = (fun i j => raw39489 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39489step0 raw39489; decide +kernel
      have hl : raw39489step0Labels = raw39489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39489 raw39489Labels permutation434 hz
    mixedMoment B raw39489step0 raw39489step0Labels = mixedMoment B raw39489step1 raw39489step1Labels := by
      have hz : ∀ j, raw39489step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39489step1 = (fun i j => raw39489step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39489step1 raw39489step0; decide +kernel
      have hl : raw39489step1Labels = raw39489step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39489step0 raw39489step0Labels permutation80 hz
    _ = mixedMoment B node408 node408Labels := by rfl

theorem canonical39490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39490 raw39490Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39490 raw39490Labels = mixedMoment B raw39490step0 raw39490step0Labels := by
      have hz : ∀ j, raw39490 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39490step0 = (fun i j => raw39490 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39490step0 raw39490; decide +kernel
      have hl : raw39490step0Labels = raw39490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39490 raw39490Labels permutation346 hz
    mixedMoment B raw39490step0 raw39490step0Labels = mixedMoment B raw39490step1 raw39490step1Labels := by
      have ha : raw39490step1 = (fun i j => raw39490step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39490step1 raw39490step0; decide +kernel
      have hl : raw39490step1Labels = raw39490step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39490step0 raw39490step0Labels permutation38 permutation2
    _ = mixedMoment B node384 node384Labels := by rfl

theorem canonical39491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39491 raw39491Labels = mixedMoment B node381 node381Labels := by
  calc
    mixedMoment B raw39491 raw39491Labels = mixedMoment B raw39491step0 raw39491step0Labels := by
      have hz : ∀ j, raw39491 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39491step0 = (fun i j => raw39491 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39491step0 raw39491; decide +kernel
      have hl : raw39491step0Labels = raw39491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39491 raw39491Labels permutation346 hz
    mixedMoment B raw39491step0 raw39491step0Labels = mixedMoment B raw39491step1 raw39491step1Labels := by
      have ha : raw39491step1 = (fun i j => raw39491step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39491step1 raw39491step0; decide +kernel
      have hl : raw39491step1Labels = raw39491step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39491step0 raw39491step0Labels permutation38 permutation2
    _ = mixedMoment B node381 node381Labels := by rfl

theorem canonical39492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39492 raw39492Labels = mixedMoment B node364 node364Labels := by
  calc
    mixedMoment B raw39492 raw39492Labels = mixedMoment B raw39492step0 raw39492step0Labels := by
      have hz : ∀ j, raw39492 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39492step0 = (fun i j => raw39492 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39492step0 raw39492; decide +kernel
      have hl : raw39492step0Labels = raw39492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39492 raw39492Labels permutation346 hz
    mixedMoment B raw39492step0 raw39492step0Labels = mixedMoment B raw39492step1 raw39492step1Labels := by
      have ha : raw39492step1 = (fun i j => raw39492step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39492step1 raw39492step0; decide +kernel
      have hl : raw39492step1Labels = raw39492step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39492step0 raw39492step0Labels permutation38 permutation2
    _ = mixedMoment B node364 node364Labels := by rfl

theorem canonical39493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39493 raw39493Labels = mixedMoment B node393 node393Labels := by
  calc
    mixedMoment B raw39493 raw39493Labels = mixedMoment B raw39493step0 raw39493step0Labels := by
      have hz : ∀ j, raw39493 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39493step0 = (fun i j => raw39493 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39493step0 raw39493; decide +kernel
      have hl : raw39493step0Labels = raw39493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39493 raw39493Labels permutation346 hz
    mixedMoment B raw39493step0 raw39493step0Labels = mixedMoment B raw39493step1 raw39493step1Labels := by
      have ha : raw39493step1 = (fun i j => raw39493step0 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39493step1 raw39493step0; decide +kernel
      have hl : raw39493step1Labels = raw39493step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39493step0 raw39493step0Labels permutation144 permutation4
    _ = mixedMoment B node393 node393Labels := by rfl

theorem canonical39494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39494 raw39494Labels = mixedMoment B node409 node409Labels := by
  calc
    mixedMoment B raw39494 raw39494Labels = mixedMoment B raw39494step0 raw39494step0Labels := by
      have hz : ∀ j, raw39494 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39494step0 = (fun i j => raw39494 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39494step0 raw39494; decide +kernel
      have hl : raw39494step0Labels = raw39494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39494 raw39494Labels permutation346 hz
    mixedMoment B raw39494step0 raw39494step0Labels = mixedMoment B raw39494step1 raw39494step1Labels := by
      have ha : raw39494step1 = (fun i j => raw39494step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39494step1 raw39494step0; decide +kernel
      have hl : raw39494step1Labels = raw39494step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39494step0 raw39494step0Labels permutation37 permutation2
    _ = mixedMoment B node409 node409Labels := by rfl

theorem canonical39495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39495 raw39495Labels = mixedMoment B node380 node380Labels := by
  calc
    mixedMoment B raw39495 raw39495Labels = mixedMoment B raw39495step0 raw39495step0Labels := by
      have ha : raw39495step0 = (fun i j => raw39495 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39495step0 raw39495; decide +kernel
      have hl : raw39495step0Labels = raw39495Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39495 raw39495Labels permutation180 permutation2
    _ = mixedMoment B node380 node380Labels := by rfl

theorem canonical39496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39496 raw39496Labels = mixedMoment B node363 node363Labels := by
  calc
    mixedMoment B raw39496 raw39496Labels = mixedMoment B raw39496step0 raw39496step0Labels := by
      have ha : raw39496step0 = (fun i j => raw39496 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39496step0 raw39496; decide +kernel
      have hl : raw39496step0Labels = raw39496Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39496 raw39496Labels permutation180 permutation2
    _ = mixedMoment B node363 node363Labels := by rfl

theorem canonical39497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39497 raw39497Labels = mixedMoment B node386 node386Labels := by
  calc
    mixedMoment B raw39497 raw39497Labels = mixedMoment B raw39497step0 raw39497step0Labels := by
      have hz : ∀ j, raw39497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39497step0 = (fun i j => raw39497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39497step0 raw39497; decide +kernel
      have hl : raw39497step0Labels = raw39497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39497 raw39497Labels permutation434 hz
    mixedMoment B raw39497step0 raw39497step0Labels = mixedMoment B raw39497step1 raw39497step1Labels := by
      have ha : raw39497step1 = (fun i j => raw39497step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39497step1 raw39497step0; decide +kernel
      have hl : raw39497step1Labels = raw39497step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39497step0 raw39497step0Labels permutation149 permutation5
    _ = mixedMoment B node386 node386Labels := by rfl

theorem canonical39498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39498 raw39498Labels = mixedMoment B node397 node397Labels := by
  calc
    mixedMoment B raw39498 raw39498Labels = mixedMoment B raw39498step0 raw39498step0Labels := by
      have hz : ∀ j, raw39498 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39498step0 = (fun i j => raw39498 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39498step0 raw39498; decide +kernel
      have hl : raw39498step0Labels = raw39498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39498 raw39498Labels permutation434 hz
    _ = mixedMoment B node397 node397Labels := by rfl

theorem canonical39499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39499 raw39499Labels = mixedMoment B node393 node393Labels := by
  calc
    mixedMoment B raw39499 raw39499Labels = mixedMoment B raw39499step0 raw39499step0Labels := by
      have hz : ∀ j, raw39499 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39499step0 = (fun i j => raw39499 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39499step0 raw39499; decide +kernel
      have hl : raw39499step0Labels = raw39499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39499 raw39499Labels permutation434 hz
    _ = mixedMoment B node393 node393Labels := by rfl

theorem canonical39500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39500 raw39500Labels = mixedMoment B node357 node357Labels := by
  calc
    mixedMoment B raw39500 raw39500Labels = mixedMoment B raw39500step0 raw39500step0Labels := by
      have ha : raw39500step0 = (fun i j => raw39500 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39500step0 raw39500; decide +kernel
      have hl : raw39500step0Labels = raw39500Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39500 raw39500Labels permutation200 permutation2
    _ = mixedMoment B node357 node357Labels := by rfl

theorem canonical39501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39501 raw39501Labels = mixedMoment B node392 node392Labels := by
  calc
    mixedMoment B raw39501 raw39501Labels = mixedMoment B raw39501step0 raw39501step0Labels := by
      have ha : raw39501step0 = (fun i j => raw39501 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39501step0 raw39501; decide +kernel
      have hl : raw39501step0Labels = raw39501Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39501 raw39501Labels permutation156 permutation2
    _ = mixedMoment B node392 node392Labels := by rfl

theorem canonical39502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39502 raw39502Labels = mixedMoment B node394 node394Labels := by
  calc
    mixedMoment B raw39502 raw39502Labels = mixedMoment B raw39502step0 raw39502step0Labels := by
      have ha : raw39502step0 = (fun i j => raw39502 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39502step0 raw39502; decide +kernel
      have hl : raw39502step0Labels = raw39502Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39502 raw39502Labels permutation157 permutation2
    _ = mixedMoment B node394 node394Labels := by rfl

theorem canonical39503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39503 raw39503Labels = mixedMoment B node406 node406Labels := by
  calc
    mixedMoment B raw39503 raw39503Labels = mixedMoment B raw39503step0 raw39503step0Labels := by
      have hz : ∀ j, raw39503 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39503step0 = (fun i j => raw39503 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39503step0 raw39503; decide +kernel
      have hl : raw39503step0Labels = raw39503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39503 raw39503Labels permutation434 hz
    mixedMoment B raw39503step0 raw39503step0Labels = mixedMoment B raw39503step1 raw39503step1Labels := by
      have hz : ∀ j, raw39503step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39503step1 = (fun i j => raw39503step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39503step1 raw39503step0; decide +kernel
      have hl : raw39503step1Labels = raw39503step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39503step0 raw39503step0Labels permutation80 hz
    _ = mixedMoment B node406 node406Labels := by rfl

theorem canonical39504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39504 raw39504Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw39504 raw39504Labels = mixedMoment B raw39504step0 raw39504step0Labels := by
      have hz : ∀ j, raw39504 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39504step0 = (fun i j => raw39504 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39504step0 raw39504; decide +kernel
      have hl : raw39504step0Labels = raw39504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39504 raw39504Labels permutation434 hz
    mixedMoment B raw39504step0 raw39504step0Labels = mixedMoment B raw39504step1 raw39504step1Labels := by
      have hz : ∀ j, raw39504step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39504step1 = (fun i j => raw39504step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39504step1 raw39504step0; decide +kernel
      have hl : raw39504step1Labels = raw39504step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39504step0 raw39504step0Labels permutation80 hz
    _ = mixedMoment B node404 node404Labels := by rfl

theorem canonical39505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39505 raw39505Labels = mixedMoment B node342 node342Labels := by
  calc
    mixedMoment B raw39505 raw39505Labels = mixedMoment B raw39505step0 raw39505step0Labels := by
      have hz : ∀ j, raw39505 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39505step0 = (fun i j => raw39505 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39505step0 raw39505; decide +kernel
      have hl : raw39505step0Labels = raw39505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39505 raw39505Labels permutation434 hz
    mixedMoment B raw39505step0 raw39505step0Labels = mixedMoment B raw39505step1 raw39505step1Labels := by
      have hz : ∀ j, raw39505step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39505step1 = (fun i j => raw39505step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39505step1 raw39505step0; decide +kernel
      have hl : raw39505step1Labels = raw39505step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39505step0 raw39505step0Labels permutation80 hz
    mixedMoment B raw39505step1 raw39505step1Labels = mixedMoment B raw39505step2 raw39505step2Labels := by
      have ha : raw39505step2 = (fun i j => raw39505step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39505step2 raw39505step1; decide +kernel
      have hl : raw39505step2Labels = raw39505step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39505step1 raw39505step1Labels permutation29 permutation7
    _ = mixedMoment B node342 node342Labels := by rfl

theorem canonical39506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39506 raw39506Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw39506 raw39506Labels = mixedMoment B raw39506step0 raw39506step0Labels := by
      have hz : ∀ j, raw39506 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39506step0 = (fun i j => raw39506 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39506step0 raw39506; decide +kernel
      have hl : raw39506step0Labels = raw39506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39506 raw39506Labels permutation346 hz
    mixedMoment B raw39506step0 raw39506step0Labels = mixedMoment B raw39506step1 raw39506step1Labels := by
      have ha : raw39506step1 = (fun i j => raw39506step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39506step1 raw39506step0; decide +kernel
      have hl : raw39506step1Labels = raw39506step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39506step0 raw39506step0Labels permutation38 permutation2
    _ = mixedMoment B node377 node377Labels := by rfl

theorem canonical39507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39507 raw39507Labels = mixedMoment B node324 node324Labels := by
  calc
    mixedMoment B raw39507 raw39507Labels = mixedMoment B raw39507step0 raw39507step0Labels := by
      have hz : ∀ j, raw39507 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39507step0 = (fun i j => raw39507 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39507step0 raw39507; decide +kernel
      have hl : raw39507step0Labels = raw39507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39507 raw39507Labels permutation346 hz
    mixedMoment B raw39507step0 raw39507step0Labels = mixedMoment B raw39507step1 raw39507step1Labels := by
      have ha : raw39507step1 = (fun i j => raw39507step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39507step1 raw39507step0; decide +kernel
      have hl : raw39507step1Labels = raw39507step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39507step0 raw39507step0Labels permutation139 permutation7
    _ = mixedMoment B node324 node324Labels := by rfl

theorem canonical39508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39508 raw39508Labels = mixedMoment B node399 node399Labels := by
  calc
    mixedMoment B raw39508 raw39508Labels = mixedMoment B raw39508step0 raw39508step0Labels := by
      have hz : ∀ j, raw39508 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39508step0 = (fun i j => raw39508 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39508step0 raw39508; decide +kernel
      have hl : raw39508step0Labels = raw39508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39508 raw39508Labels permutation346 hz
    mixedMoment B raw39508step0 raw39508step0Labels = mixedMoment B raw39508step1 raw39508step1Labels := by
      have ha : raw39508step1 = (fun i j => raw39508step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39508step1 raw39508step0; decide +kernel
      have hl : raw39508step1Labels = raw39508step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39508step0 raw39508step0Labels permutation37 permutation2
    _ = mixedMoment B node399 node399Labels := by rfl

theorem canonical39509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39509 raw39509Labels = mixedMoment B node400 node400Labels := by
  calc
    mixedMoment B raw39509 raw39509Labels = mixedMoment B raw39509step0 raw39509step0Labels := by
      have hz : ∀ j, raw39509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39509step0 = (fun i j => raw39509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39509step0 raw39509; decide +kernel
      have hl : raw39509step0Labels = raw39509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39509 raw39509Labels permutation346 hz
    mixedMoment B raw39509step0 raw39509step0Labels = mixedMoment B raw39509step1 raw39509step1Labels := by
      have ha : raw39509step1 = (fun i j => raw39509step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39509step1 raw39509step0; decide +kernel
      have hl : raw39509step1Labels = raw39509step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39509step0 raw39509step0Labels permutation37 permutation2
    _ = mixedMoment B node400 node400Labels := by rfl

theorem canonical39510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39510 raw39510Labels = mixedMoment B node403 node403Labels := by
  calc
    mixedMoment B raw39510 raw39510Labels = mixedMoment B raw39510step0 raw39510step0Labels := by
      have hz : ∀ j, raw39510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39510step0 = (fun i j => raw39510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39510step0 raw39510; decide +kernel
      have hl : raw39510step0Labels = raw39510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39510 raw39510Labels permutation346 hz
    mixedMoment B raw39510step0 raw39510step0Labels = mixedMoment B raw39510step1 raw39510step1Labels := by
      have ha : raw39510step1 = (fun i j => raw39510step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39510step1 raw39510step0; decide +kernel
      have hl : raw39510step1Labels = raw39510step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39510step0 raw39510step0Labels permutation35 permutation2
    _ = mixedMoment B node403 node403Labels := by rfl

theorem canonical39511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39511 raw39511Labels = mixedMoment B node376 node376Labels := by
  calc
    mixedMoment B raw39511 raw39511Labels = mixedMoment B raw39511step0 raw39511step0Labels := by
      have ha : raw39511step0 = (fun i j => raw39511 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39511step0 raw39511; decide +kernel
      have hl : raw39511step0Labels = raw39511Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39511 raw39511Labels permutation180 permutation2
    _ = mixedMoment B node376 node376Labels := by rfl

theorem canonical39512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39512 raw39512Labels = mixedMoment B node359 node359Labels := by
  calc
    mixedMoment B raw39512 raw39512Labels = mixedMoment B raw39512step0 raw39512step0Labels := by
      have ha : raw39512step0 = (fun i j => raw39512 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39512step0 raw39512; decide +kernel
      have hl : raw39512step0Labels = raw39512Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39512 raw39512Labels permutation181 permutation2
    _ = mixedMoment B node359 node359Labels := by rfl

theorem canonical39513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39513 raw39513Labels = mixedMoment B node421 node421Labels := by
  calc
    mixedMoment B raw39513 raw39513Labels = mixedMoment B raw39513step0 raw39513step0Labels := by
      have hz : ∀ j, raw39513 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39513step0 = (fun i j => raw39513 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39513step0 raw39513; decide +kernel
      have hl : raw39513step0Labels = raw39513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39513 raw39513Labels permutation434 hz
    mixedMoment B raw39513step0 raw39513step0Labels = mixedMoment B raw39513step1 raw39513step1Labels := by
      have hz : ∀ j, raw39513step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39513step1 = (fun i j => raw39513step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39513step1 raw39513step0; decide +kernel
      have hl : raw39513step1Labels = raw39513step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39513step0 raw39513step0Labels permutation80 hz
    mixedMoment B raw39513step1 raw39513step1Labels = mixedMoment B raw39513step2 raw39513step2Labels := by
      have hz : ∀ j, raw39513step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39513step2 = (fun i j => raw39513step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39513step2 raw39513step1; decide +kernel
      have hl : raw39513step2Labels = raw39513step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39513step1 raw39513step1Labels permutation14 hz
    _ = mixedMoment B node421 node421Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment32 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 32) =
      Integer.Sparse.eval keyMomentRow32 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 32).leftCharge (GramAssembly.key 32).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 414) := by
    have ha : gramCharges (GramAssembly.key 32).leftCharge (GramAssembly.key 32).rightCharge = raw39482 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39482Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39482 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 32).leftCharge (GramAssembly.key 32).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow32, Integer.Sparse.eval]

theorem keyMoment33 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 33) =
      Integer.Sparse.eval keyMomentRow33 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 33).leftCharge (GramAssembly.key 33).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 400) := by
    have ha : gramCharges (GramAssembly.key 33).leftCharge (GramAssembly.key 33).rightCharge = raw39483 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39483Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39483 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 33).leftCharge (GramAssembly.key 33).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow33, Integer.Sparse.eval]

theorem keyMoment34 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 34) =
      Integer.Sparse.eval keyMomentRow34 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 34).leftCharge (GramAssembly.key 34).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 409) := by
    have ha : gramCharges (GramAssembly.key 34).leftCharge (GramAssembly.key 34).rightCharge = raw39484 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39484Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39484 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 34).leftCharge (GramAssembly.key 34).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow34, Integer.Sparse.eval]

theorem keyMoment35 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 35) =
      Integer.Sparse.eval keyMomentRow35 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 35).leftCharge (GramAssembly.key 35).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 270) := by
    have ha : gramCharges (GramAssembly.key 35).leftCharge (GramAssembly.key 35).rightCharge = raw39485 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39485Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39485 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 35).leftCharge (GramAssembly.key 35).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow35, Integer.Sparse.eval]

theorem keyMoment36 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 36) =
      Integer.Sparse.eval keyMomentRow36 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 36).leftCharge (GramAssembly.key 36).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 391) := by
    have ha : gramCharges (GramAssembly.key 36).leftCharge (GramAssembly.key 36).rightCharge = raw39486 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39486Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39486 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 36).leftCharge (GramAssembly.key 36).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow36, Integer.Sparse.eval]

theorem keyMoment37 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 37) =
      Integer.Sparse.eval keyMomentRow37 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 37).leftCharge (GramAssembly.key 37).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 412) := by
    have ha : gramCharges (GramAssembly.key 37).leftCharge (GramAssembly.key 37).rightCharge = raw39487 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39487Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39487 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 37).leftCharge (GramAssembly.key 37).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow37, Integer.Sparse.eval]

theorem keyMoment38 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 38) =
      Integer.Sparse.eval keyMomentRow38 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 38).leftCharge (GramAssembly.key 38).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 410) := by
    have ha : gramCharges (GramAssembly.key 38).leftCharge (GramAssembly.key 38).rightCharge = raw39488 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39488Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39488 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 38).leftCharge (GramAssembly.key 38).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow38, Integer.Sparse.eval]

theorem keyMoment39 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 39) =
      Integer.Sparse.eval keyMomentRow39 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 39).leftCharge (GramAssembly.key 39).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 408) := by
    have ha : gramCharges (GramAssembly.key 39).leftCharge (GramAssembly.key 39).rightCharge = raw39489 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39489Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39489 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 39).leftCharge (GramAssembly.key 39).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow39, Integer.Sparse.eval]

theorem keyMoment40 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 40) =
      Integer.Sparse.eval keyMomentRow40 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 40).leftCharge (GramAssembly.key 40).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 40).leftCharge (GramAssembly.key 40).rightCharge = raw39490 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39490Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39490 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 40).leftCharge (GramAssembly.key 40).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow40, Integer.Sparse.eval]

theorem keyMoment41 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 41) =
      Integer.Sparse.eval keyMomentRow41 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 41).leftCharge (GramAssembly.key 41).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 381) := by
    have ha : gramCharges (GramAssembly.key 41).leftCharge (GramAssembly.key 41).rightCharge = raw39491 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39491Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39491 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 41).leftCharge (GramAssembly.key 41).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow41, Integer.Sparse.eval]

theorem keyMoment42 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 42) =
      Integer.Sparse.eval keyMomentRow42 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 42).leftCharge (GramAssembly.key 42).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 364) := by
    have ha : gramCharges (GramAssembly.key 42).leftCharge (GramAssembly.key 42).rightCharge = raw39492 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39492Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39492 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 42).leftCharge (GramAssembly.key 42).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow42, Integer.Sparse.eval]

theorem keyMoment43 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 43) =
      Integer.Sparse.eval keyMomentRow43 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 43).leftCharge (GramAssembly.key 43).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 393) := by
    have ha : gramCharges (GramAssembly.key 43).leftCharge (GramAssembly.key 43).rightCharge = raw39493 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39493Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39493 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 43).leftCharge (GramAssembly.key 43).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow43, Integer.Sparse.eval]

theorem keyMoment44 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 44) =
      Integer.Sparse.eval keyMomentRow44 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 44).leftCharge (GramAssembly.key 44).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 409) := by
    have ha : gramCharges (GramAssembly.key 44).leftCharge (GramAssembly.key 44).rightCharge = raw39494 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39494Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39494 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 44).leftCharge (GramAssembly.key 44).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow44, Integer.Sparse.eval]

theorem keyMoment45 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 45) =
      Integer.Sparse.eval keyMomentRow45 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 45).leftCharge (GramAssembly.key 45).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 380) := by
    have ha : gramCharges (GramAssembly.key 45).leftCharge (GramAssembly.key 45).rightCharge = raw39495 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39495Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39495 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 45).leftCharge (GramAssembly.key 45).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow45, Integer.Sparse.eval]

theorem keyMoment46 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 46) =
      Integer.Sparse.eval keyMomentRow46 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 46).leftCharge (GramAssembly.key 46).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 363) := by
    have ha : gramCharges (GramAssembly.key 46).leftCharge (GramAssembly.key 46).rightCharge = raw39496 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39496Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39496 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 46).leftCharge (GramAssembly.key 46).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow46, Integer.Sparse.eval]

theorem keyMoment47 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 47) =
      Integer.Sparse.eval keyMomentRow47 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 47).leftCharge (GramAssembly.key 47).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 386) := by
    have ha : gramCharges (GramAssembly.key 47).leftCharge (GramAssembly.key 47).rightCharge = raw39497 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39497Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39497 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 47).leftCharge (GramAssembly.key 47).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow47, Integer.Sparse.eval]

theorem keyMoment48 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 48) =
      Integer.Sparse.eval keyMomentRow48 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 48).leftCharge (GramAssembly.key 48).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 397) := by
    have ha : gramCharges (GramAssembly.key 48).leftCharge (GramAssembly.key 48).rightCharge = raw39498 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39498Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39498 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 48).leftCharge (GramAssembly.key 48).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow48, Integer.Sparse.eval]

theorem keyMoment49 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 49) =
      Integer.Sparse.eval keyMomentRow49 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 49).leftCharge (GramAssembly.key 49).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 393) := by
    have ha : gramCharges (GramAssembly.key 49).leftCharge (GramAssembly.key 49).rightCharge = raw39499 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39499Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39499 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 49).leftCharge (GramAssembly.key 49).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow49, Integer.Sparse.eval]

theorem keyMoment50 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 50) =
      Integer.Sparse.eval keyMomentRow50 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 50).leftCharge (GramAssembly.key 50).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 357) := by
    have ha : gramCharges (GramAssembly.key 50).leftCharge (GramAssembly.key 50).rightCharge = raw39500 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39500Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39500 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 50).leftCharge (GramAssembly.key 50).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow50, Integer.Sparse.eval]

theorem keyMoment51 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 51) =
      Integer.Sparse.eval keyMomentRow51 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 51).leftCharge (GramAssembly.key 51).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 392) := by
    have ha : gramCharges (GramAssembly.key 51).leftCharge (GramAssembly.key 51).rightCharge = raw39501 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39501Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39501 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 51).leftCharge (GramAssembly.key 51).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow51, Integer.Sparse.eval]

theorem keyMoment52 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 52) =
      Integer.Sparse.eval keyMomentRow52 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 52).leftCharge (GramAssembly.key 52).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 394) := by
    have ha : gramCharges (GramAssembly.key 52).leftCharge (GramAssembly.key 52).rightCharge = raw39502 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39502Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39502 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 52).leftCharge (GramAssembly.key 52).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow52, Integer.Sparse.eval]

theorem keyMoment53 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 53) =
      Integer.Sparse.eval keyMomentRow53 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 53).leftCharge (GramAssembly.key 53).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 406) := by
    have ha : gramCharges (GramAssembly.key 53).leftCharge (GramAssembly.key 53).rightCharge = raw39503 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39503Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39503 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 53).leftCharge (GramAssembly.key 53).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow53, Integer.Sparse.eval]

theorem keyMoment54 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 54) =
      Integer.Sparse.eval keyMomentRow54 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 54).leftCharge (GramAssembly.key 54).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 404) := by
    have ha : gramCharges (GramAssembly.key 54).leftCharge (GramAssembly.key 54).rightCharge = raw39504 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39504Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39504 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 54).leftCharge (GramAssembly.key 54).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow54, Integer.Sparse.eval]

theorem keyMoment55 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 55) =
      Integer.Sparse.eval keyMomentRow55 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 55).leftCharge (GramAssembly.key 55).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 342) := by
    have ha : gramCharges (GramAssembly.key 55).leftCharge (GramAssembly.key 55).rightCharge = raw39505 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39505Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39505 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 55).leftCharge (GramAssembly.key 55).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow55, Integer.Sparse.eval]

theorem keyMoment56 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 56) =
      Integer.Sparse.eval keyMomentRow56 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 56).leftCharge (GramAssembly.key 56).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 377) := by
    have ha : gramCharges (GramAssembly.key 56).leftCharge (GramAssembly.key 56).rightCharge = raw39506 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39506Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39506 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 56).leftCharge (GramAssembly.key 56).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow56, Integer.Sparse.eval]

theorem keyMoment57 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 57) =
      Integer.Sparse.eval keyMomentRow57 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 57).leftCharge (GramAssembly.key 57).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 324) := by
    have ha : gramCharges (GramAssembly.key 57).leftCharge (GramAssembly.key 57).rightCharge = raw39507 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39507Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39507 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 57).leftCharge (GramAssembly.key 57).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow57, Integer.Sparse.eval]

theorem keyMoment58 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 58) =
      Integer.Sparse.eval keyMomentRow58 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 58).leftCharge (GramAssembly.key 58).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 399) := by
    have ha : gramCharges (GramAssembly.key 58).leftCharge (GramAssembly.key 58).rightCharge = raw39508 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39508Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39508 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 58).leftCharge (GramAssembly.key 58).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow58, Integer.Sparse.eval]

theorem keyMoment59 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 59) =
      Integer.Sparse.eval keyMomentRow59 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 59).leftCharge (GramAssembly.key 59).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 400) := by
    have ha : gramCharges (GramAssembly.key 59).leftCharge (GramAssembly.key 59).rightCharge = raw39509 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39509Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39509 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 59).leftCharge (GramAssembly.key 59).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow59, Integer.Sparse.eval]

theorem keyMoment60 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 60) =
      Integer.Sparse.eval keyMomentRow60 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 60).leftCharge (GramAssembly.key 60).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 403) := by
    have ha : gramCharges (GramAssembly.key 60).leftCharge (GramAssembly.key 60).rightCharge = raw39510 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39510Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39510 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 60).leftCharge (GramAssembly.key 60).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow60, Integer.Sparse.eval]

theorem keyMoment61 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 61) =
      Integer.Sparse.eval keyMomentRow61 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 61).leftCharge (GramAssembly.key 61).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 376) := by
    have ha : gramCharges (GramAssembly.key 61).leftCharge (GramAssembly.key 61).rightCharge = raw39511 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39511Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39511 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 61).leftCharge (GramAssembly.key 61).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow61, Integer.Sparse.eval]

theorem keyMoment62 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 62) =
      Integer.Sparse.eval keyMomentRow62 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 62).leftCharge (GramAssembly.key 62).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 359) := by
    have ha : gramCharges (GramAssembly.key 62).leftCharge (GramAssembly.key 62).rightCharge = raw39512 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39512Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39512 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 62).leftCharge (GramAssembly.key 62).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow62, Integer.Sparse.eval]

theorem keyMoment63 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 63) =
      Integer.Sparse.eval keyMomentRow63 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 63).leftCharge (GramAssembly.key 63).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 421) := by
    have ha : gramCharges (GramAssembly.key 63).leftCharge (GramAssembly.key 63).rightCharge = raw39513 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39513Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39513 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 63).leftCharge (GramAssembly.key 63).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow63, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt32 : keyMomentRows (32 : Fin 2886) =
    keyMomentRow32 := by decide +kernel

theorem keyMomentRowsAt33 : keyMomentRows (33 : Fin 2886) =
    keyMomentRow33 := by decide +kernel

theorem keyMomentRowsAt34 : keyMomentRows (34 : Fin 2886) =
    keyMomentRow34 := by decide +kernel

theorem keyMomentRowsAt35 : keyMomentRows (35 : Fin 2886) =
    keyMomentRow35 := by decide +kernel

theorem keyMomentRowsAt36 : keyMomentRows (36 : Fin 2886) =
    keyMomentRow36 := by decide +kernel

theorem keyMomentRowsAt37 : keyMomentRows (37 : Fin 2886) =
    keyMomentRow37 := by decide +kernel

theorem keyMomentRowsAt38 : keyMomentRows (38 : Fin 2886) =
    keyMomentRow38 := by decide +kernel

theorem keyMomentRowsAt39 : keyMomentRows (39 : Fin 2886) =
    keyMomentRow39 := by decide +kernel

theorem keyMomentRowsAt40 : keyMomentRows (40 : Fin 2886) =
    keyMomentRow40 := by decide +kernel

theorem keyMomentRowsAt41 : keyMomentRows (41 : Fin 2886) =
    keyMomentRow41 := by decide +kernel

theorem keyMomentRowsAt42 : keyMomentRows (42 : Fin 2886) =
    keyMomentRow42 := by decide +kernel

theorem keyMomentRowsAt43 : keyMomentRows (43 : Fin 2886) =
    keyMomentRow43 := by decide +kernel

theorem keyMomentRowsAt44 : keyMomentRows (44 : Fin 2886) =
    keyMomentRow44 := by decide +kernel

theorem keyMomentRowsAt45 : keyMomentRows (45 : Fin 2886) =
    keyMomentRow45 := by decide +kernel

theorem keyMomentRowsAt46 : keyMomentRows (46 : Fin 2886) =
    keyMomentRow46 := by decide +kernel

theorem keyMomentRowsAt47 : keyMomentRows (47 : Fin 2886) =
    keyMomentRow47 := by decide +kernel

theorem keyMomentRowsAt48 : keyMomentRows (48 : Fin 2886) =
    keyMomentRow48 := by decide +kernel

theorem keyMomentRowsAt49 : keyMomentRows (49 : Fin 2886) =
    keyMomentRow49 := by decide +kernel

theorem keyMomentRowsAt50 : keyMomentRows (50 : Fin 2886) =
    keyMomentRow50 := by decide +kernel

theorem keyMomentRowsAt51 : keyMomentRows (51 : Fin 2886) =
    keyMomentRow51 := by decide +kernel

theorem keyMomentRowsAt52 : keyMomentRows (52 : Fin 2886) =
    keyMomentRow52 := by decide +kernel

theorem keyMomentRowsAt53 : keyMomentRows (53 : Fin 2886) =
    keyMomentRow53 := by decide +kernel

theorem keyMomentRowsAt54 : keyMomentRows (54 : Fin 2886) =
    keyMomentRow54 := by decide +kernel

theorem keyMomentRowsAt55 : keyMomentRows (55 : Fin 2886) =
    keyMomentRow55 := by decide +kernel

theorem keyMomentRowsAt56 : keyMomentRows (56 : Fin 2886) =
    keyMomentRow56 := by decide +kernel

theorem keyMomentRowsAt57 : keyMomentRows (57 : Fin 2886) =
    keyMomentRow57 := by decide +kernel

theorem keyMomentRowsAt58 : keyMomentRows (58 : Fin 2886) =
    keyMomentRow58 := by decide +kernel

theorem keyMomentRowsAt59 : keyMomentRows (59 : Fin 2886) =
    keyMomentRow59 := by decide +kernel

theorem keyMomentRowsAt60 : keyMomentRows (60 : Fin 2886) =
    keyMomentRow60 := by decide +kernel

theorem keyMomentRowsAt61 : keyMomentRows (61 : Fin 2886) =
    keyMomentRow61 := by decide +kernel

theorem keyMomentRowsAt62 : keyMomentRows (62 : Fin 2886) =
    keyMomentRow62 := by decide +kernel

theorem keyMomentRowsAt63 : keyMomentRows (63 : Fin 2886) =
    keyMomentRow63 := by decide +kernel

theorem keyMomentChunkSound1_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 1) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 32 ∨ k.val = 33 ∨ k.val = 34 ∨ k.val = 35 ∨ k.val = 36 ∨ k.val = 37 ∨ k.val = 38 ∨ k.val = 39 ∨ k.val = 40 ∨ k.val = 41 ∨ k.val = 42 ∨ k.val = 43 ∨ k.val = 44 ∨ k.val = 45 ∨ k.val = 46 ∨ k.val = 47 ∨ k.val = 48 ∨ k.val = 49 ∨ k.val = 50 ∨ k.val = 51 ∨ k.val = 52 ∨ k.val = 53 ∨ k.val = 54 ∨ k.val = 55 ∨ k.val = 56 ∨ k.val = 57 ∨ k.val = 58 ∨ k.val = 59 ∨ k.val = 60 ∨ k.val = 61 ∨ k.val = 62 ∨ k.val = 63 := by omega
  rcases heq with h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63
  · have he : k = (32 : Fin 2886) := Fin.ext h32
    subst k
    rw [keyMomentRowsAt32]
    exact keyMoment32 B hB
  · have he : k = (33 : Fin 2886) := Fin.ext h33
    subst k
    rw [keyMomentRowsAt33]
    exact keyMoment33 B hB
  · have he : k = (34 : Fin 2886) := Fin.ext h34
    subst k
    rw [keyMomentRowsAt34]
    exact keyMoment34 B hB
  · have he : k = (35 : Fin 2886) := Fin.ext h35
    subst k
    rw [keyMomentRowsAt35]
    exact keyMoment35 B hB
  · have he : k = (36 : Fin 2886) := Fin.ext h36
    subst k
    rw [keyMomentRowsAt36]
    exact keyMoment36 B hB
  · have he : k = (37 : Fin 2886) := Fin.ext h37
    subst k
    rw [keyMomentRowsAt37]
    exact keyMoment37 B hB
  · have he : k = (38 : Fin 2886) := Fin.ext h38
    subst k
    rw [keyMomentRowsAt38]
    exact keyMoment38 B hB
  · have he : k = (39 : Fin 2886) := Fin.ext h39
    subst k
    rw [keyMomentRowsAt39]
    exact keyMoment39 B hB
  · have he : k = (40 : Fin 2886) := Fin.ext h40
    subst k
    rw [keyMomentRowsAt40]
    exact keyMoment40 B hB
  · have he : k = (41 : Fin 2886) := Fin.ext h41
    subst k
    rw [keyMomentRowsAt41]
    exact keyMoment41 B hB
  · have he : k = (42 : Fin 2886) := Fin.ext h42
    subst k
    rw [keyMomentRowsAt42]
    exact keyMoment42 B hB
  · have he : k = (43 : Fin 2886) := Fin.ext h43
    subst k
    rw [keyMomentRowsAt43]
    exact keyMoment43 B hB
  · have he : k = (44 : Fin 2886) := Fin.ext h44
    subst k
    rw [keyMomentRowsAt44]
    exact keyMoment44 B hB
  · have he : k = (45 : Fin 2886) := Fin.ext h45
    subst k
    rw [keyMomentRowsAt45]
    exact keyMoment45 B hB
  · have he : k = (46 : Fin 2886) := Fin.ext h46
    subst k
    rw [keyMomentRowsAt46]
    exact keyMoment46 B hB
  · have he : k = (47 : Fin 2886) := Fin.ext h47
    subst k
    rw [keyMomentRowsAt47]
    exact keyMoment47 B hB
  · have he : k = (48 : Fin 2886) := Fin.ext h48
    subst k
    rw [keyMomentRowsAt48]
    exact keyMoment48 B hB
  · have he : k = (49 : Fin 2886) := Fin.ext h49
    subst k
    rw [keyMomentRowsAt49]
    exact keyMoment49 B hB
  · have he : k = (50 : Fin 2886) := Fin.ext h50
    subst k
    rw [keyMomentRowsAt50]
    exact keyMoment50 B hB
  · have he : k = (51 : Fin 2886) := Fin.ext h51
    subst k
    rw [keyMomentRowsAt51]
    exact keyMoment51 B hB
  · have he : k = (52 : Fin 2886) := Fin.ext h52
    subst k
    rw [keyMomentRowsAt52]
    exact keyMoment52 B hB
  · have he : k = (53 : Fin 2886) := Fin.ext h53
    subst k
    rw [keyMomentRowsAt53]
    exact keyMoment53 B hB
  · have he : k = (54 : Fin 2886) := Fin.ext h54
    subst k
    rw [keyMomentRowsAt54]
    exact keyMoment54 B hB
  · have he : k = (55 : Fin 2886) := Fin.ext h55
    subst k
    rw [keyMomentRowsAt55]
    exact keyMoment55 B hB
  · have he : k = (56 : Fin 2886) := Fin.ext h56
    subst k
    rw [keyMomentRowsAt56]
    exact keyMoment56 B hB
  · have he : k = (57 : Fin 2886) := Fin.ext h57
    subst k
    rw [keyMomentRowsAt57]
    exact keyMoment57 B hB
  · have he : k = (58 : Fin 2886) := Fin.ext h58
    subst k
    rw [keyMomentRowsAt58]
    exact keyMoment58 B hB
  · have he : k = (59 : Fin 2886) := Fin.ext h59
    subst k
    rw [keyMomentRowsAt59]
    exact keyMoment59 B hB
  · have he : k = (60 : Fin 2886) := Fin.ext h60
    subst k
    rw [keyMomentRowsAt60]
    exact keyMoment60 B hB
  · have he : k = (61 : Fin 2886) := Fin.ext h61
    subst k
    rw [keyMomentRowsAt61]
    exact keyMoment61 B hB
  · have he : k = (62 : Fin 2886) := Fin.ext h62
    subst k
    rw [keyMomentRowsAt62]
    exact keyMoment62 B hB
  · have he : k = (63 : Fin 2886) := Fin.ext h63
    subst k
    rw [keyMomentRowsAt63]
    exact keyMoment63 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound1_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound1_e_oai
