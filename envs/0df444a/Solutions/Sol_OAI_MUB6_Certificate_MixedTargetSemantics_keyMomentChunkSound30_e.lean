-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound30_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:51:30.792991+00:00
-- url     : https://prove2.me/submissions/53e27277-97d0-4695-834f-34becb822c13

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical315
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40400 raw40400Labels = mixedMoment B node1971 node1971Labels := by
  calc
    mixedMoment B raw40400 raw40400Labels = mixedMoment B raw40400step0 raw40400step0Labels := by
      have hz : ∀ j, raw40400 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40400step0 = (fun i j => raw40400 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40400step0 raw40400; decide +kernel
      have hl : raw40400step0Labels = raw40400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40400 raw40400Labels permutation346 hz
    mixedMoment B raw40400step0 raw40400step0Labels = mixedMoment B raw40400step1 raw40400step1Labels := by
      have ha : raw40400step1 = (fun i j => raw40400step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40400step1 raw40400step0; decide +kernel
      have hl : raw40400step1Labels = raw40400step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40400step0 raw40400step0Labels permutation65 permutation6
    _ = mixedMoment B node1971 node1971Labels := by rfl

theorem canonical40401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40401 raw40401Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw40401 raw40401Labels = mixedMoment B raw40401step0 raw40401step0Labels := by
      have hz : ∀ j, raw40401 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40401step0 = (fun i j => raw40401 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40401step0 raw40401; decide +kernel
      have hl : raw40401step0Labels = raw40401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40401 raw40401Labels permutation346 hz
    mixedMoment B raw40401step0 raw40401step0Labels = mixedMoment B raw40401step1 raw40401step1Labels := by
      have ha : raw40401step1 = (fun i j => raw40401step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40401step1 raw40401step0; decide +kernel
      have hl : raw40401step1Labels = raw40401step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40401step0 raw40401step0Labels permutation65 permutation6
    _ = mixedMoment B node2026 node2026Labels := by rfl

theorem canonical40402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40402 raw40402Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw40402 raw40402Labels = mixedMoment B raw40402step0 raw40402step0Labels := by
      have hz : ∀ j, raw40402 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40402step0 = (fun i j => raw40402 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40402step0 raw40402; decide +kernel
      have hl : raw40402step0Labels = raw40402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40402 raw40402Labels permutation346 hz
    mixedMoment B raw40402step0 raw40402step0Labels = mixedMoment B raw40402step1 raw40402step1Labels := by
      have ha : raw40402step1 = (fun i j => raw40402step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40402step1 raw40402step0; decide +kernel
      have hl : raw40402step1Labels = raw40402step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40402step0 raw40402step0Labels permutation65 permutation6
    _ = mixedMoment B node2235 node2235Labels := by rfl

theorem canonical40403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40403 raw40403Labels = mixedMoment B node1976 node1976Labels := by
  calc
    mixedMoment B raw40403 raw40403Labels = mixedMoment B raw40403step0 raw40403step0Labels := by
      have ha : raw40403step0 = (fun i j => raw40403 (permutation332 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40403step0 raw40403; decide +kernel
      have hl : raw40403step0Labels = raw40403Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40403 raw40403Labels permutation332 permutation6
    _ = mixedMoment B node1976 node1976Labels := by rfl

theorem canonical40404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40404 raw40404Labels = mixedMoment B node1793 node1793Labels := by
  calc
    mixedMoment B raw40404 raw40404Labels = mixedMoment B raw40404step0 raw40404step0Labels := by
      have ha : raw40404step0 = (fun i j => raw40404 (permutation345 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40404step0 raw40404; decide +kernel
      have hl : raw40404step0Labels = raw40404Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40404 raw40404Labels permutation345 permutation6
    _ = mixedMoment B node1793 node1793Labels := by rfl

theorem canonical40405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40405 raw40405Labels = mixedMoment B node1965 node1965Labels := by
  calc
    mixedMoment B raw40405 raw40405Labels = mixedMoment B raw40405step0 raw40405step0Labels := by
      have ha : raw40405step0 = (fun i j => raw40405 (permutation316 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40405step0 raw40405; decide +kernel
      have hl : raw40405step0Labels = raw40405Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40405 raw40405Labels permutation316 permutation6
    _ = mixedMoment B node1965 node1965Labels := by rfl

theorem canonical40406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40406 raw40406Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw40406 raw40406Labels = mixedMoment B raw40406step0 raw40406step0Labels := by
      have ha : raw40406step0 = (fun i j => raw40406 (permutation317 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40406step0 raw40406; decide +kernel
      have hl : raw40406step0Labels = raw40406Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40406 raw40406Labels permutation317 permutation6
    _ = mixedMoment B node2010 node2010Labels := by rfl

theorem canonical40407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40407 raw40407Labels = mixedMoment B node1957 node1957Labels := by
  calc
    mixedMoment B raw40407 raw40407Labels = mixedMoment B raw40407step0 raw40407step0Labels := by
      have ha : raw40407step0 = (fun i j => raw40407 (permutation317 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40407step0 raw40407; decide +kernel
      have hl : raw40407step0Labels = raw40407Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40407 raw40407Labels permutation317 permutation6
    _ = mixedMoment B node1957 node1957Labels := by rfl

theorem canonical40408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40408 raw40408Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw40408 raw40408Labels = mixedMoment B raw40408step0 raw40408step0Labels := by
      have hz : ∀ j, raw40408 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40408step0 = (fun i j => raw40408 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40408step0 raw40408; decide +kernel
      have hl : raw40408step0Labels = raw40408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40408 raw40408Labels permutation520 hz
    mixedMoment B raw40408step0 raw40408step0Labels = mixedMoment B raw40408step1 raw40408step1Labels := by
      have hz : ∀ j, raw40408step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40408step1 = (fun i j => raw40408step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40408step1 raw40408step0; decide +kernel
      have hl : raw40408step1Labels = raw40408step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40408step0 raw40408step0Labels permutation104 hz
    mixedMoment B raw40408step1 raw40408step1Labels = mixedMoment B raw40408step2 raw40408step2Labels := by
      have ha : raw40408step2 = (fun i j => raw40408step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40408step2 raw40408step1; decide +kernel
      have hl : raw40408step2Labels = raw40408step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40408step1 raw40408step1Labels permutation31 permutation3
    mixedMoment B raw40408step2 raw40408step2Labels = mixedMoment B raw40408step3 raw40408step3Labels := by
      have ha : raw40408step3 = -raw40408step2 := by apply Matrix.ext; change ∀ i j, raw40408step3 i j = -(raw40408step2 i j); unfold raw40408step3 raw40408step2; decide +kernel
      have hl : raw40408step3Labels = raw40408step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2255 node2255Labels := by rfl

theorem canonical40409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40409 raw40409Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw40409 raw40409Labels = mixedMoment B raw40409step0 raw40409step0Labels := by
      have hz : ∀ j, raw40409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40409step0 = (fun i j => raw40409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40409step0 raw40409; decide +kernel
      have hl : raw40409step0Labels = raw40409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40409 raw40409Labels permutation434 hz
    mixedMoment B raw40409step0 raw40409step0Labels = mixedMoment B raw40409step1 raw40409step1Labels := by
      have ha : raw40409step1 = (fun i j => raw40409step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40409step1 raw40409step0; decide +kernel
      have hl : raw40409step1Labels = raw40409step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40409step0 raw40409step0Labels permutation151 permutation3
    mixedMoment B raw40409step1 raw40409step1Labels = mixedMoment B raw40409step2 raw40409step2Labels := by
      have ha : raw40409step2 = -raw40409step1 := by apply Matrix.ext; change ∀ i j, raw40409step2 i j = -(raw40409step1 i j); unfold raw40409step2 raw40409step1; decide +kernel
      have hl : raw40409step2Labels = raw40409step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2716 node2716Labels := by rfl

theorem canonical40410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40410 raw40410Labels = mixedMoment B node3033 node3033Labels := by
  calc
    mixedMoment B raw40410 raw40410Labels = mixedMoment B raw40410step0 raw40410step0Labels := by
      have hz : ∀ j, raw40410 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40410step0 = (fun i j => raw40410 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40410step0 raw40410; decide +kernel
      have hl : raw40410step0Labels = raw40410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40410 raw40410Labels permutation434 hz
    mixedMoment B raw40410step0 raw40410step0Labels = mixedMoment B raw40410step1 raw40410step1Labels := by
      have ha : raw40410step1 = (fun i j => raw40410step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40410step1 raw40410step0; decide +kernel
      have hl : raw40410step1Labels = raw40410step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40410step0 raw40410step0Labels permutation151 permutation3
    mixedMoment B raw40410step1 raw40410step1Labels = mixedMoment B raw40410step2 raw40410step2Labels := by
      have ha : raw40410step2 = -raw40410step1 := by apply Matrix.ext; change ∀ i j, raw40410step2 i j = -(raw40410step1 i j); unfold raw40410step2 raw40410step1; decide +kernel
      have hl : raw40410step2Labels = raw40410step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3033 node3033Labels := by rfl

theorem canonical40411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40411 raw40411Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw40411 raw40411Labels = mixedMoment B raw40411step0 raw40411step0Labels := by
      have hz : ∀ j, raw40411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40411step0 = (fun i j => raw40411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40411step0 raw40411; decide +kernel
      have hl : raw40411step0Labels = raw40411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40411 raw40411Labels permutation434 hz
    mixedMoment B raw40411step0 raw40411step0Labels = mixedMoment B raw40411step1 raw40411step1Labels := by
      have ha : raw40411step1 = (fun i j => raw40411step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40411step1 raw40411step0; decide +kernel
      have hl : raw40411step1Labels = raw40411step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40411step0 raw40411step0Labels permutation55 permutation6
    mixedMoment B raw40411step1 raw40411step1Labels = mixedMoment B raw40411step2 raw40411step2Labels := by
      have ha : raw40411step2 = -raw40411step1 := by apply Matrix.ext; change ∀ i j, raw40411step2 i j = -(raw40411step1 i j); unfold raw40411step2 raw40411step1; decide +kernel
      have hl : raw40411step2Labels = raw40411step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3156 node3156Labels := by rfl

theorem canonical40412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40412 raw40412Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw40412 raw40412Labels = mixedMoment B raw40412step0 raw40412step0Labels := by
      have hz : ∀ j, raw40412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40412step0 = (fun i j => raw40412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40412step0 raw40412; decide +kernel
      have hl : raw40412step0Labels = raw40412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40412 raw40412Labels permutation434 hz
    mixedMoment B raw40412step0 raw40412step0Labels = mixedMoment B raw40412step1 raw40412step1Labels := by
      have ha : raw40412step1 = (fun i j => raw40412step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40412step1 raw40412step0; decide +kernel
      have hl : raw40412step1Labels = raw40412step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40412step0 raw40412step0Labels permutation32 permutation3
    _ = mixedMoment B node3222 node3222Labels := by rfl

theorem canonical40413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40413 raw40413Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw40413 raw40413Labels = mixedMoment B raw40413step0 raw40413step0Labels := by
      have hz : ∀ j, raw40413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40413step0 = (fun i j => raw40413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40413step0 raw40413; decide +kernel
      have hl : raw40413step0Labels = raw40413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40413 raw40413Labels permutation434 hz
    mixedMoment B raw40413step0 raw40413step0Labels = mixedMoment B raw40413step1 raw40413step1Labels := by
      have ha : raw40413step1 = (fun i j => raw40413step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40413step1 raw40413step0; decide +kernel
      have hl : raw40413step1Labels = raw40413step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40413step0 raw40413step0Labels permutation49 permutation6
    mixedMoment B raw40413step1 raw40413step1Labels = mixedMoment B raw40413step2 raw40413step2Labels := by
      have ha : raw40413step2 = -raw40413step1 := by apply Matrix.ext; change ∀ i j, raw40413step2 i j = -(raw40413step1 i j); unfold raw40413step2 raw40413step1; decide +kernel
      have hl : raw40413step2Labels = raw40413step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3180 node3180Labels := by rfl

theorem canonical40414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40414 raw40414Labels = mixedMoment B node3131 node3131Labels := by
  calc
    mixedMoment B raw40414 raw40414Labels = mixedMoment B raw40414step0 raw40414step0Labels := by
      have hz : ∀ j, raw40414 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40414step0 = (fun i j => raw40414 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40414step0 raw40414; decide +kernel
      have hl : raw40414step0Labels = raw40414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40414 raw40414Labels permutation434 hz
    mixedMoment B raw40414step0 raw40414step0Labels = mixedMoment B raw40414step1 raw40414step1Labels := by
      have ha : raw40414step1 = (fun i j => raw40414step0 (permutation47 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40414step1 raw40414step0; decide +kernel
      have hl : raw40414step1Labels = raw40414step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40414step0 raw40414step0Labels permutation47 permutation6
    mixedMoment B raw40414step1 raw40414step1Labels = mixedMoment B raw40414step2 raw40414step2Labels := by
      have ha : raw40414step2 = -raw40414step1 := by apply Matrix.ext; change ∀ i j, raw40414step2 i j = -(raw40414step1 i j); unfold raw40414step2 raw40414step1; decide +kernel
      have hl : raw40414step2Labels = raw40414step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3131 node3131Labels := by rfl

theorem canonical40415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40415 raw40415Labels = mixedMoment B node3062 node3062Labels := by
  calc
    mixedMoment B raw40415 raw40415Labels = mixedMoment B raw40415step0 raw40415step0Labels := by
      have ha : raw40415step0 = (fun i j => raw40415 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40415step0 raw40415; decide +kernel
      have hl : raw40415step0Labels = raw40415Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40415 raw40415Labels permutation664 permutation3
    mixedMoment B raw40415step0 raw40415step0Labels = mixedMoment B raw40415step1 raw40415step1Labels := by
      have ha : raw40415step1 = -raw40415step0 := by apply Matrix.ext; change ∀ i j, raw40415step1 i j = -(raw40415step0 i j); unfold raw40415step1 raw40415step0; decide +kernel
      have hl : raw40415step1Labels = raw40415step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3062 node3062Labels := by rfl

theorem canonical40416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40416 raw40416Labels = mixedMoment B node3196 node3196Labels := by
  calc
    mixedMoment B raw40416 raw40416Labels = mixedMoment B raw40416step0 raw40416step0Labels := by
      have ha : raw40416step0 = (fun i j => raw40416 (permutation223 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40416step0 raw40416; decide +kernel
      have hl : raw40416step0Labels = raw40416Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40416 raw40416Labels permutation223 permutation6
    mixedMoment B raw40416step0 raw40416step0Labels = mixedMoment B raw40416step1 raw40416step1Labels := by
      have ha : raw40416step1 = -raw40416step0 := by apply Matrix.ext; change ∀ i j, raw40416step1 i j = -(raw40416step0 i j); unfold raw40416step1 raw40416step0; decide +kernel
      have hl : raw40416step1Labels = raw40416step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3196 node3196Labels := by rfl

theorem canonical40417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40417 raw40417Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw40417 raw40417Labels = mixedMoment B raw40417step0 raw40417step0Labels := by
      have ha : raw40417step0 = (fun i j => raw40417 (permutation217 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40417step0 raw40417; decide +kernel
      have hl : raw40417step0Labels = raw40417Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40417 raw40417Labels permutation217 permutation6
    mixedMoment B raw40417step0 raw40417step0Labels = mixedMoment B raw40417step1 raw40417step1Labels := by
      have ha : raw40417step1 = -raw40417step0 := by apply Matrix.ext; change ∀ i j, raw40417step1 i j = -(raw40417step0 i j); unfold raw40417step1 raw40417step0; decide +kernel
      have hl : raw40417step1Labels = raw40417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3202 node3202Labels := by rfl

theorem canonical40418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40418 raw40418Labels = mixedMoment B node3163 node3163Labels := by
  calc
    mixedMoment B raw40418 raw40418Labels = mixedMoment B raw40418step0 raw40418step0Labels := by
      have ha : raw40418step0 = (fun i j => raw40418 (permutation237 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40418step0 raw40418; decide +kernel
      have hl : raw40418step0Labels = raw40418Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40418 raw40418Labels permutation237 permutation6
    mixedMoment B raw40418step0 raw40418step0Labels = mixedMoment B raw40418step1 raw40418step1Labels := by
      have ha : raw40418step1 = -raw40418step0 := by apply Matrix.ext; change ∀ i j, raw40418step1 i j = -(raw40418step0 i j); unfold raw40418step1 raw40418step0; decide +kernel
      have hl : raw40418step1Labels = raw40418step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3163 node3163Labels := by rfl

theorem canonical40419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40419 raw40419Labels = mixedMoment B node3136 node3136Labels := by
  calc
    mixedMoment B raw40419 raw40419Labels = mixedMoment B raw40419step0 raw40419step0Labels := by
      have ha : raw40419step0 = (fun i j => raw40419 (permutation223 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40419step0 raw40419; decide +kernel
      have hl : raw40419step0Labels = raw40419Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40419 raw40419Labels permutation223 permutation6
    mixedMoment B raw40419step0 raw40419step0Labels = mixedMoment B raw40419step1 raw40419step1Labels := by
      have ha : raw40419step1 = -raw40419step0 := by apply Matrix.ext; change ∀ i j, raw40419step1 i j = -(raw40419step0 i j); unfold raw40419step1 raw40419step0; decide +kernel
      have hl : raw40419step1Labels = raw40419step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3136 node3136Labels := by rfl

theorem canonical40420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40420 raw40420Labels = mixedMoment B node3134 node3134Labels := by
  calc
    mixedMoment B raw40420 raw40420Labels = mixedMoment B raw40420step0 raw40420step0Labels := by
      have ha : raw40420step0 = (fun i j => raw40420 (permutation215 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40420step0 raw40420; decide +kernel
      have hl : raw40420step0Labels = raw40420Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40420 raw40420Labels permutation215 permutation6
    mixedMoment B raw40420step0 raw40420step0Labels = mixedMoment B raw40420step1 raw40420step1Labels := by
      have ha : raw40420step1 = -raw40420step0 := by apply Matrix.ext; change ∀ i j, raw40420step1 i j = -(raw40420step0 i j); unfold raw40420step1 raw40420step0; decide +kernel
      have hl : raw40420step1Labels = raw40420step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3134 node3134Labels := by rfl

theorem canonical40421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40421 raw40421Labels = mixedMoment B node3127 node3127Labels := by
  calc
    mixedMoment B raw40421 raw40421Labels = mixedMoment B raw40421step0 raw40421step0Labels := by
      have ha : raw40421step0 = (fun i j => raw40421 (permutation259 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40421step0 raw40421; decide +kernel
      have hl : raw40421step0Labels = raw40421Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40421 raw40421Labels permutation259 permutation6
    mixedMoment B raw40421step0 raw40421step0Labels = mixedMoment B raw40421step1 raw40421step1Labels := by
      have ha : raw40421step1 = -raw40421step0 := by apply Matrix.ext; change ∀ i j, raw40421step1 i j = -(raw40421step0 i j); unfold raw40421step1 raw40421step0; decide +kernel
      have hl : raw40421step1Labels = raw40421step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3127 node3127Labels := by rfl

theorem canonical40422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40422 raw40422Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw40422 raw40422Labels = mixedMoment B raw40422step0 raw40422step0Labels := by
      have ha : raw40422step0 = (fun i j => raw40422 (permutation264 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40422step0 raw40422; decide +kernel
      have hl : raw40422step0Labels = raw40422Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40422 raw40422Labels permutation264 permutation6
    mixedMoment B raw40422step0 raw40422step0Labels = mixedMoment B raw40422step1 raw40422step1Labels := by
      have ha : raw40422step1 = -raw40422step0 := by apply Matrix.ext; change ∀ i j, raw40422step1 i j = -(raw40422step0 i j); unfold raw40422step1 raw40422step0; decide +kernel
      have hl : raw40422step1Labels = raw40422step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3170 node3170Labels := by rfl

theorem canonical40423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40423 raw40423Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw40423 raw40423Labels = mixedMoment B raw40423step0 raw40423step0Labels := by
      have ha : raw40423step0 = (fun i j => raw40423 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40423step0 raw40423; decide +kernel
      have hl : raw40423step0Labels = raw40423Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40423 raw40423Labels permutation152 permutation3
    _ = mixedMoment B node3221 node3221Labels := by rfl

theorem canonical40424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40424 raw40424Labels = mixedMoment B node3161 node3161Labels := by
  calc
    mixedMoment B raw40424 raw40424Labels = mixedMoment B raw40424step0 raw40424step0Labels := by
      have hz : ∀ j, raw40424 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40424step0 = (fun i j => raw40424 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40424step0 raw40424; decide +kernel
      have hl : raw40424step0Labels = raw40424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40424 raw40424Labels permutation434 hz
    mixedMoment B raw40424step0 raw40424step0Labels = mixedMoment B raw40424step1 raw40424step1Labels := by
      have hz : ∀ j, raw40424step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40424step1 = (fun i j => raw40424step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40424step1 raw40424step0; decide +kernel
      have hl : raw40424step1Labels = raw40424step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40424step0 raw40424step0Labels permutation80 hz
    mixedMoment B raw40424step1 raw40424step1Labels = mixedMoment B raw40424step2 raw40424step2Labels := by
      have ha : raw40424step2 = (fun i j => raw40424step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40424step2 raw40424step1; decide +kernel
      have hl : raw40424step2Labels = raw40424step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40424step1 raw40424step1Labels permutation13 permutation6
    mixedMoment B raw40424step2 raw40424step2Labels = mixedMoment B raw40424step3 raw40424step3Labels := by
      have ha : raw40424step3 = -raw40424step2 := by apply Matrix.ext; change ∀ i j, raw40424step3 i j = -(raw40424step2 i j); unfold raw40424step3 raw40424step2; decide +kernel
      have hl : raw40424step3Labels = raw40424step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3161 node3161Labels := by rfl

theorem canonical40425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40425 raw40425Labels = mixedMoment B node2821 node2821Labels := by
  calc
    mixedMoment B raw40425 raw40425Labels = mixedMoment B raw40425step0 raw40425step0Labels := by
      have hz : ∀ j, raw40425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40425step0 = (fun i j => raw40425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40425step0 raw40425; decide +kernel
      have hl : raw40425step0Labels = raw40425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40425 raw40425Labels permutation434 hz
    mixedMoment B raw40425step0 raw40425step0Labels = mixedMoment B raw40425step1 raw40425step1Labels := by
      have hz : ∀ j, raw40425step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40425step1 = (fun i j => raw40425step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40425step1 raw40425step0; decide +kernel
      have hl : raw40425step1Labels = raw40425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40425step0 raw40425step0Labels permutation80 hz
    mixedMoment B raw40425step1 raw40425step1Labels = mixedMoment B raw40425step2 raw40425step2Labels := by
      have ha : raw40425step2 = (fun i j => raw40425step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40425step2 raw40425step1; decide +kernel
      have hl : raw40425step2Labels = raw40425step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40425step1 raw40425step1Labels permutation29 permutation6
    _ = mixedMoment B node2821 node2821Labels := by rfl

theorem canonical40426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40426 raw40426Labels = mixedMoment B node3198 node3198Labels := by
  calc
    mixedMoment B raw40426 raw40426Labels = mixedMoment B raw40426step0 raw40426step0Labels := by
      have hz : ∀ j, raw40426 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40426step0 = (fun i j => raw40426 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40426step0 raw40426; decide +kernel
      have hl : raw40426step0Labels = raw40426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40426 raw40426Labels permutation346 hz
    mixedMoment B raw40426step0 raw40426step0Labels = mixedMoment B raw40426step1 raw40426step1Labels := by
      have ha : raw40426step1 = (fun i j => raw40426step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40426step1 raw40426step0; decide +kernel
      have hl : raw40426step1Labels = raw40426step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40426step0 raw40426step0Labels permutation43 permutation6
    mixedMoment B raw40426step1 raw40426step1Labels = mixedMoment B raw40426step2 raw40426step2Labels := by
      have ha : raw40426step2 = -raw40426step1 := by apply Matrix.ext; change ∀ i j, raw40426step2 i j = -(raw40426step1 i j); unfold raw40426step2 raw40426step1; decide +kernel
      have hl : raw40426step2Labels = raw40426step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3198 node3198Labels := by rfl

theorem canonical40427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40427 raw40427Labels = mixedMoment B node2816 node2816Labels := by
  calc
    mixedMoment B raw40427 raw40427Labels = mixedMoment B raw40427step0 raw40427step0Labels := by
      have hz : ∀ j, raw40427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40427step0 = (fun i j => raw40427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40427step0 raw40427; decide +kernel
      have hl : raw40427step0Labels = raw40427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40427 raw40427Labels permutation346 hz
    mixedMoment B raw40427step0 raw40427step0Labels = mixedMoment B raw40427step1 raw40427step1Labels := by
      have ha : raw40427step1 = (fun i j => raw40427step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40427step1 raw40427step0; decide +kernel
      have hl : raw40427step1Labels = raw40427step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40427step0 raw40427step0Labels permutation137 permutation6
    _ = mixedMoment B node2816 node2816Labels := by rfl

theorem canonical40428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40428 raw40428Labels = mixedMoment B node3138 node3138Labels := by
  calc
    mixedMoment B raw40428 raw40428Labels = mixedMoment B raw40428step0 raw40428step0Labels := by
      have hz : ∀ j, raw40428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40428step0 = (fun i j => raw40428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40428step0 raw40428; decide +kernel
      have hl : raw40428step0Labels = raw40428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40428 raw40428Labels permutation346 hz
    mixedMoment B raw40428step0 raw40428step0Labels = mixedMoment B raw40428step1 raw40428step1Labels := by
      have ha : raw40428step1 = (fun i j => raw40428step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40428step1 raw40428step0; decide +kernel
      have hl : raw40428step1Labels = raw40428step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40428step0 raw40428step0Labels permutation43 permutation6
    mixedMoment B raw40428step1 raw40428step1Labels = mixedMoment B raw40428step2 raw40428step2Labels := by
      have ha : raw40428step2 = -raw40428step1 := by apply Matrix.ext; change ∀ i j, raw40428step2 i j = -(raw40428step1 i j); unfold raw40428step2 raw40428step1; decide +kernel
      have hl : raw40428step2Labels = raw40428step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3138 node3138Labels := by rfl

theorem canonical40429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40429 raw40429Labels = mixedMoment B node2803 node2803Labels := by
  calc
    mixedMoment B raw40429 raw40429Labels = mixedMoment B raw40429step0 raw40429step0Labels := by
      have hz : ∀ j, raw40429 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40429step0 = (fun i j => raw40429 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40429step0 raw40429; decide +kernel
      have hl : raw40429step0Labels = raw40429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40429 raw40429Labels permutation346 hz
    mixedMoment B raw40429step0 raw40429step0Labels = mixedMoment B raw40429step1 raw40429step1Labels := by
      have ha : raw40429step1 = (fun i j => raw40429step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40429step1 raw40429step0; decide +kernel
      have hl : raw40429step1Labels = raw40429step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40429step0 raw40429step0Labels permutation139 permutation6
    _ = mixedMoment B node2803 node2803Labels := by rfl

theorem canonical40430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40430 raw40430Labels = mixedMoment B node3129 node3129Labels := by
  calc
    mixedMoment B raw40430 raw40430Labels = mixedMoment B raw40430step0 raw40430step0Labels := by
      have hz : ∀ j, raw40430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40430step0 = (fun i j => raw40430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40430step0 raw40430; decide +kernel
      have hl : raw40430step0Labels = raw40430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40430 raw40430Labels permutation346 hz
    mixedMoment B raw40430step0 raw40430step0Labels = mixedMoment B raw40430step1 raw40430step1Labels := by
      have ha : raw40430step1 = (fun i j => raw40430step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40430step1 raw40430step0; decide +kernel
      have hl : raw40430step1Labels = raw40430step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40430step0 raw40430step0Labels permutation55 permutation6
    mixedMoment B raw40430step1 raw40430step1Labels = mixedMoment B raw40430step2 raw40430step2Labels := by
      have ha : raw40430step2 = -raw40430step1 := by apply Matrix.ext; change ∀ i j, raw40430step2 i j = -(raw40430step1 i j); unfold raw40430step2 raw40430step1; decide +kernel
      have hl : raw40430step2Labels = raw40430step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3129 node3129Labels := by rfl

theorem canonical40431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40431 raw40431Labels = mixedMoment B node3174 node3174Labels := by
  calc
    mixedMoment B raw40431 raw40431Labels = mixedMoment B raw40431step0 raw40431step0Labels := by
      have hz : ∀ j, raw40431 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40431step0 = (fun i j => raw40431 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40431step0 raw40431; decide +kernel
      have hl : raw40431step0Labels = raw40431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40431 raw40431Labels permutation346 hz
    mixedMoment B raw40431step0 raw40431step0Labels = mixedMoment B raw40431step1 raw40431step1Labels := by
      have ha : raw40431step1 = (fun i j => raw40431step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40431step1 raw40431step0; decide +kernel
      have hl : raw40431step1Labels = raw40431step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40431step0 raw40431step0Labels permutation55 permutation6
    mixedMoment B raw40431step1 raw40431step1Labels = mixedMoment B raw40431step2 raw40431step2Labels := by
      have ha : raw40431step2 = -raw40431step1 := by apply Matrix.ext; change ∀ i j, raw40431step2 i j = -(raw40431step1 i j); unfold raw40431step2 raw40431step1; decide +kernel
      have hl : raw40431step2Labels = raw40431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3174 node3174Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment960 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 960) =
      Integer.Sparse.eval keyMomentRow960 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 960).leftCharge (GramAssembly.key 960).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1971) := by
    have ha : gramCharges (GramAssembly.key 960).leftCharge (GramAssembly.key 960).rightCharge = raw40400 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40400Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40400 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 960).leftCharge (GramAssembly.key 960).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow960, Integer.Sparse.eval]

theorem keyMoment961 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 961) =
      Integer.Sparse.eval keyMomentRow961 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 961).leftCharge (GramAssembly.key 961).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2026) := by
    have ha : gramCharges (GramAssembly.key 961).leftCharge (GramAssembly.key 961).rightCharge = raw40401 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40401Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40401 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 961).leftCharge (GramAssembly.key 961).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow961, Integer.Sparse.eval]

theorem keyMoment962 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 962) =
      Integer.Sparse.eval keyMomentRow962 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 962).leftCharge (GramAssembly.key 962).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2235) := by
    have ha : gramCharges (GramAssembly.key 962).leftCharge (GramAssembly.key 962).rightCharge = raw40402 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40402Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40402 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 962).leftCharge (GramAssembly.key 962).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow962, Integer.Sparse.eval]

theorem keyMoment963 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 963) =
      Integer.Sparse.eval keyMomentRow963 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 963).leftCharge (GramAssembly.key 963).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1976) := by
    have ha : gramCharges (GramAssembly.key 963).leftCharge (GramAssembly.key 963).rightCharge = raw40403 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40403Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40403 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 963).leftCharge (GramAssembly.key 963).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow963, Integer.Sparse.eval]

theorem keyMoment964 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 964) =
      Integer.Sparse.eval keyMomentRow964 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 964).leftCharge (GramAssembly.key 964).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1793) := by
    have ha : gramCharges (GramAssembly.key 964).leftCharge (GramAssembly.key 964).rightCharge = raw40404 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40404Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40404 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 964).leftCharge (GramAssembly.key 964).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow964, Integer.Sparse.eval]

theorem keyMoment965 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 965) =
      Integer.Sparse.eval keyMomentRow965 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 965).leftCharge (GramAssembly.key 965).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1965) := by
    have ha : gramCharges (GramAssembly.key 965).leftCharge (GramAssembly.key 965).rightCharge = raw40405 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40405Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40405 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 965).leftCharge (GramAssembly.key 965).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow965, Integer.Sparse.eval]

theorem keyMoment966 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 966) =
      Integer.Sparse.eval keyMomentRow966 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 966).leftCharge (GramAssembly.key 966).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2010) := by
    have ha : gramCharges (GramAssembly.key 966).leftCharge (GramAssembly.key 966).rightCharge = raw40406 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40406Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40406 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 966).leftCharge (GramAssembly.key 966).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow966, Integer.Sparse.eval]

theorem keyMoment967 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 967) =
      Integer.Sparse.eval keyMomentRow967 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 967).leftCharge (GramAssembly.key 967).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1957) := by
    have ha : gramCharges (GramAssembly.key 967).leftCharge (GramAssembly.key 967).rightCharge = raw40407 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40407Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40407 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 967).leftCharge (GramAssembly.key 967).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow967, Integer.Sparse.eval]

theorem keyMoment968 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 968) =
      Integer.Sparse.eval keyMomentRow968 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 968).leftCharge (GramAssembly.key 968).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2255) := by
    have ha : gramCharges (GramAssembly.key 968).leftCharge (GramAssembly.key 968).rightCharge = raw40408 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40408Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40408 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 968).leftCharge (GramAssembly.key 968).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow968, Integer.Sparse.eval]

theorem keyMoment969 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 969) =
      Integer.Sparse.eval keyMomentRow969 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 969).leftCharge (GramAssembly.key 969).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2716) := by
    have ha : gramCharges (GramAssembly.key 969).leftCharge (GramAssembly.key 969).rightCharge = raw40409 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40409Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40409 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 969).leftCharge (GramAssembly.key 969).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow969, Integer.Sparse.eval]

theorem keyMoment970 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 970) =
      Integer.Sparse.eval keyMomentRow970 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 970).leftCharge (GramAssembly.key 970).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3033) := by
    have ha : gramCharges (GramAssembly.key 970).leftCharge (GramAssembly.key 970).rightCharge = raw40410 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40410Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40410 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 970).leftCharge (GramAssembly.key 970).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow970, Integer.Sparse.eval]

theorem keyMoment971 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 971) =
      Integer.Sparse.eval keyMomentRow971 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 971).leftCharge (GramAssembly.key 971).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3156) := by
    have ha : gramCharges (GramAssembly.key 971).leftCharge (GramAssembly.key 971).rightCharge = raw40411 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40411Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40411 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 971).leftCharge (GramAssembly.key 971).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow971, Integer.Sparse.eval]

theorem keyMoment972 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 972) =
      Integer.Sparse.eval keyMomentRow972 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 972).leftCharge (GramAssembly.key 972).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3222) := by
    have ha : gramCharges (GramAssembly.key 972).leftCharge (GramAssembly.key 972).rightCharge = raw40412 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40412Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40412 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 972).leftCharge (GramAssembly.key 972).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow972, Integer.Sparse.eval]

theorem keyMoment973 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 973) =
      Integer.Sparse.eval keyMomentRow973 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 973).leftCharge (GramAssembly.key 973).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3180) := by
    have ha : gramCharges (GramAssembly.key 973).leftCharge (GramAssembly.key 973).rightCharge = raw40413 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40413Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40413 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 973).leftCharge (GramAssembly.key 973).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow973, Integer.Sparse.eval]

theorem keyMoment974 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 974) =
      Integer.Sparse.eval keyMomentRow974 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 974).leftCharge (GramAssembly.key 974).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3131) := by
    have ha : gramCharges (GramAssembly.key 974).leftCharge (GramAssembly.key 974).rightCharge = raw40414 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40414Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40414 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 974).leftCharge (GramAssembly.key 974).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow974, Integer.Sparse.eval]

theorem keyMoment975 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 975) =
      Integer.Sparse.eval keyMomentRow975 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 975).leftCharge (GramAssembly.key 975).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3062) := by
    have ha : gramCharges (GramAssembly.key 975).leftCharge (GramAssembly.key 975).rightCharge = raw40415 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40415Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40415 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 975).leftCharge (GramAssembly.key 975).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow975, Integer.Sparse.eval]

theorem keyMoment976 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 976) =
      Integer.Sparse.eval keyMomentRow976 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 976).leftCharge (GramAssembly.key 976).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3196) := by
    have ha : gramCharges (GramAssembly.key 976).leftCharge (GramAssembly.key 976).rightCharge = raw40416 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40416Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40416 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 976).leftCharge (GramAssembly.key 976).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow976, Integer.Sparse.eval]

theorem keyMoment977 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 977) =
      Integer.Sparse.eval keyMomentRow977 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 977).leftCharge (GramAssembly.key 977).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3202) := by
    have ha : gramCharges (GramAssembly.key 977).leftCharge (GramAssembly.key 977).rightCharge = raw40417 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40417Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40417 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 977).leftCharge (GramAssembly.key 977).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow977, Integer.Sparse.eval]

theorem keyMoment978 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 978) =
      Integer.Sparse.eval keyMomentRow978 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 978).leftCharge (GramAssembly.key 978).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3163) := by
    have ha : gramCharges (GramAssembly.key 978).leftCharge (GramAssembly.key 978).rightCharge = raw40418 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40418Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40418 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 978).leftCharge (GramAssembly.key 978).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow978, Integer.Sparse.eval]

theorem keyMoment979 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 979) =
      Integer.Sparse.eval keyMomentRow979 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 979).leftCharge (GramAssembly.key 979).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3136) := by
    have ha : gramCharges (GramAssembly.key 979).leftCharge (GramAssembly.key 979).rightCharge = raw40419 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40419Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40419 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 979).leftCharge (GramAssembly.key 979).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow979, Integer.Sparse.eval]

theorem keyMoment980 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 980) =
      Integer.Sparse.eval keyMomentRow980 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 980).leftCharge (GramAssembly.key 980).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3134) := by
    have ha : gramCharges (GramAssembly.key 980).leftCharge (GramAssembly.key 980).rightCharge = raw40420 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40420Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40420 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 980).leftCharge (GramAssembly.key 980).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow980, Integer.Sparse.eval]

theorem keyMoment981 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 981) =
      Integer.Sparse.eval keyMomentRow981 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 981).leftCharge (GramAssembly.key 981).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3127) := by
    have ha : gramCharges (GramAssembly.key 981).leftCharge (GramAssembly.key 981).rightCharge = raw40421 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40421Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40421 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 981).leftCharge (GramAssembly.key 981).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow981, Integer.Sparse.eval]

theorem keyMoment982 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 982) =
      Integer.Sparse.eval keyMomentRow982 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 982).leftCharge (GramAssembly.key 982).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3170) := by
    have ha : gramCharges (GramAssembly.key 982).leftCharge (GramAssembly.key 982).rightCharge = raw40422 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40422Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40422 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 982).leftCharge (GramAssembly.key 982).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow982, Integer.Sparse.eval]

theorem keyMoment983 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 983) =
      Integer.Sparse.eval keyMomentRow983 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 983).leftCharge (GramAssembly.key 983).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3221) := by
    have ha : gramCharges (GramAssembly.key 983).leftCharge (GramAssembly.key 983).rightCharge = raw40423 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40423Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40423 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 983).leftCharge (GramAssembly.key 983).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow983, Integer.Sparse.eval]

theorem keyMoment984 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 984) =
      Integer.Sparse.eval keyMomentRow984 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 984).leftCharge (GramAssembly.key 984).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3161) := by
    have ha : gramCharges (GramAssembly.key 984).leftCharge (GramAssembly.key 984).rightCharge = raw40424 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40424Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40424 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 984).leftCharge (GramAssembly.key 984).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow984, Integer.Sparse.eval]

theorem keyMoment985 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 985) =
      Integer.Sparse.eval keyMomentRow985 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 985).leftCharge (GramAssembly.key 985).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2821) := by
    have ha : gramCharges (GramAssembly.key 985).leftCharge (GramAssembly.key 985).rightCharge = raw40425 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40425Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40425 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 985).leftCharge (GramAssembly.key 985).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow985, Integer.Sparse.eval]

theorem keyMoment986 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 986) =
      Integer.Sparse.eval keyMomentRow986 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 986).leftCharge (GramAssembly.key 986).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3198) := by
    have ha : gramCharges (GramAssembly.key 986).leftCharge (GramAssembly.key 986).rightCharge = raw40426 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40426Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40426 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 986).leftCharge (GramAssembly.key 986).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow986, Integer.Sparse.eval]

theorem keyMoment987 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 987) =
      Integer.Sparse.eval keyMomentRow987 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 987).leftCharge (GramAssembly.key 987).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2816) := by
    have ha : gramCharges (GramAssembly.key 987).leftCharge (GramAssembly.key 987).rightCharge = raw40427 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40427Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40427 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 987).leftCharge (GramAssembly.key 987).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow987, Integer.Sparse.eval]

theorem keyMoment988 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 988) =
      Integer.Sparse.eval keyMomentRow988 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 988).leftCharge (GramAssembly.key 988).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3138) := by
    have ha : gramCharges (GramAssembly.key 988).leftCharge (GramAssembly.key 988).rightCharge = raw40428 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40428Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40428 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 988).leftCharge (GramAssembly.key 988).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow988, Integer.Sparse.eval]

theorem keyMoment989 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 989) =
      Integer.Sparse.eval keyMomentRow989 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 989).leftCharge (GramAssembly.key 989).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2803) := by
    have ha : gramCharges (GramAssembly.key 989).leftCharge (GramAssembly.key 989).rightCharge = raw40429 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40429Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40429 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 989).leftCharge (GramAssembly.key 989).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow989, Integer.Sparse.eval]

theorem keyMoment990 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 990) =
      Integer.Sparse.eval keyMomentRow990 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 990).leftCharge (GramAssembly.key 990).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3129) := by
    have ha : gramCharges (GramAssembly.key 990).leftCharge (GramAssembly.key 990).rightCharge = raw40430 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40430Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40430 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 990).leftCharge (GramAssembly.key 990).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow990, Integer.Sparse.eval]

theorem keyMoment991 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 991) =
      Integer.Sparse.eval keyMomentRow991 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 991).leftCharge (GramAssembly.key 991).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3174) := by
    have ha : gramCharges (GramAssembly.key 991).leftCharge (GramAssembly.key 991).rightCharge = raw40431 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40431Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40431 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 991).leftCharge (GramAssembly.key 991).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow991, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt960 : keyMomentRows (960 : Fin 2886) =
    keyMomentRow960 := by decide +kernel

theorem keyMomentRowsAt961 : keyMomentRows (961 : Fin 2886) =
    keyMomentRow961 := by decide +kernel

theorem keyMomentRowsAt962 : keyMomentRows (962 : Fin 2886) =
    keyMomentRow962 := by decide +kernel

theorem keyMomentRowsAt963 : keyMomentRows (963 : Fin 2886) =
    keyMomentRow963 := by decide +kernel

theorem keyMomentRowsAt964 : keyMomentRows (964 : Fin 2886) =
    keyMomentRow964 := by decide +kernel

theorem keyMomentRowsAt965 : keyMomentRows (965 : Fin 2886) =
    keyMomentRow965 := by decide +kernel

theorem keyMomentRowsAt966 : keyMomentRows (966 : Fin 2886) =
    keyMomentRow966 := by decide +kernel

theorem keyMomentRowsAt967 : keyMomentRows (967 : Fin 2886) =
    keyMomentRow967 := by decide +kernel

theorem keyMomentRowsAt968 : keyMomentRows (968 : Fin 2886) =
    keyMomentRow968 := by decide +kernel

theorem keyMomentRowsAt969 : keyMomentRows (969 : Fin 2886) =
    keyMomentRow969 := by decide +kernel

theorem keyMomentRowsAt970 : keyMomentRows (970 : Fin 2886) =
    keyMomentRow970 := by decide +kernel

theorem keyMomentRowsAt971 : keyMomentRows (971 : Fin 2886) =
    keyMomentRow971 := by decide +kernel

theorem keyMomentRowsAt972 : keyMomentRows (972 : Fin 2886) =
    keyMomentRow972 := by decide +kernel

theorem keyMomentRowsAt973 : keyMomentRows (973 : Fin 2886) =
    keyMomentRow973 := by decide +kernel

theorem keyMomentRowsAt974 : keyMomentRows (974 : Fin 2886) =
    keyMomentRow974 := by decide +kernel

theorem keyMomentRowsAt975 : keyMomentRows (975 : Fin 2886) =
    keyMomentRow975 := by decide +kernel

theorem keyMomentRowsAt976 : keyMomentRows (976 : Fin 2886) =
    keyMomentRow976 := by decide +kernel

theorem keyMomentRowsAt977 : keyMomentRows (977 : Fin 2886) =
    keyMomentRow977 := by decide +kernel

theorem keyMomentRowsAt978 : keyMomentRows (978 : Fin 2886) =
    keyMomentRow978 := by decide +kernel

theorem keyMomentRowsAt979 : keyMomentRows (979 : Fin 2886) =
    keyMomentRow979 := by decide +kernel

theorem keyMomentRowsAt980 : keyMomentRows (980 : Fin 2886) =
    keyMomentRow980 := by decide +kernel

theorem keyMomentRowsAt981 : keyMomentRows (981 : Fin 2886) =
    keyMomentRow981 := by decide +kernel

theorem keyMomentRowsAt982 : keyMomentRows (982 : Fin 2886) =
    keyMomentRow982 := by decide +kernel

theorem keyMomentRowsAt983 : keyMomentRows (983 : Fin 2886) =
    keyMomentRow983 := by decide +kernel

theorem keyMomentRowsAt984 : keyMomentRows (984 : Fin 2886) =
    keyMomentRow984 := by decide +kernel

theorem keyMomentRowsAt985 : keyMomentRows (985 : Fin 2886) =
    keyMomentRow985 := by decide +kernel

theorem keyMomentRowsAt986 : keyMomentRows (986 : Fin 2886) =
    keyMomentRow986 := by decide +kernel

theorem keyMomentRowsAt987 : keyMomentRows (987 : Fin 2886) =
    keyMomentRow987 := by decide +kernel

theorem keyMomentRowsAt988 : keyMomentRows (988 : Fin 2886) =
    keyMomentRow988 := by decide +kernel

theorem keyMomentRowsAt989 : keyMomentRows (989 : Fin 2886) =
    keyMomentRow989 := by decide +kernel

theorem keyMomentRowsAt990 : keyMomentRows (990 : Fin 2886) =
    keyMomentRow990 := by decide +kernel

theorem keyMomentRowsAt991 : keyMomentRows (991 : Fin 2886) =
    keyMomentRow991 := by decide +kernel

theorem keyMomentChunkSound30_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 30) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 960 ∨ k.val = 961 ∨ k.val = 962 ∨ k.val = 963 ∨ k.val = 964 ∨ k.val = 965 ∨ k.val = 966 ∨ k.val = 967 ∨ k.val = 968 ∨ k.val = 969 ∨ k.val = 970 ∨ k.val = 971 ∨ k.val = 972 ∨ k.val = 973 ∨ k.val = 974 ∨ k.val = 975 ∨ k.val = 976 ∨ k.val = 977 ∨ k.val = 978 ∨ k.val = 979 ∨ k.val = 980 ∨ k.val = 981 ∨ k.val = 982 ∨ k.val = 983 ∨ k.val = 984 ∨ k.val = 985 ∨ k.val = 986 ∨ k.val = 987 ∨ k.val = 988 ∨ k.val = 989 ∨ k.val = 990 ∨ k.val = 991 := by omega
  rcases heq with h960 | h961 | h962 | h963 | h964 | h965 | h966 | h967 | h968 | h969 | h970 | h971 | h972 | h973 | h974 | h975 | h976 | h977 | h978 | h979 | h980 | h981 | h982 | h983 | h984 | h985 | h986 | h987 | h988 | h989 | h990 | h991
  · have he : k = (960 : Fin 2886) := Fin.ext h960
    subst k
    rw [keyMomentRowsAt960]
    exact keyMoment960 B hB
  · have he : k = (961 : Fin 2886) := Fin.ext h961
    subst k
    rw [keyMomentRowsAt961]
    exact keyMoment961 B hB
  · have he : k = (962 : Fin 2886) := Fin.ext h962
    subst k
    rw [keyMomentRowsAt962]
    exact keyMoment962 B hB
  · have he : k = (963 : Fin 2886) := Fin.ext h963
    subst k
    rw [keyMomentRowsAt963]
    exact keyMoment963 B hB
  · have he : k = (964 : Fin 2886) := Fin.ext h964
    subst k
    rw [keyMomentRowsAt964]
    exact keyMoment964 B hB
  · have he : k = (965 : Fin 2886) := Fin.ext h965
    subst k
    rw [keyMomentRowsAt965]
    exact keyMoment965 B hB
  · have he : k = (966 : Fin 2886) := Fin.ext h966
    subst k
    rw [keyMomentRowsAt966]
    exact keyMoment966 B hB
  · have he : k = (967 : Fin 2886) := Fin.ext h967
    subst k
    rw [keyMomentRowsAt967]
    exact keyMoment967 B hB
  · have he : k = (968 : Fin 2886) := Fin.ext h968
    subst k
    rw [keyMomentRowsAt968]
    exact keyMoment968 B hB
  · have he : k = (969 : Fin 2886) := Fin.ext h969
    subst k
    rw [keyMomentRowsAt969]
    exact keyMoment969 B hB
  · have he : k = (970 : Fin 2886) := Fin.ext h970
    subst k
    rw [keyMomentRowsAt970]
    exact keyMoment970 B hB
  · have he : k = (971 : Fin 2886) := Fin.ext h971
    subst k
    rw [keyMomentRowsAt971]
    exact keyMoment971 B hB
  · have he : k = (972 : Fin 2886) := Fin.ext h972
    subst k
    rw [keyMomentRowsAt972]
    exact keyMoment972 B hB
  · have he : k = (973 : Fin 2886) := Fin.ext h973
    subst k
    rw [keyMomentRowsAt973]
    exact keyMoment973 B hB
  · have he : k = (974 : Fin 2886) := Fin.ext h974
    subst k
    rw [keyMomentRowsAt974]
    exact keyMoment974 B hB
  · have he : k = (975 : Fin 2886) := Fin.ext h975
    subst k
    rw [keyMomentRowsAt975]
    exact keyMoment975 B hB
  · have he : k = (976 : Fin 2886) := Fin.ext h976
    subst k
    rw [keyMomentRowsAt976]
    exact keyMoment976 B hB
  · have he : k = (977 : Fin 2886) := Fin.ext h977
    subst k
    rw [keyMomentRowsAt977]
    exact keyMoment977 B hB
  · have he : k = (978 : Fin 2886) := Fin.ext h978
    subst k
    rw [keyMomentRowsAt978]
    exact keyMoment978 B hB
  · have he : k = (979 : Fin 2886) := Fin.ext h979
    subst k
    rw [keyMomentRowsAt979]
    exact keyMoment979 B hB
  · have he : k = (980 : Fin 2886) := Fin.ext h980
    subst k
    rw [keyMomentRowsAt980]
    exact keyMoment980 B hB
  · have he : k = (981 : Fin 2886) := Fin.ext h981
    subst k
    rw [keyMomentRowsAt981]
    exact keyMoment981 B hB
  · have he : k = (982 : Fin 2886) := Fin.ext h982
    subst k
    rw [keyMomentRowsAt982]
    exact keyMoment982 B hB
  · have he : k = (983 : Fin 2886) := Fin.ext h983
    subst k
    rw [keyMomentRowsAt983]
    exact keyMoment983 B hB
  · have he : k = (984 : Fin 2886) := Fin.ext h984
    subst k
    rw [keyMomentRowsAt984]
    exact keyMoment984 B hB
  · have he : k = (985 : Fin 2886) := Fin.ext h985
    subst k
    rw [keyMomentRowsAt985]
    exact keyMoment985 B hB
  · have he : k = (986 : Fin 2886) := Fin.ext h986
    subst k
    rw [keyMomentRowsAt986]
    exact keyMoment986 B hB
  · have he : k = (987 : Fin 2886) := Fin.ext h987
    subst k
    rw [keyMomentRowsAt987]
    exact keyMoment987 B hB
  · have he : k = (988 : Fin 2886) := Fin.ext h988
    subst k
    rw [keyMomentRowsAt988]
    exact keyMoment988 B hB
  · have he : k = (989 : Fin 2886) := Fin.ext h989
    subst k
    rw [keyMomentRowsAt989]
    exact keyMoment989 B hB
  · have he : k = (990 : Fin 2886) := Fin.ext h990
    subst k
    rw [keyMomentRowsAt990]
    exact keyMoment990 B hB
  · have he : k = (991 : Fin 2886) := Fin.ext h991
    subst k
    rw [keyMomentRowsAt991]
    exact keyMoment991 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound30_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound30_e_oai
