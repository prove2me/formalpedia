-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:44:08.013839+00:00
-- url     : https://prove2.me/submissions/fcca9c00-a13c-4be1-a6af-79eb418cb6e7

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

theorem mixedMoment_zero_first_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (hA : ∀ i, A i 0 = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i j.succ) (fun j => label j.succ) := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  unfold mixedIntegrand
  rw [Fin.prod_univ_succ]
  have hz : (fun i => A i 0) = 0 := funext hA
  rw [hz, rowFourier_zero, one_mul]

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

theorem delete_zero_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (σ : Equiv.Perm (Fin (n + 1))) (hz : ∀ i, A i (σ 0) = 0) :
    mixedMoment B A label =
      mixedMoment B (fun i j => A i (σ j.succ)) (fun j => label (σ j.succ)) := by
  rw [← mixedMoment_factor_permutation B A label σ]
  exact mixedMoment_zero_first_factor B _ _ hz

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

theorem canonical39450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39450 raw39450Labels = mixedMoment B node2 node2Labels := by
  calc
    mixedMoment B raw39450 raw39450Labels = mixedMoment B raw39450step0 raw39450step0Labels := by
      have hz : ∀ j, raw39450 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39450step0 = (fun i j => raw39450 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39450step0 raw39450; decide +kernel
      have hl : raw39450step0Labels = raw39450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39450 raw39450Labels permutation520 hz
    mixedMoment B raw39450step0 raw39450step0Labels = mixedMoment B raw39450step1 raw39450step1Labels := by
      have hz : ∀ j, raw39450step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39450step1 = (fun i j => raw39450step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39450step1 raw39450step0; decide +kernel
      have hl : raw39450step1Labels = raw39450step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39450step0 raw39450step0Labels permutation104 hz
    mixedMoment B raw39450step1 raw39450step1Labels = mixedMoment B raw39450step2 raw39450step2Labels := by
      have hz : ∀ j, raw39450step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39450step2 = (fun i j => raw39450step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39450step2 raw39450step1; decide +kernel
      have hl : raw39450step2Labels = raw39450step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39450step1 raw39450step1Labels permutation20 hz
    mixedMoment B raw39450step2 raw39450step2Labels = mixedMoment B raw39450step3 raw39450step3Labels := by
      have hz : ∀ j, raw39450step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw39450step3 = (fun i j => raw39450step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw39450step3 raw39450step2; decide +kernel
      have hl : raw39450step3Labels = raw39450step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39450step2 raw39450step2Labels permutation4 hz
    mixedMoment B raw39450step3 raw39450step3Labels = mixedMoment B raw39450step4 raw39450step4Labels := by
      have hz : ∀ i, raw39450step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw39450step4 = (fun i j => raw39450step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw39450step4 raw39450step3; decide +kernel
      have hl : raw39450step4Labels = (fun j => raw39450step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw39450step3 raw39450step3Labels permutation6 hz
    _ = mixedMoment B node2 node2Labels := by rfl

theorem canonical39451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39451 raw39451Labels = mixedMoment B node1 node1Labels := by
  calc
    mixedMoment B raw39451 raw39451Labels = mixedMoment B raw39451step0 raw39451step0Labels := by
      have hz : ∀ j, raw39451 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39451step0 = (fun i j => raw39451 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39451step0 raw39451; decide +kernel
      have hl : raw39451step0Labels = raw39451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39451 raw39451Labels permutation434 hz
    mixedMoment B raw39451step0 raw39451step0Labels = mixedMoment B raw39451step1 raw39451step1Labels := by
      have hz : ∀ j, raw39451step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39451step1 = (fun i j => raw39451step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39451step1 raw39451step0; decide +kernel
      have hl : raw39451step1Labels = raw39451step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39451step0 raw39451step0Labels permutation80 hz
    mixedMoment B raw39451step1 raw39451step1Labels = mixedMoment B raw39451step2 raw39451step2Labels := by
      have hz : ∀ j, raw39451step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39451step2 = (fun i j => raw39451step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39451step2 raw39451step1; decide +kernel
      have hl : raw39451step2Labels = raw39451step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39451step1 raw39451step1Labels permutation14 hz
    mixedMoment B raw39451step2 raw39451step2Labels = mixedMoment B raw39451step3 raw39451step3Labels := by
      have hz : ∀ i, raw39451step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw39451step3 = (fun i j => raw39451step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw39451step3 raw39451step2; decide +kernel
      have hl : raw39451step3Labels = (fun j => raw39451step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw39451step2 raw39451step2Labels permutation6 hz
    _ = mixedMoment B node1 node1Labels := by rfl

theorem canonical39452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39452 raw39452Labels = mixedMoment B node272 node272Labels := by
  calc
    mixedMoment B raw39452 raw39452Labels = mixedMoment B raw39452step0 raw39452step0Labels := by
      have hz : ∀ j, raw39452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39452step0 = (fun i j => raw39452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39452step0 raw39452; decide +kernel
      have hl : raw39452step0Labels = raw39452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39452 raw39452Labels permutation434 hz
    mixedMoment B raw39452step0 raw39452step0Labels = mixedMoment B raw39452step1 raw39452step1Labels := by
      have hz : ∀ j, raw39452step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39452step1 = (fun i j => raw39452step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39452step1 raw39452step0; decide +kernel
      have hl : raw39452step1Labels = raw39452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39452step0 raw39452step0Labels permutation80 hz
    mixedMoment B raw39452step1 raw39452step1Labels = mixedMoment B raw39452step2 raw39452step2Labels := by
      have hz : ∀ j, raw39452step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39452step2 = (fun i j => raw39452step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39452step2 raw39452step1; decide +kernel
      have hl : raw39452step2Labels = raw39452step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39452step1 raw39452step1Labels permutation14 hz
    mixedMoment B raw39452step2 raw39452step2Labels = mixedMoment B raw39452step3 raw39452step3Labels := by
      have ha : raw39452step3 = (fun i j => raw39452step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39452step3 raw39452step2; decide +kernel
      have hl : raw39452step3Labels = raw39452step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39452step2 raw39452step2Labels permutation2 permutation3
    _ = mixedMoment B node272 node272Labels := by rfl

theorem canonical39453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39453 raw39453Labels = mixedMoment B node270 node270Labels := by
  calc
    mixedMoment B raw39453 raw39453Labels = mixedMoment B raw39453step0 raw39453step0Labels := by
      have hz : ∀ j, raw39453 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39453step0 = (fun i j => raw39453 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39453step0 raw39453; decide +kernel
      have hl : raw39453step0Labels = raw39453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39453 raw39453Labels permutation434 hz
    mixedMoment B raw39453step0 raw39453step0Labels = mixedMoment B raw39453step1 raw39453step1Labels := by
      have hz : ∀ j, raw39453step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39453step1 = (fun i j => raw39453step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39453step1 raw39453step0; decide +kernel
      have hl : raw39453step1Labels = raw39453step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39453step0 raw39453step0Labels permutation80 hz
    mixedMoment B raw39453step1 raw39453step1Labels = mixedMoment B raw39453step2 raw39453step2Labels := by
      have hz : ∀ j, raw39453step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39453step2 = (fun i j => raw39453step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39453step2 raw39453step1; decide +kernel
      have hl : raw39453step2Labels = raw39453step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39453step1 raw39453step1Labels permutation14 hz
    mixedMoment B raw39453step2 raw39453step2Labels = mixedMoment B raw39453step3 raw39453step3Labels := by
      have ha : raw39453step3 = (fun i j => raw39453step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39453step3 raw39453step2; decide +kernel
      have hl : raw39453step3Labels = raw39453step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39453step2 raw39453step2Labels permutation3 permutation5
    mixedMoment B raw39453step3 raw39453step3Labels = mixedMoment B raw39453step4 raw39453step4Labels := by
      have ha : raw39453step4 = -raw39453step3 := by apply Matrix.ext; change ∀ i j, raw39453step4 i j = -(raw39453step3 i j); unfold raw39453step4 raw39453step3; decide +kernel
      have hl : raw39453step4Labels = raw39453step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node270 node270Labels := by rfl

theorem canonical39454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39454 raw39454Labels = mixedMoment B node266 node266Labels := by
  calc
    mixedMoment B raw39454 raw39454Labels = mixedMoment B raw39454step0 raw39454step0Labels := by
      have hz : ∀ j, raw39454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39454step0 = (fun i j => raw39454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39454step0 raw39454; decide +kernel
      have hl : raw39454step0Labels = raw39454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39454 raw39454Labels permutation346 hz
    mixedMoment B raw39454step0 raw39454step0Labels = mixedMoment B raw39454step1 raw39454step1Labels := by
      have hz : ∀ j, raw39454step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39454step1 = (fun i j => raw39454step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39454step1 raw39454step0; decide +kernel
      have hl : raw39454step1Labels = raw39454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39454step0 raw39454step0Labels permutation56 hz
    mixedMoment B raw39454step1 raw39454step1Labels = mixedMoment B raw39454step2 raw39454step2Labels := by
      have ha : raw39454step2 = (fun i j => raw39454step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39454step2 raw39454step1; decide +kernel
      have hl : raw39454step2Labels = raw39454step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39454step1 raw39454step1Labels permutation8 permutation3
    _ = mixedMoment B node266 node266Labels := by rfl

theorem canonical39455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39455 raw39455Labels = mixedMoment B node267 node267Labels := by
  calc
    mixedMoment B raw39455 raw39455Labels = mixedMoment B raw39455step0 raw39455step0Labels := by
      have hz : ∀ j, raw39455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39455step0 = (fun i j => raw39455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39455step0 raw39455; decide +kernel
      have hl : raw39455step0Labels = raw39455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39455 raw39455Labels permutation346 hz
    mixedMoment B raw39455step0 raw39455step0Labels = mixedMoment B raw39455step1 raw39455step1Labels := by
      have hz : ∀ j, raw39455step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39455step1 = (fun i j => raw39455step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39455step1 raw39455step0; decide +kernel
      have hl : raw39455step1Labels = raw39455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39455step0 raw39455step0Labels permutation56 hz
    mixedMoment B raw39455step1 raw39455step1Labels = mixedMoment B raw39455step2 raw39455step2Labels := by
      have ha : raw39455step2 = (fun i j => raw39455step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39455step2 raw39455step1; decide +kernel
      have hl : raw39455step2Labels = raw39455step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39455step1 raw39455step1Labels permutation8 permutation3
    _ = mixedMoment B node267 node267Labels := by rfl

theorem canonical39456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39456 raw39456Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw39456 raw39456Labels = mixedMoment B raw39456step0 raw39456step0Labels := by
      have hz : ∀ j, raw39456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39456step0 = (fun i j => raw39456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39456step0 raw39456; decide +kernel
      have hl : raw39456step0Labels = raw39456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39456 raw39456Labels permutation346 hz
    mixedMoment B raw39456step0 raw39456step0Labels = mixedMoment B raw39456step1 raw39456step1Labels := by
      have hz : ∀ j, raw39456step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39456step1 = (fun i j => raw39456step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39456step1 raw39456step0; decide +kernel
      have hl : raw39456step1Labels = raw39456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39456step0 raw39456step0Labels permutation56 hz
    mixedMoment B raw39456step1 raw39456step1Labels = mixedMoment B raw39456step2 raw39456step2Labels := by
      have ha : raw39456step2 = (fun i j => raw39456step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39456step2 raw39456step1; decide +kernel
      have hl : raw39456step2Labels = raw39456step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39456step1 raw39456step1Labels permutation8 permutation3
    _ = mixedMoment B node268 node268Labels := by rfl

theorem canonical39457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39457 raw39457Labels = mixedMoment B node269 node269Labels := by
  calc
    mixedMoment B raw39457 raw39457Labels = mixedMoment B raw39457step0 raw39457step0Labels := by
      have hz : ∀ j, raw39457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39457step0 = (fun i j => raw39457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39457step0 raw39457; decide +kernel
      have hl : raw39457step0Labels = raw39457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39457 raw39457Labels permutation346 hz
    mixedMoment B raw39457step0 raw39457step0Labels = mixedMoment B raw39457step1 raw39457step1Labels := by
      have hz : ∀ j, raw39457step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39457step1 = (fun i j => raw39457step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39457step1 raw39457step0; decide +kernel
      have hl : raw39457step1Labels = raw39457step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39457step0 raw39457step0Labels permutation56 hz
    mixedMoment B raw39457step1 raw39457step1Labels = mixedMoment B raw39457step2 raw39457step2Labels := by
      have ha : raw39457step2 = (fun i j => raw39457step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39457step2 raw39457step1; decide +kernel
      have hl : raw39457step2Labels = raw39457step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39457step1 raw39457step1Labels permutation8 permutation3
    _ = mixedMoment B node269 node269Labels := by rfl

theorem canonical39458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39458 raw39458Labels = mixedMoment B node267 node267Labels := by
  calc
    mixedMoment B raw39458 raw39458Labels = mixedMoment B raw39458step0 raw39458step0Labels := by
      have hz : ∀ j, raw39458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39458step0 = (fun i j => raw39458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39458step0 raw39458; decide +kernel
      have hl : raw39458step0Labels = raw39458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39458 raw39458Labels permutation346 hz
    mixedMoment B raw39458step0 raw39458step0Labels = mixedMoment B raw39458step1 raw39458step1Labels := by
      have hz : ∀ j, raw39458step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39458step1 = (fun i j => raw39458step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39458step1 raw39458step0; decide +kernel
      have hl : raw39458step1Labels = raw39458step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39458step0 raw39458step0Labels permutation56 hz
    mixedMoment B raw39458step1 raw39458step1Labels = mixedMoment B raw39458step2 raw39458step2Labels := by
      have ha : raw39458step2 = (fun i j => raw39458step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39458step2 raw39458step1; decide +kernel
      have hl : raw39458step2Labels = raw39458step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39458step1 raw39458step1Labels permutation8 permutation5
    mixedMoment B raw39458step2 raw39458step2Labels = mixedMoment B raw39458step3 raw39458step3Labels := by
      have ha : raw39458step3 = -raw39458step2 := by apply Matrix.ext; change ∀ i j, raw39458step3 i j = -(raw39458step2 i j); unfold raw39458step3 raw39458step2; decide +kernel
      have hl : raw39458step3Labels = raw39458step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node267 node267Labels := by rfl

theorem canonical39459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39459 raw39459Labels = mixedMoment B node0 node0Labels := by
  calc
    mixedMoment B raw39459 raw39459Labels = mixedMoment B raw39459step0 raw39459step0Labels := by
      have hz : ∀ j, raw39459 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39459step0 = (fun i j => raw39459 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39459step0 raw39459; decide +kernel
      have hl : raw39459step0Labels = raw39459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39459 raw39459Labels permutation346 hz
    mixedMoment B raw39459step0 raw39459step0Labels = mixedMoment B raw39459step1 raw39459step1Labels := by
      have hz : ∀ j, raw39459step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39459step1 = (fun i j => raw39459step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39459step1 raw39459step0; decide +kernel
      have hl : raw39459step1Labels = raw39459step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39459step0 raw39459step0Labels permutation56 hz
    mixedMoment B raw39459step1 raw39459step1Labels = mixedMoment B raw39459step2 raw39459step2Labels := by
      have hz : ∀ i, raw39459step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw39459step2 = (fun i j => raw39459step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw39459step2 raw39459step1; decide +kernel
      have hl : raw39459step2Labels = (fun j => raw39459step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw39459step1 raw39459step1Labels permutation6 hz
    _ = mixedMoment B node0 node0Labels := by rfl

theorem canonical39460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39460 raw39460Labels = mixedMoment B node261 node261Labels := by
  calc
    mixedMoment B raw39460 raw39460Labels = mixedMoment B raw39460step0 raw39460step0Labels := by
      have hz : ∀ j, raw39460 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39460step0 = (fun i j => raw39460 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39460step0 raw39460; decide +kernel
      have hl : raw39460step0Labels = raw39460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39460 raw39460Labels permutation265 hz
    mixedMoment B raw39460step0 raw39460step0Labels = mixedMoment B raw39460step1 raw39460step1Labels := by
      have ha : raw39460step1 = (fun i j => raw39460step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39460step1 raw39460step0; decide +kernel
      have hl : raw39460step1Labels = raw39460step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39460step0 raw39460step0Labels permutation32 permutation3
    _ = mixedMoment B node261 node261Labels := by rfl

theorem canonical39461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39461 raw39461Labels = mixedMoment B node265 node265Labels := by
  calc
    mixedMoment B raw39461 raw39461Labels = mixedMoment B raw39461step0 raw39461step0Labels := by
      have hz : ∀ j, raw39461 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39461step0 = (fun i j => raw39461 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39461step0 raw39461; decide +kernel
      have hl : raw39461step0Labels = raw39461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39461 raw39461Labels permutation265 hz
    mixedMoment B raw39461step0 raw39461step0Labels = mixedMoment B raw39461step1 raw39461step1Labels := by
      have ha : raw39461step1 = (fun i j => raw39461step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39461step1 raw39461step0; decide +kernel
      have hl : raw39461step1Labels = raw39461step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39461step0 raw39461step0Labels permutation32 permutation3
    _ = mixedMoment B node265 node265Labels := by rfl

theorem canonical39462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39462 raw39462Labels = mixedMoment B node261 node261Labels := by
  calc
    mixedMoment B raw39462 raw39462Labels = mixedMoment B raw39462step0 raw39462step0Labels := by
      have hz : ∀ j, raw39462 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39462step0 = (fun i j => raw39462 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39462step0 raw39462; decide +kernel
      have hl : raw39462step0Labels = raw39462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39462 raw39462Labels permutation265 hz
    mixedMoment B raw39462step0 raw39462step0Labels = mixedMoment B raw39462step1 raw39462step1Labels := by
      have ha : raw39462step1 = (fun i j => raw39462step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39462step1 raw39462step0; decide +kernel
      have hl : raw39462step1Labels = raw39462step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39462step0 raw39462step0Labels permutation41 permutation5
    mixedMoment B raw39462step1 raw39462step1Labels = mixedMoment B raw39462step2 raw39462step2Labels := by
      have ha : raw39462step2 = -raw39462step1 := by apply Matrix.ext; change ∀ i j, raw39462step2 i j = -(raw39462step1 i j); unfold raw39462step2 raw39462step1; decide +kernel
      have hl : raw39462step2Labels = raw39462step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node261 node261Labels := by rfl

theorem canonical39463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39463 raw39463Labels = mixedMoment B node259 node259Labels := by
  calc
    mixedMoment B raw39463 raw39463Labels = mixedMoment B raw39463step0 raw39463step0Labels := by
      have ha : raw39463step0 = (fun i j => raw39463 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39463step0 raw39463; decide +kernel
      have hl : raw39463step0Labels = raw39463Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39463 raw39463Labels permutation152 permutation3
    _ = mixedMoment B node259 node259Labels := by rfl

theorem canonical39464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39464 raw39464Labels = mixedMoment B node5502 node5502Labels := by
  calc
    mixedMoment B raw39464 raw39464Labels = mixedMoment B raw39464step0 raw39464step0Labels := by
      have hz : ∀ j, raw39464 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39464step0 = (fun i j => raw39464 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39464step0 raw39464; decide +kernel
      have hl : raw39464step0Labels = raw39464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39464 raw39464Labels permutation520 hz
    mixedMoment B raw39464step0 raw39464step0Labels = mixedMoment B raw39464step1 raw39464step1Labels := by
      have hz : ∀ j, raw39464step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39464step1 = (fun i j => raw39464step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39464step1 raw39464step0; decide +kernel
      have hl : raw39464step1Labels = raw39464step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39464step0 raw39464step0Labels permutation104 hz
    mixedMoment B raw39464step1 raw39464step1Labels = mixedMoment B raw39464step2 raw39464step2Labels := by
      have hz : ∀ j, raw39464step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39464step2 = (fun i j => raw39464step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39464step2 raw39464step1; decide +kernel
      have hl : raw39464step2Labels = raw39464step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39464step1 raw39464step1Labels permutation20 hz
    mixedMoment B raw39464step2 raw39464step2Labels = mixedMoment B raw39464step3 raw39464step3Labels := by
      have ha : raw39464step3 = (fun i j => raw39464step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39464step3 raw39464step2; decide +kernel
      have hl : raw39464step3Labels = raw39464step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39464step2 raw39464step2Labels permutation7 permutation3
    mixedMoment B raw39464step3 raw39464step3Labels = mixedMoment B raw39464step4 raw39464step4Labels := by
      have ha : raw39464step4 = -raw39464step3 := by apply Matrix.ext; change ∀ i j, raw39464step4 i j = -(raw39464step3 i j); unfold raw39464step4 raw39464step3; decide +kernel
      have hl : raw39464step4Labels = raw39464step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5502 node5502Labels := by rfl

theorem canonical39465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39465 raw39465Labels = mixedMoment B node388 node388Labels := by
  calc
    mixedMoment B raw39465 raw39465Labels = mixedMoment B raw39465step0 raw39465step0Labels := by
      have hz : ∀ j, raw39465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39465step0 = (fun i j => raw39465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39465step0 raw39465; decide +kernel
      have hl : raw39465step0Labels = raw39465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39465 raw39465Labels permutation434 hz
    mixedMoment B raw39465step0 raw39465step0Labels = mixedMoment B raw39465step1 raw39465step1Labels := by
      have hz : ∀ j, raw39465step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39465step1 = (fun i j => raw39465step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39465step1 raw39465step0; decide +kernel
      have hl : raw39465step1Labels = raw39465step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39465step0 raw39465step0Labels permutation80 hz
    mixedMoment B raw39465step1 raw39465step1Labels = mixedMoment B raw39465step2 raw39465step2Labels := by
      have ha : raw39465step2 = (fun i j => raw39465step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39465step2 raw39465step1; decide +kernel
      have hl : raw39465step2Labels = raw39465step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39465step1 raw39465step1Labels permutation8 permutation3
    _ = mixedMoment B node388 node388Labels := by rfl

theorem canonical39466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39466 raw39466Labels = mixedMoment B node389 node389Labels := by
  calc
    mixedMoment B raw39466 raw39466Labels = mixedMoment B raw39466step0 raw39466step0Labels := by
      have hz : ∀ j, raw39466 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39466step0 = (fun i j => raw39466 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39466step0 raw39466; decide +kernel
      have hl : raw39466step0Labels = raw39466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39466 raw39466Labels permutation434 hz
    mixedMoment B raw39466step0 raw39466step0Labels = mixedMoment B raw39466step1 raw39466step1Labels := by
      have hz : ∀ j, raw39466step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39466step1 = (fun i j => raw39466step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39466step1 raw39466step0; decide +kernel
      have hl : raw39466step1Labels = raw39466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39466step0 raw39466step0Labels permutation80 hz
    mixedMoment B raw39466step1 raw39466step1Labels = mixedMoment B raw39466step2 raw39466step2Labels := by
      have ha : raw39466step2 = (fun i j => raw39466step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39466step2 raw39466step1; decide +kernel
      have hl : raw39466step2Labels = raw39466step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39466step1 raw39466step1Labels permutation8 permutation3
    _ = mixedMoment B node389 node389Labels := by rfl

theorem canonical39467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39467 raw39467Labels = mixedMoment B node391 node391Labels := by
  calc
    mixedMoment B raw39467 raw39467Labels = mixedMoment B raw39467step0 raw39467step0Labels := by
      have hz : ∀ j, raw39467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39467step0 = (fun i j => raw39467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39467step0 raw39467; decide +kernel
      have hl : raw39467step0Labels = raw39467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39467 raw39467Labels permutation434 hz
    mixedMoment B raw39467step0 raw39467step0Labels = mixedMoment B raw39467step1 raw39467step1Labels := by
      have hz : ∀ j, raw39467step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39467step1 = (fun i j => raw39467step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39467step1 raw39467step0; decide +kernel
      have hl : raw39467step1Labels = raw39467step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39467step0 raw39467step0Labels permutation80 hz
    mixedMoment B raw39467step1 raw39467step1Labels = mixedMoment B raw39467step2 raw39467step2Labels := by
      have ha : raw39467step2 = (fun i j => raw39467step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39467step2 raw39467step1; decide +kernel
      have hl : raw39467step2Labels = raw39467step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39467step1 raw39467step1Labels permutation8 permutation3
    _ = mixedMoment B node391 node391Labels := by rfl

theorem canonical39468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39468 raw39468Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw39468 raw39468Labels = mixedMoment B raw39468step0 raw39468step0Labels := by
      have hz : ∀ j, raw39468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39468step0 = (fun i j => raw39468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39468step0 raw39468; decide +kernel
      have hl : raw39468step0Labels = raw39468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39468 raw39468Labels permutation346 hz
    mixedMoment B raw39468step0 raw39468step0Labels = mixedMoment B raw39468step1 raw39468step1Labels := by
      have ha : raw39468step1 = (fun i j => raw39468step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39468step1 raw39468step0; decide +kernel
      have hl : raw39468step1Labels = raw39468step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39468step0 raw39468step0Labels permutation32 permutation3
    _ = mixedMoment B node377 node377Labels := by rfl

theorem canonical39469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39469 raw39469Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39469 raw39469Labels = mixedMoment B raw39469step0 raw39469step0Labels := by
      have hz : ∀ j, raw39469 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39469step0 = (fun i j => raw39469 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39469step0 raw39469; decide +kernel
      have hl : raw39469step0Labels = raw39469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39469 raw39469Labels permutation346 hz
    mixedMoment B raw39469step0 raw39469step0Labels = mixedMoment B raw39469step1 raw39469step1Labels := by
      have ha : raw39469step1 = (fun i j => raw39469step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39469step1 raw39469step0; decide +kernel
      have hl : raw39469step1Labels = raw39469step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39469step0 raw39469step0Labels permutation32 permutation3
    _ = mixedMoment B node384 node384Labels := by rfl

theorem canonical39470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39470 raw39470Labels = mixedMoment B node386 node386Labels := by
  calc
    mixedMoment B raw39470 raw39470Labels = mixedMoment B raw39470step0 raw39470step0Labels := by
      have hz : ∀ j, raw39470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39470step0 = (fun i j => raw39470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39470step0 raw39470; decide +kernel
      have hl : raw39470step0Labels = raw39470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39470 raw39470Labels permutation346 hz
    mixedMoment B raw39470step0 raw39470step0Labels = mixedMoment B raw39470step1 raw39470step1Labels := by
      have ha : raw39470step1 = (fun i j => raw39470step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39470step1 raw39470step0; decide +kernel
      have hl : raw39470step1Labels = raw39470step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39470step0 raw39470step0Labels permutation32 permutation3
    _ = mixedMoment B node386 node386Labels := by rfl

theorem canonical39471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39471 raw39471Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw39471 raw39471Labels = mixedMoment B raw39471step0 raw39471step0Labels := by
      have hz : ∀ j, raw39471 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39471step0 = (fun i j => raw39471 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39471step0 raw39471; decide +kernel
      have hl : raw39471step0Labels = raw39471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39471 raw39471Labels permutation346 hz
    mixedMoment B raw39471step0 raw39471step0Labels = mixedMoment B raw39471step1 raw39471step1Labels := by
      have ha : raw39471step1 = (fun i j => raw39471step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39471step1 raw39471step0; decide +kernel
      have hl : raw39471step1Labels = raw39471step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39471step0 raw39471step0Labels permutation32 permutation3
    _ = mixedMoment B node387 node387Labels := by rfl

theorem canonical39472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39472 raw39472Labels = mixedMoment B node375 node375Labels := by
  calc
    mixedMoment B raw39472 raw39472Labels = mixedMoment B raw39472step0 raw39472step0Labels := by
      have ha : raw39472step0 = (fun i j => raw39472 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39472step0 raw39472; decide +kernel
      have hl : raw39472step0Labels = raw39472Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39472 raw39472Labels permutation152 permutation3
    _ = mixedMoment B node375 node375Labels := by rfl

theorem canonical39473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39473 raw39473Labels = mixedMoment B node382 node382Labels := by
  calc
    mixedMoment B raw39473 raw39473Labels = mixedMoment B raw39473step0 raw39473step0Labels := by
      have ha : raw39473step0 = (fun i j => raw39473 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39473step0 raw39473; decide +kernel
      have hl : raw39473step0Labels = raw39473Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39473 raw39473Labels permutation152 permutation3
    _ = mixedMoment B node382 node382Labels := by rfl

theorem canonical39474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39474 raw39474Labels = mixedMoment B node415 node415Labels := by
  calc
    mixedMoment B raw39474 raw39474Labels = mixedMoment B raw39474step0 raw39474step0Labels := by
      have hz : ∀ j, raw39474 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39474step0 = (fun i j => raw39474 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39474step0 raw39474; decide +kernel
      have hl : raw39474step0Labels = raw39474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39474 raw39474Labels permutation434 hz
    mixedMoment B raw39474step0 raw39474step0Labels = mixedMoment B raw39474step1 raw39474step1Labels := by
      have hz : ∀ j, raw39474step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39474step1 = (fun i j => raw39474step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39474step1 raw39474step0; decide +kernel
      have hl : raw39474step1Labels = raw39474step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39474step0 raw39474step0Labels permutation80 hz
    mixedMoment B raw39474step1 raw39474step1Labels = mixedMoment B raw39474step2 raw39474step2Labels := by
      have hz : ∀ j, raw39474step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39474step2 = (fun i j => raw39474step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39474step2 raw39474step1; decide +kernel
      have hl : raw39474step2Labels = raw39474step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39474step1 raw39474step1Labels permutation14 hz
    mixedMoment B raw39474step2 raw39474step2Labels = mixedMoment B raw39474step3 raw39474step3Labels := by
      have ha : raw39474step3 = (fun i j => raw39474step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39474step3 raw39474step2; decide +kernel
      have hl : raw39474step3Labels = raw39474step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39474step2 raw39474step2Labels permutation2 permutation3
    _ = mixedMoment B node415 node415Labels := by rfl

theorem canonical39475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39475 raw39475Labels = mixedMoment B node419 node419Labels := by
  calc
    mixedMoment B raw39475 raw39475Labels = mixedMoment B raw39475step0 raw39475step0Labels := by
      have hz : ∀ j, raw39475 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39475step0 = (fun i j => raw39475 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39475step0 raw39475; decide +kernel
      have hl : raw39475step0Labels = raw39475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39475 raw39475Labels permutation434 hz
    mixedMoment B raw39475step0 raw39475step0Labels = mixedMoment B raw39475step1 raw39475step1Labels := by
      have hz : ∀ j, raw39475step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39475step1 = (fun i j => raw39475step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39475step1 raw39475step0; decide +kernel
      have hl : raw39475step1Labels = raw39475step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39475step0 raw39475step0Labels permutation80 hz
    mixedMoment B raw39475step1 raw39475step1Labels = mixedMoment B raw39475step2 raw39475step2Labels := by
      have hz : ∀ j, raw39475step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39475step2 = (fun i j => raw39475step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39475step2 raw39475step1; decide +kernel
      have hl : raw39475step2Labels = raw39475step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39475step1 raw39475step1Labels permutation14 hz
    mixedMoment B raw39475step2 raw39475step2Labels = mixedMoment B raw39475step3 raw39475step3Labels := by
      have ha : raw39475step3 = (fun i j => raw39475step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39475step3 raw39475step2; decide +kernel
      have hl : raw39475step3Labels = raw39475step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39475step2 raw39475step2Labels permutation2 permutation3
    _ = mixedMoment B node419 node419Labels := by rfl

theorem canonical39476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39476 raw39476Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw39476 raw39476Labels = mixedMoment B raw39476step0 raw39476step0Labels := by
      have hz : ∀ j, raw39476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39476step0 = (fun i j => raw39476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39476step0 raw39476; decide +kernel
      have hl : raw39476step0Labels = raw39476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39476 raw39476Labels permutation434 hz
    mixedMoment B raw39476step0 raw39476step0Labels = mixedMoment B raw39476step1 raw39476step1Labels := by
      have hz : ∀ j, raw39476step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39476step1 = (fun i j => raw39476step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39476step1 raw39476step0; decide +kernel
      have hl : raw39476step1Labels = raw39476step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39476step0 raw39476step0Labels permutation80 hz
    mixedMoment B raw39476step1 raw39476step1Labels = mixedMoment B raw39476step2 raw39476step2Labels := by
      have hz : ∀ j, raw39476step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39476step2 = (fun i j => raw39476step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39476step2 raw39476step1; decide +kernel
      have hl : raw39476step2Labels = raw39476step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39476step1 raw39476step1Labels permutation14 hz
    mixedMoment B raw39476step2 raw39476step2Labels = mixedMoment B raw39476step3 raw39476step3Labels := by
      have ha : raw39476step3 = (fun i j => raw39476step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39476step3 raw39476step2; decide +kernel
      have hl : raw39476step3Labels = raw39476step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39476step2 raw39476step2Labels permutation2 permutation3
    _ = mixedMoment B node420 node420Labels := by rfl

theorem canonical39477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39477 raw39477Labels = mixedMoment B node421 node421Labels := by
  calc
    mixedMoment B raw39477 raw39477Labels = mixedMoment B raw39477step0 raw39477step0Labels := by
      have hz : ∀ j, raw39477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39477step0 = (fun i j => raw39477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39477step0 raw39477; decide +kernel
      have hl : raw39477step0Labels = raw39477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39477 raw39477Labels permutation434 hz
    mixedMoment B raw39477step0 raw39477step0Labels = mixedMoment B raw39477step1 raw39477step1Labels := by
      have hz : ∀ j, raw39477step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39477step1 = (fun i j => raw39477step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39477step1 raw39477step0; decide +kernel
      have hl : raw39477step1Labels = raw39477step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39477step0 raw39477step0Labels permutation80 hz
    mixedMoment B raw39477step1 raw39477step1Labels = mixedMoment B raw39477step2 raw39477step2Labels := by
      have hz : ∀ j, raw39477step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39477step2 = (fun i j => raw39477step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39477step2 raw39477step1; decide +kernel
      have hl : raw39477step2Labels = raw39477step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39477step1 raw39477step1Labels permutation14 hz
    mixedMoment B raw39477step2 raw39477step2Labels = mixedMoment B raw39477step3 raw39477step3Labels := by
      have ha : raw39477step3 = (fun i j => raw39477step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39477step3 raw39477step2; decide +kernel
      have hl : raw39477step3Labels = raw39477step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39477step2 raw39477step2Labels permutation2 permutation3
    _ = mixedMoment B node421 node421Labels := by rfl

theorem canonical39478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39478 raw39478Labels = mixedMoment B node402 node402Labels := by
  calc
    mixedMoment B raw39478 raw39478Labels = mixedMoment B raw39478step0 raw39478step0Labels := by
      have hz : ∀ j, raw39478 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39478step0 = (fun i j => raw39478 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39478step0 raw39478; decide +kernel
      have hl : raw39478step0Labels = raw39478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39478 raw39478Labels permutation346 hz
    mixedMoment B raw39478step0 raw39478step0Labels = mixedMoment B raw39478step1 raw39478step1Labels := by
      have hz : ∀ j, raw39478step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39478step1 = (fun i j => raw39478step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39478step1 raw39478step0; decide +kernel
      have hl : raw39478step1Labels = raw39478step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39478step0 raw39478step0Labels permutation56 hz
    mixedMoment B raw39478step1 raw39478step1Labels = mixedMoment B raw39478step2 raw39478step2Labels := by
      have ha : raw39478step2 = (fun i j => raw39478step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39478step2 raw39478step1; decide +kernel
      have hl : raw39478step2Labels = raw39478step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39478step1 raw39478step1Labels permutation8 permutation3
    _ = mixedMoment B node402 node402Labels := by rfl

theorem canonical39479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39479 raw39479Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw39479 raw39479Labels = mixedMoment B raw39479step0 raw39479step0Labels := by
      have hz : ∀ j, raw39479 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39479step0 = (fun i j => raw39479 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39479step0 raw39479; decide +kernel
      have hl : raw39479step0Labels = raw39479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39479 raw39479Labels permutation346 hz
    mixedMoment B raw39479step0 raw39479step0Labels = mixedMoment B raw39479step1 raw39479step1Labels := by
      have hz : ∀ j, raw39479step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39479step1 = (fun i j => raw39479step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39479step1 raw39479step0; decide +kernel
      have hl : raw39479step1Labels = raw39479step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39479step0 raw39479step0Labels permutation56 hz
    mixedMoment B raw39479step1 raw39479step1Labels = mixedMoment B raw39479step2 raw39479step2Labels := by
      have ha : raw39479step2 = (fun i j => raw39479step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39479step2 raw39479step1; decide +kernel
      have hl : raw39479step2Labels = raw39479step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39479step1 raw39479step1Labels permutation8 permutation3
    _ = mixedMoment B node405 node405Labels := by rfl

theorem canonical39480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39480 raw39480Labels = mixedMoment B node391 node391Labels := by
  calc
    mixedMoment B raw39480 raw39480Labels = mixedMoment B raw39480step0 raw39480step0Labels := by
      have hz : ∀ j, raw39480 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39480step0 = (fun i j => raw39480 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39480step0 raw39480; decide +kernel
      have hl : raw39480step0Labels = raw39480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39480 raw39480Labels permutation346 hz
    mixedMoment B raw39480step0 raw39480step0Labels = mixedMoment B raw39480step1 raw39480step1Labels := by
      have hz : ∀ j, raw39480step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39480step1 = (fun i j => raw39480step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39480step1 raw39480step0; decide +kernel
      have hl : raw39480step1Labels = raw39480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39480step0 raw39480step0Labels permutation56 hz
    mixedMoment B raw39480step1 raw39480step1Labels = mixedMoment B raw39480step2 raw39480step2Labels := by
      have ha : raw39480step2 = (fun i j => raw39480step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39480step2 raw39480step1; decide +kernel
      have hl : raw39480step2Labels = raw39480step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39480step1 raw39480step1Labels permutation30 permutation7
    _ = mixedMoment B node391 node391Labels := by rfl

theorem canonical39481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39481 raw39481Labels = mixedMoment B node406 node406Labels := by
  calc
    mixedMoment B raw39481 raw39481Labels = mixedMoment B raw39481step0 raw39481step0Labels := by
      have hz : ∀ j, raw39481 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39481step0 = (fun i j => raw39481 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39481step0 raw39481; decide +kernel
      have hl : raw39481step0Labels = raw39481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39481 raw39481Labels permutation346 hz
    mixedMoment B raw39481step0 raw39481step0Labels = mixedMoment B raw39481step1 raw39481step1Labels := by
      have hz : ∀ j, raw39481step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39481step1 = (fun i j => raw39481step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39481step1 raw39481step0; decide +kernel
      have hl : raw39481step1Labels = raw39481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39481step0 raw39481step0Labels permutation56 hz
    mixedMoment B raw39481step1 raw39481step1Labels = mixedMoment B raw39481step2 raw39481step2Labels := by
      have ha : raw39481step2 = (fun i j => raw39481step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39481step2 raw39481step1; decide +kernel
      have hl : raw39481step2Labels = raw39481step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39481step1 raw39481step1Labels permutation31 permutation4
    _ = mixedMoment B node406 node406Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 0) =
      Integer.Sparse.eval keyMomentRow0 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 0).leftCharge (GramAssembly.key 0).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 2) := by
    have ha : gramCharges (GramAssembly.key 0).leftCharge (GramAssembly.key 0).rightCharge = raw39450 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39450Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39450 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 0).leftCharge (GramAssembly.key 0).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow0, Integer.Sparse.eval]

theorem keyMoment1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1) =
      Integer.Sparse.eval keyMomentRow1 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1).leftCharge (GramAssembly.key 1).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 1) := by
    have ha : gramCharges (GramAssembly.key 1).leftCharge (GramAssembly.key 1).rightCharge = raw39451 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39451Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39451 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1).leftCharge (GramAssembly.key 1).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow1, Integer.Sparse.eval]

theorem keyMoment2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2) =
      Integer.Sparse.eval keyMomentRow2 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2).leftCharge (GramAssembly.key 2).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 272) := by
    have ha : gramCharges (GramAssembly.key 2).leftCharge (GramAssembly.key 2).rightCharge = raw39452 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39452Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39452 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2).leftCharge (GramAssembly.key 2).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow2, Integer.Sparse.eval]

theorem keyMoment3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 3) =
      Integer.Sparse.eval keyMomentRow3 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 3).leftCharge (GramAssembly.key 3).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 270) := by
    have ha : gramCharges (GramAssembly.key 3).leftCharge (GramAssembly.key 3).rightCharge = raw39453 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39453Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39453 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 3).leftCharge (GramAssembly.key 3).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow3, Integer.Sparse.eval]

theorem keyMoment4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 4) =
      Integer.Sparse.eval keyMomentRow4 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 4).leftCharge (GramAssembly.key 4).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 266) := by
    have ha : gramCharges (GramAssembly.key 4).leftCharge (GramAssembly.key 4).rightCharge = raw39454 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39454Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39454 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 4).leftCharge (GramAssembly.key 4).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow4, Integer.Sparse.eval]

theorem keyMoment5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 5) =
      Integer.Sparse.eval keyMomentRow5 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 5).leftCharge (GramAssembly.key 5).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 267) := by
    have ha : gramCharges (GramAssembly.key 5).leftCharge (GramAssembly.key 5).rightCharge = raw39455 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39455Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39455 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 5).leftCharge (GramAssembly.key 5).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow5, Integer.Sparse.eval]

theorem keyMoment6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 6) =
      Integer.Sparse.eval keyMomentRow6 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 6).leftCharge (GramAssembly.key 6).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 268) := by
    have ha : gramCharges (GramAssembly.key 6).leftCharge (GramAssembly.key 6).rightCharge = raw39456 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39456Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39456 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 6).leftCharge (GramAssembly.key 6).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow6, Integer.Sparse.eval]

theorem keyMoment7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 7) =
      Integer.Sparse.eval keyMomentRow7 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 7).leftCharge (GramAssembly.key 7).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 269) := by
    have ha : gramCharges (GramAssembly.key 7).leftCharge (GramAssembly.key 7).rightCharge = raw39457 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39457Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39457 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 7).leftCharge (GramAssembly.key 7).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow7, Integer.Sparse.eval]

theorem keyMoment8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 8) =
      Integer.Sparse.eval keyMomentRow8 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 8).leftCharge (GramAssembly.key 8).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 267) := by
    have ha : gramCharges (GramAssembly.key 8).leftCharge (GramAssembly.key 8).rightCharge = raw39458 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39458Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39458 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 8).leftCharge (GramAssembly.key 8).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow8, Integer.Sparse.eval]

theorem keyMoment9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 9) =
      Integer.Sparse.eval keyMomentRow9 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 9).leftCharge (GramAssembly.key 9).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 0) := by
    have ha : gramCharges (GramAssembly.key 9).leftCharge (GramAssembly.key 9).rightCharge = raw39459 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39459Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39459 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 9).leftCharge (GramAssembly.key 9).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow9, Integer.Sparse.eval]

theorem keyMoment10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 10) =
      Integer.Sparse.eval keyMomentRow10 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 10).leftCharge (GramAssembly.key 10).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 261) := by
    have ha : gramCharges (GramAssembly.key 10).leftCharge (GramAssembly.key 10).rightCharge = raw39460 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39460Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39460 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 10).leftCharge (GramAssembly.key 10).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow10, Integer.Sparse.eval]

theorem keyMoment11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 11) =
      Integer.Sparse.eval keyMomentRow11 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 11).leftCharge (GramAssembly.key 11).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 265) := by
    have ha : gramCharges (GramAssembly.key 11).leftCharge (GramAssembly.key 11).rightCharge = raw39461 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39461Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39461 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 11).leftCharge (GramAssembly.key 11).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow11, Integer.Sparse.eval]

theorem keyMoment12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 12) =
      Integer.Sparse.eval keyMomentRow12 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 12).leftCharge (GramAssembly.key 12).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 261) := by
    have ha : gramCharges (GramAssembly.key 12).leftCharge (GramAssembly.key 12).rightCharge = raw39462 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39462Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39462 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 12).leftCharge (GramAssembly.key 12).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow12, Integer.Sparse.eval]

theorem keyMoment13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 13) =
      Integer.Sparse.eval keyMomentRow13 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 13).leftCharge (GramAssembly.key 13).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 259) := by
    have ha : gramCharges (GramAssembly.key 13).leftCharge (GramAssembly.key 13).rightCharge = raw39463 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39463Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39463 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 13).leftCharge (GramAssembly.key 13).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow13, Integer.Sparse.eval]

theorem keyMoment14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 14) =
      Integer.Sparse.eval keyMomentRow14 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 14).leftCharge (GramAssembly.key 14).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 0) := by
    have ha : gramCharges (GramAssembly.key 14).leftCharge (GramAssembly.key 14).rightCharge = raw39464 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39464Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39464 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 14).leftCharge (GramAssembly.key 14).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow14, Integer.Sparse.eval]

theorem keyMoment15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 15) =
      Integer.Sparse.eval keyMomentRow15 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 15).leftCharge (GramAssembly.key 15).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 388) := by
    have ha : gramCharges (GramAssembly.key 15).leftCharge (GramAssembly.key 15).rightCharge = raw39465 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39465Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39465 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 15).leftCharge (GramAssembly.key 15).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow15, Integer.Sparse.eval]

theorem keyMoment16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 16) =
      Integer.Sparse.eval keyMomentRow16 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 16).leftCharge (GramAssembly.key 16).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 389) := by
    have ha : gramCharges (GramAssembly.key 16).leftCharge (GramAssembly.key 16).rightCharge = raw39466 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39466Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39466 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 16).leftCharge (GramAssembly.key 16).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow16, Integer.Sparse.eval]

theorem keyMoment17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 17) =
      Integer.Sparse.eval keyMomentRow17 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 17).leftCharge (GramAssembly.key 17).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 391) := by
    have ha : gramCharges (GramAssembly.key 17).leftCharge (GramAssembly.key 17).rightCharge = raw39467 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39467Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39467 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 17).leftCharge (GramAssembly.key 17).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow17, Integer.Sparse.eval]

theorem keyMoment18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 18) =
      Integer.Sparse.eval keyMomentRow18 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 18).leftCharge (GramAssembly.key 18).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 377) := by
    have ha : gramCharges (GramAssembly.key 18).leftCharge (GramAssembly.key 18).rightCharge = raw39468 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39468Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39468 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 18).leftCharge (GramAssembly.key 18).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow18, Integer.Sparse.eval]

theorem keyMoment19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 19) =
      Integer.Sparse.eval keyMomentRow19 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 19).leftCharge (GramAssembly.key 19).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 19).leftCharge (GramAssembly.key 19).rightCharge = raw39469 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39469Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39469 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 19).leftCharge (GramAssembly.key 19).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow19, Integer.Sparse.eval]

theorem keyMoment20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 20) =
      Integer.Sparse.eval keyMomentRow20 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 20).leftCharge (GramAssembly.key 20).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 386) := by
    have ha : gramCharges (GramAssembly.key 20).leftCharge (GramAssembly.key 20).rightCharge = raw39470 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39470Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39470 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 20).leftCharge (GramAssembly.key 20).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow20, Integer.Sparse.eval]

theorem keyMoment21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 21) =
      Integer.Sparse.eval keyMomentRow21 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 21).leftCharge (GramAssembly.key 21).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 387) := by
    have ha : gramCharges (GramAssembly.key 21).leftCharge (GramAssembly.key 21).rightCharge = raw39471 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39471Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39471 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 21).leftCharge (GramAssembly.key 21).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow21, Integer.Sparse.eval]

theorem keyMoment22 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 22) =
      Integer.Sparse.eval keyMomentRow22 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 22).leftCharge (GramAssembly.key 22).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 375) := by
    have ha : gramCharges (GramAssembly.key 22).leftCharge (GramAssembly.key 22).rightCharge = raw39472 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39472Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39472 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 22).leftCharge (GramAssembly.key 22).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow22, Integer.Sparse.eval]

theorem keyMoment23 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 23) =
      Integer.Sparse.eval keyMomentRow23 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 23).leftCharge (GramAssembly.key 23).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 382) := by
    have ha : gramCharges (GramAssembly.key 23).leftCharge (GramAssembly.key 23).rightCharge = raw39473 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39473Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39473 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 23).leftCharge (GramAssembly.key 23).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow23, Integer.Sparse.eval]

theorem keyMoment24 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 24) =
      Integer.Sparse.eval keyMomentRow24 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 24).leftCharge (GramAssembly.key 24).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 415) := by
    have ha : gramCharges (GramAssembly.key 24).leftCharge (GramAssembly.key 24).rightCharge = raw39474 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39474Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39474 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 24).leftCharge (GramAssembly.key 24).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow24, Integer.Sparse.eval]

theorem keyMoment25 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 25) =
      Integer.Sparse.eval keyMomentRow25 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 25).leftCharge (GramAssembly.key 25).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 419) := by
    have ha : gramCharges (GramAssembly.key 25).leftCharge (GramAssembly.key 25).rightCharge = raw39475 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39475Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39475 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 25).leftCharge (GramAssembly.key 25).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow25, Integer.Sparse.eval]

theorem keyMoment26 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 26) =
      Integer.Sparse.eval keyMomentRow26 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 26).leftCharge (GramAssembly.key 26).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 420) := by
    have ha : gramCharges (GramAssembly.key 26).leftCharge (GramAssembly.key 26).rightCharge = raw39476 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39476Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39476 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 26).leftCharge (GramAssembly.key 26).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow26, Integer.Sparse.eval]

theorem keyMoment27 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 27) =
      Integer.Sparse.eval keyMomentRow27 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 27).leftCharge (GramAssembly.key 27).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 421) := by
    have ha : gramCharges (GramAssembly.key 27).leftCharge (GramAssembly.key 27).rightCharge = raw39477 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39477Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39477 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 27).leftCharge (GramAssembly.key 27).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow27, Integer.Sparse.eval]

theorem keyMoment28 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 28) =
      Integer.Sparse.eval keyMomentRow28 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 28).leftCharge (GramAssembly.key 28).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 402) := by
    have ha : gramCharges (GramAssembly.key 28).leftCharge (GramAssembly.key 28).rightCharge = raw39478 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39478Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39478 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 28).leftCharge (GramAssembly.key 28).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow28, Integer.Sparse.eval]

theorem keyMoment29 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 29) =
      Integer.Sparse.eval keyMomentRow29 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 29).leftCharge (GramAssembly.key 29).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 405) := by
    have ha : gramCharges (GramAssembly.key 29).leftCharge (GramAssembly.key 29).rightCharge = raw39479 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39479Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39479 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 29).leftCharge (GramAssembly.key 29).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow29, Integer.Sparse.eval]

theorem keyMoment30 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 30) =
      Integer.Sparse.eval keyMomentRow30 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 30).leftCharge (GramAssembly.key 30).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 391) := by
    have ha : gramCharges (GramAssembly.key 30).leftCharge (GramAssembly.key 30).rightCharge = raw39480 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39480Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39480 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 30).leftCharge (GramAssembly.key 30).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow30, Integer.Sparse.eval]

theorem keyMoment31 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 31) =
      Integer.Sparse.eval keyMomentRow31 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 31).leftCharge (GramAssembly.key 31).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 406) := by
    have ha : gramCharges (GramAssembly.key 31).leftCharge (GramAssembly.key 31).rightCharge = raw39481 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39481Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39481 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 31).leftCharge (GramAssembly.key 31).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow31, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt0 : keyMomentRows (0 : Fin 2886) =
    keyMomentRow0 := by decide +kernel

theorem keyMomentRowsAt1 : keyMomentRows (1 : Fin 2886) =
    keyMomentRow1 := by decide +kernel

theorem keyMomentRowsAt2 : keyMomentRows (2 : Fin 2886) =
    keyMomentRow2 := by decide +kernel

theorem keyMomentRowsAt3 : keyMomentRows (3 : Fin 2886) =
    keyMomentRow3 := by decide +kernel

theorem keyMomentRowsAt4 : keyMomentRows (4 : Fin 2886) =
    keyMomentRow4 := by decide +kernel

theorem keyMomentRowsAt5 : keyMomentRows (5 : Fin 2886) =
    keyMomentRow5 := by decide +kernel

theorem keyMomentRowsAt6 : keyMomentRows (6 : Fin 2886) =
    keyMomentRow6 := by decide +kernel

theorem keyMomentRowsAt7 : keyMomentRows (7 : Fin 2886) =
    keyMomentRow7 := by decide +kernel

theorem keyMomentRowsAt8 : keyMomentRows (8 : Fin 2886) =
    keyMomentRow8 := by decide +kernel

theorem keyMomentRowsAt9 : keyMomentRows (9 : Fin 2886) =
    keyMomentRow9 := by decide +kernel

theorem keyMomentRowsAt10 : keyMomentRows (10 : Fin 2886) =
    keyMomentRow10 := by decide +kernel

theorem keyMomentRowsAt11 : keyMomentRows (11 : Fin 2886) =
    keyMomentRow11 := by decide +kernel

theorem keyMomentRowsAt12 : keyMomentRows (12 : Fin 2886) =
    keyMomentRow12 := by decide +kernel

theorem keyMomentRowsAt13 : keyMomentRows (13 : Fin 2886) =
    keyMomentRow13 := by decide +kernel

theorem keyMomentRowsAt14 : keyMomentRows (14 : Fin 2886) =
    keyMomentRow14 := by decide +kernel

theorem keyMomentRowsAt15 : keyMomentRows (15 : Fin 2886) =
    keyMomentRow15 := by decide +kernel

theorem keyMomentRowsAt16 : keyMomentRows (16 : Fin 2886) =
    keyMomentRow16 := by decide +kernel

theorem keyMomentRowsAt17 : keyMomentRows (17 : Fin 2886) =
    keyMomentRow17 := by decide +kernel

theorem keyMomentRowsAt18 : keyMomentRows (18 : Fin 2886) =
    keyMomentRow18 := by decide +kernel

theorem keyMomentRowsAt19 : keyMomentRows (19 : Fin 2886) =
    keyMomentRow19 := by decide +kernel

theorem keyMomentRowsAt20 : keyMomentRows (20 : Fin 2886) =
    keyMomentRow20 := by decide +kernel

theorem keyMomentRowsAt21 : keyMomentRows (21 : Fin 2886) =
    keyMomentRow21 := by decide +kernel

theorem keyMomentRowsAt22 : keyMomentRows (22 : Fin 2886) =
    keyMomentRow22 := by decide +kernel

theorem keyMomentRowsAt23 : keyMomentRows (23 : Fin 2886) =
    keyMomentRow23 := by decide +kernel

theorem keyMomentRowsAt24 : keyMomentRows (24 : Fin 2886) =
    keyMomentRow24 := by decide +kernel

theorem keyMomentRowsAt25 : keyMomentRows (25 : Fin 2886) =
    keyMomentRow25 := by decide +kernel

theorem keyMomentRowsAt26 : keyMomentRows (26 : Fin 2886) =
    keyMomentRow26 := by decide +kernel

theorem keyMomentRowsAt27 : keyMomentRows (27 : Fin 2886) =
    keyMomentRow27 := by decide +kernel

theorem keyMomentRowsAt28 : keyMomentRows (28 : Fin 2886) =
    keyMomentRow28 := by decide +kernel

theorem keyMomentRowsAt29 : keyMomentRows (29 : Fin 2886) =
    keyMomentRow29 := by decide +kernel

theorem keyMomentRowsAt30 : keyMomentRows (30 : Fin 2886) =
    keyMomentRow30 := by decide +kernel

theorem keyMomentRowsAt31 : keyMomentRows (31 : Fin 2886) =
    keyMomentRow31 := by decide +kernel

theorem keyMomentChunkSound0_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 0) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 ∨ k.val = 4 ∨ k.val = 5 ∨ k.val = 6 ∨ k.val = 7 ∨ k.val = 8 ∨ k.val = 9 ∨ k.val = 10 ∨ k.val = 11 ∨ k.val = 12 ∨ k.val = 13 ∨ k.val = 14 ∨ k.val = 15 ∨ k.val = 16 ∨ k.val = 17 ∨ k.val = 18 ∨ k.val = 19 ∨ k.val = 20 ∨ k.val = 21 ∨ k.val = 22 ∨ k.val = 23 ∨ k.val = 24 ∨ k.val = 25 ∨ k.val = 26 ∨ k.val = 27 ∨ k.val = 28 ∨ k.val = 29 ∨ k.val = 30 ∨ k.val = 31 := by omega
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
  · have he : k = (0 : Fin 2886) := Fin.ext h0
    subst k
    rw [keyMomentRowsAt0]
    exact keyMoment0 B hB
  · have he : k = (1 : Fin 2886) := Fin.ext h1
    subst k
    rw [keyMomentRowsAt1]
    exact keyMoment1 B hB
  · have he : k = (2 : Fin 2886) := Fin.ext h2
    subst k
    rw [keyMomentRowsAt2]
    exact keyMoment2 B hB
  · have he : k = (3 : Fin 2886) := Fin.ext h3
    subst k
    rw [keyMomentRowsAt3]
    exact keyMoment3 B hB
  · have he : k = (4 : Fin 2886) := Fin.ext h4
    subst k
    rw [keyMomentRowsAt4]
    exact keyMoment4 B hB
  · have he : k = (5 : Fin 2886) := Fin.ext h5
    subst k
    rw [keyMomentRowsAt5]
    exact keyMoment5 B hB
  · have he : k = (6 : Fin 2886) := Fin.ext h6
    subst k
    rw [keyMomentRowsAt6]
    exact keyMoment6 B hB
  · have he : k = (7 : Fin 2886) := Fin.ext h7
    subst k
    rw [keyMomentRowsAt7]
    exact keyMoment7 B hB
  · have he : k = (8 : Fin 2886) := Fin.ext h8
    subst k
    rw [keyMomentRowsAt8]
    exact keyMoment8 B hB
  · have he : k = (9 : Fin 2886) := Fin.ext h9
    subst k
    rw [keyMomentRowsAt9]
    exact keyMoment9 B hB
  · have he : k = (10 : Fin 2886) := Fin.ext h10
    subst k
    rw [keyMomentRowsAt10]
    exact keyMoment10 B hB
  · have he : k = (11 : Fin 2886) := Fin.ext h11
    subst k
    rw [keyMomentRowsAt11]
    exact keyMoment11 B hB
  · have he : k = (12 : Fin 2886) := Fin.ext h12
    subst k
    rw [keyMomentRowsAt12]
    exact keyMoment12 B hB
  · have he : k = (13 : Fin 2886) := Fin.ext h13
    subst k
    rw [keyMomentRowsAt13]
    exact keyMoment13 B hB
  · have he : k = (14 : Fin 2886) := Fin.ext h14
    subst k
    rw [keyMomentRowsAt14]
    exact keyMoment14 B hB
  · have he : k = (15 : Fin 2886) := Fin.ext h15
    subst k
    rw [keyMomentRowsAt15]
    exact keyMoment15 B hB
  · have he : k = (16 : Fin 2886) := Fin.ext h16
    subst k
    rw [keyMomentRowsAt16]
    exact keyMoment16 B hB
  · have he : k = (17 : Fin 2886) := Fin.ext h17
    subst k
    rw [keyMomentRowsAt17]
    exact keyMoment17 B hB
  · have he : k = (18 : Fin 2886) := Fin.ext h18
    subst k
    rw [keyMomentRowsAt18]
    exact keyMoment18 B hB
  · have he : k = (19 : Fin 2886) := Fin.ext h19
    subst k
    rw [keyMomentRowsAt19]
    exact keyMoment19 B hB
  · have he : k = (20 : Fin 2886) := Fin.ext h20
    subst k
    rw [keyMomentRowsAt20]
    exact keyMoment20 B hB
  · have he : k = (21 : Fin 2886) := Fin.ext h21
    subst k
    rw [keyMomentRowsAt21]
    exact keyMoment21 B hB
  · have he : k = (22 : Fin 2886) := Fin.ext h22
    subst k
    rw [keyMomentRowsAt22]
    exact keyMoment22 B hB
  · have he : k = (23 : Fin 2886) := Fin.ext h23
    subst k
    rw [keyMomentRowsAt23]
    exact keyMoment23 B hB
  · have he : k = (24 : Fin 2886) := Fin.ext h24
    subst k
    rw [keyMomentRowsAt24]
    exact keyMoment24 B hB
  · have he : k = (25 : Fin 2886) := Fin.ext h25
    subst k
    rw [keyMomentRowsAt25]
    exact keyMoment25 B hB
  · have he : k = (26 : Fin 2886) := Fin.ext h26
    subst k
    rw [keyMomentRowsAt26]
    exact keyMoment26 B hB
  · have he : k = (27 : Fin 2886) := Fin.ext h27
    subst k
    rw [keyMomentRowsAt27]
    exact keyMoment27 B hB
  · have he : k = (28 : Fin 2886) := Fin.ext h28
    subst k
    rw [keyMomentRowsAt28]
    exact keyMoment28 B hB
  · have he : k = (29 : Fin 2886) := Fin.ext h29
    subst k
    rw [keyMomentRowsAt29]
    exact keyMoment29 B hB
  · have he : k = (30 : Fin 2886) := Fin.ext h30
    subst k
    rw [keyMomentRowsAt30]
    exact keyMoment30 B hB
  · have he : k = (31 : Fin 2886) := Fin.ext h31
    subst k
    rw [keyMomentRowsAt31]
    exact keyMoment31 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound0_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound0_e_oai
