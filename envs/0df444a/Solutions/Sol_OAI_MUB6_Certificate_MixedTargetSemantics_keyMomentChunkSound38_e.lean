-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound38_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:54:06.999461+00:00
-- url     : https://prove2.me/submissions/5f4caefe-35d1-4896-b9d6-eb34e8dd2ef7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E111
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E117
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical317
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40648 raw40648Labels = mixedMoment B node3908 node3908Labels := by
  calc
    mixedMoment B raw40648 raw40648Labels = mixedMoment B raw40648step0 raw40648step0Labels := by
      have hz : ∀ j, raw40648 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40648step0 = (fun i j => raw40648 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40648step0 raw40648; decide +kernel
      have hl : raw40648step0Labels = raw40648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40648 raw40648Labels permutation434 hz
    mixedMoment B raw40648step0 raw40648step0Labels = mixedMoment B raw40648step1 raw40648step1Labels := by
      have hz : ∀ j, raw40648step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40648step1 = (fun i j => raw40648step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40648step1 raw40648step0; decide +kernel
      have hl : raw40648step1Labels = raw40648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40648step0 raw40648step0Labels permutation80 hz
    mixedMoment B raw40648step1 raw40648step1Labels = mixedMoment B raw40648step2 raw40648step2Labels := by
      have ha : raw40648step2 = (fun i j => raw40648step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40648step2 raw40648step1; decide +kernel
      have hl : raw40648step2Labels = raw40648step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40648step1 raw40648step1Labels permutation8 permutation3
    _ = mixedMoment B node3908 node3908Labels := by rfl

theorem canonical40649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40649 raw40649Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw40649 raw40649Labels = mixedMoment B raw40649step0 raw40649step0Labels := by
      have hz : ∀ j, raw40649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40649step0 = (fun i j => raw40649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40649step0 raw40649; decide +kernel
      have hl : raw40649step0Labels = raw40649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40649 raw40649Labels permutation346 hz
    mixedMoment B raw40649step0 raw40649step0Labels = mixedMoment B raw40649step1 raw40649step1Labels := by
      have ha : raw40649step1 = (fun i j => raw40649step0 (permutation116 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40649step1 raw40649step0; decide +kernel
      have hl : raw40649step1Labels = raw40649step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40649step0 raw40649step0Labels permutation116 permutation6
    mixedMoment B raw40649step1 raw40649step1Labels = mixedMoment B raw40649step2 raw40649step2Labels := by
      have ha : raw40649step2 = -raw40649step1 := by apply Matrix.ext; change ∀ i j, raw40649step2 i j = -(raw40649step1 i j); unfold raw40649step2 raw40649step1; decide +kernel
      have hl : raw40649step2Labels = raw40649step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical40650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40650 raw40650Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw40650 raw40650Labels = mixedMoment B raw40650step0 raw40650step0Labels := by
      have hz : ∀ j, raw40650 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40650step0 = (fun i j => raw40650 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40650step0 raw40650; decide +kernel
      have hl : raw40650step0Labels = raw40650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40650 raw40650Labels permutation346 hz
    mixedMoment B raw40650step0 raw40650step0Labels = mixedMoment B raw40650step1 raw40650step1Labels := by
      have ha : raw40650step1 = (fun i j => raw40650step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40650step1 raw40650step0; decide +kernel
      have hl : raw40650step1Labels = raw40650step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40650step0 raw40650step0Labels permutation32 permutation3
    _ = mixedMoment B node3903 node3903Labels := by rfl

theorem canonical40651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40651 raw40651Labels = mixedMoment B node3904 node3904Labels := by
  calc
    mixedMoment B raw40651 raw40651Labels = mixedMoment B raw40651step0 raw40651step0Labels := by
      have hz : ∀ j, raw40651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40651step0 = (fun i j => raw40651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40651step0 raw40651; decide +kernel
      have hl : raw40651step0Labels = raw40651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40651 raw40651Labels permutation346 hz
    mixedMoment B raw40651step0 raw40651step0Labels = mixedMoment B raw40651step1 raw40651step1Labels := by
      have ha : raw40651step1 = (fun i j => raw40651step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40651step1 raw40651step0; decide +kernel
      have hl : raw40651step1Labels = raw40651step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40651step0 raw40651step0Labels permutation32 permutation3
    _ = mixedMoment B node3904 node3904Labels := by rfl

theorem canonical40652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40652 raw40652Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw40652 raw40652Labels = mixedMoment B raw40652step0 raw40652step0Labels := by
      have hz : ∀ j, raw40652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40652step0 = (fun i j => raw40652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40652step0 raw40652; decide +kernel
      have hl : raw40652step0Labels = raw40652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40652 raw40652Labels permutation346 hz
    mixedMoment B raw40652step0 raw40652step0Labels = mixedMoment B raw40652step1 raw40652step1Labels := by
      have ha : raw40652step1 = (fun i j => raw40652step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40652step1 raw40652step0; decide +kernel
      have hl : raw40652step1Labels = raw40652step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40652step0 raw40652step0Labels permutation32 permutation3
    _ = mixedMoment B node3906 node3906Labels := by rfl

theorem canonical40653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40653 raw40653Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw40653 raw40653Labels = mixedMoment B raw40653step0 raw40653step0Labels := by
      have hz : ∀ j, raw40653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40653step0 = (fun i j => raw40653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40653step0 raw40653; decide +kernel
      have hl : raw40653step0Labels = raw40653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40653 raw40653Labels permutation346 hz
    mixedMoment B raw40653step0 raw40653step0Labels = mixedMoment B raw40653step1 raw40653step1Labels := by
      have ha : raw40653step1 = (fun i j => raw40653step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40653step1 raw40653step0; decide +kernel
      have hl : raw40653step1Labels = raw40653step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40653step0 raw40653step0Labels permutation83 permutation6
    mixedMoment B raw40653step1 raw40653step1Labels = mixedMoment B raw40653step2 raw40653step2Labels := by
      have ha : raw40653step2 = -raw40653step1 := by apply Matrix.ext; change ∀ i j, raw40653step2 i j = -(raw40653step1 i j); unfold raw40653step2 raw40653step1; decide +kernel
      have hl : raw40653step2Labels = raw40653step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical40654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40654 raw40654Labels = mixedMoment B node3901 node3901Labels := by
  calc
    mixedMoment B raw40654 raw40654Labels = mixedMoment B raw40654step0 raw40654step0Labels := by
      have ha : raw40654step0 = (fun i j => raw40654 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40654step0 raw40654; decide +kernel
      have hl : raw40654step0Labels = raw40654Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40654 raw40654Labels permutation152 permutation3
    _ = mixedMoment B node3901 node3901Labels := by rfl

theorem canonical40655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40655 raw40655Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw40655 raw40655Labels = mixedMoment B raw40655step0 raw40655step0Labels := by
      have ha : raw40655step0 = (fun i j => raw40655 (permutation468 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40655step0 raw40655; decide +kernel
      have hl : raw40655step0Labels = raw40655Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40655 raw40655Labels permutation468 permutation6
    mixedMoment B raw40655step0 raw40655step0Labels = mixedMoment B raw40655step1 raw40655step1Labels := by
      have ha : raw40655step1 = -raw40655step0 := by apply Matrix.ext; change ∀ i j, raw40655step1 i j = -(raw40655step0 i j); unfold raw40655step1 raw40655step0; decide +kernel
      have hl : raw40655step1Labels = raw40655step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3812 node3812Labels := by rfl

theorem canonical40656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40656 raw40656Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw40656 raw40656Labels = mixedMoment B raw40656step0 raw40656step0Labels := by
      have hz : ∀ j, raw40656 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40656step0 = (fun i j => raw40656 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40656step0 raw40656; decide +kernel
      have hl : raw40656step0Labels = raw40656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40656 raw40656Labels permutation434 hz
    mixedMoment B raw40656step0 raw40656step0Labels = mixedMoment B raw40656step1 raw40656step1Labels := by
      have hz : ∀ j, raw40656step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40656step1 = (fun i j => raw40656step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40656step1 raw40656step0; decide +kernel
      have hl : raw40656step1Labels = raw40656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40656step0 raw40656step0Labels permutation80 hz
    mixedMoment B raw40656step1 raw40656step1Labels = mixedMoment B raw40656step2 raw40656step2Labels := by
      have hz : ∀ j, raw40656step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40656step2 = (fun i j => raw40656step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40656step2 raw40656step1; decide +kernel
      have hl : raw40656step2Labels = raw40656step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40656step1 raw40656step1Labels permutation14 hz
    mixedMoment B raw40656step2 raw40656step2Labels = mixedMoment B raw40656step3 raw40656step3Labels := by
      have ha : raw40656step3 = (fun i j => raw40656step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40656step3 raw40656step2; decide +kernel
      have hl : raw40656step3Labels = raw40656step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40656step2 raw40656step2Labels permutation4 permutation6
    mixedMoment B raw40656step3 raw40656step3Labels = mixedMoment B raw40656step4 raw40656step4Labels := by
      have ha : raw40656step4 = -raw40656step3 := by apply Matrix.ext; change ∀ i j, raw40656step4 i j = -(raw40656step3 i j); unfold raw40656step4 raw40656step3; decide +kernel
      have hl : raw40656step4Labels = raw40656step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2281 node2281Labels := by rfl

theorem canonical40657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40657 raw40657Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw40657 raw40657Labels = mixedMoment B raw40657step0 raw40657step0Labels := by
      have hz : ∀ j, raw40657 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40657step0 = (fun i j => raw40657 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40657step0 raw40657; decide +kernel
      have hl : raw40657step0Labels = raw40657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40657 raw40657Labels permutation434 hz
    mixedMoment B raw40657step0 raw40657step0Labels = mixedMoment B raw40657step1 raw40657step1Labels := by
      have hz : ∀ j, raw40657step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40657step1 = (fun i j => raw40657step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40657step1 raw40657step0; decide +kernel
      have hl : raw40657step1Labels = raw40657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40657step0 raw40657step0Labels permutation80 hz
    mixedMoment B raw40657step1 raw40657step1Labels = mixedMoment B raw40657step2 raw40657step2Labels := by
      have hz : ∀ j, raw40657step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40657step2 = (fun i j => raw40657step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40657step2 raw40657step1; decide +kernel
      have hl : raw40657step2Labels = raw40657step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40657step1 raw40657step1Labels permutation14 hz
    mixedMoment B raw40657step2 raw40657step2Labels = mixedMoment B raw40657step3 raw40657step3Labels := by
      have ha : raw40657step3 = (fun i j => raw40657step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40657step3 raw40657step2; decide +kernel
      have hl : raw40657step3Labels = raw40657step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40657step2 raw40657step2Labels permutation6 permutation6
    mixedMoment B raw40657step3 raw40657step3Labels = mixedMoment B raw40657step4 raw40657step4Labels := by
      have ha : raw40657step4 = -raw40657step3 := by apply Matrix.ext; change ∀ i j, raw40657step4 i j = -(raw40657step3 i j); unfold raw40657step4 raw40657step3; decide +kernel
      have hl : raw40657step4Labels = raw40657step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3633 node3633Labels := by rfl

theorem canonical40658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40658 raw40658Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw40658 raw40658Labels = mixedMoment B raw40658step0 raw40658step0Labels := by
      have hz : ∀ j, raw40658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40658step0 = (fun i j => raw40658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40658step0 raw40658; decide +kernel
      have hl : raw40658step0Labels = raw40658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40658 raw40658Labels permutation346 hz
    mixedMoment B raw40658step0 raw40658step0Labels = mixedMoment B raw40658step1 raw40658step1Labels := by
      have hz : ∀ j, raw40658step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40658step1 = (fun i j => raw40658step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40658step1 raw40658step0; decide +kernel
      have hl : raw40658step1Labels = raw40658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40658step0 raw40658step0Labels permutation56 hz
    mixedMoment B raw40658step1 raw40658step1Labels = mixedMoment B raw40658step2 raw40658step2Labels := by
      have ha : raw40658step2 = (fun i j => raw40658step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40658step2 raw40658step1; decide +kernel
      have hl : raw40658step2Labels = raw40658step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40658step1 raw40658step1Labels permutation26 permutation6
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical40659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40659 raw40659Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw40659 raw40659Labels = mixedMoment B raw40659step0 raw40659step0Labels := by
      have hz : ∀ j, raw40659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40659step0 = (fun i j => raw40659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40659step0 raw40659; decide +kernel
      have hl : raw40659step0Labels = raw40659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40659 raw40659Labels permutation346 hz
    mixedMoment B raw40659step0 raw40659step0Labels = mixedMoment B raw40659step1 raw40659step1Labels := by
      have hz : ∀ j, raw40659step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40659step1 = (fun i j => raw40659step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40659step1 raw40659step0; decide +kernel
      have hl : raw40659step1Labels = raw40659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40659step0 raw40659step0Labels permutation56 hz
    mixedMoment B raw40659step1 raw40659step1Labels = mixedMoment B raw40659step2 raw40659step2Labels := by
      have ha : raw40659step2 = (fun i j => raw40659step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40659step2 raw40659step1; decide +kernel
      have hl : raw40659step2Labels = raw40659step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40659step1 raw40659step1Labels permutation8 permutation3
    _ = mixedMoment B node3913 node3913Labels := by rfl

theorem canonical40660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40660 raw40660Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw40660 raw40660Labels = mixedMoment B raw40660step0 raw40660step0Labels := by
      have hz : ∀ j, raw40660 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40660step0 = (fun i j => raw40660 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40660step0 raw40660; decide +kernel
      have hl : raw40660step0Labels = raw40660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40660 raw40660Labels permutation346 hz
    mixedMoment B raw40660step0 raw40660step0Labels = mixedMoment B raw40660step1 raw40660step1Labels := by
      have hz : ∀ j, raw40660step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40660step1 = (fun i j => raw40660step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40660step1 raw40660step0; decide +kernel
      have hl : raw40660step1Labels = raw40660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40660step0 raw40660step0Labels permutation56 hz
    mixedMoment B raw40660step1 raw40660step1Labels = mixedMoment B raw40660step2 raw40660step2Labels := by
      have ha : raw40660step2 = (fun i j => raw40660step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40660step2 raw40660step1; decide +kernel
      have hl : raw40660step2Labels = raw40660step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40660step1 raw40660step1Labels permutation18 permutation6
    mixedMoment B raw40660step2 raw40660step2Labels = mixedMoment B raw40660step3 raw40660step3Labels := by
      have ha : raw40660step3 = -raw40660step2 := by apply Matrix.ext; change ∀ i j, raw40660step3 i j = -(raw40660step2 i j); unfold raw40660step3 raw40660step2; decide +kernel
      have hl : raw40660step3Labels = raw40660step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3907 node3907Labels := by rfl

theorem canonical40661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40661 raw40661Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw40661 raw40661Labels = mixedMoment B raw40661step0 raw40661step0Labels := by
      have hz : ∀ j, raw40661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40661step0 = (fun i j => raw40661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40661step0 raw40661; decide +kernel
      have hl : raw40661step0Labels = raw40661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40661 raw40661Labels permutation346 hz
    mixedMoment B raw40661step0 raw40661step0Labels = mixedMoment B raw40661step1 raw40661step1Labels := by
      have hz : ∀ j, raw40661step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40661step1 = (fun i j => raw40661step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40661step1 raw40661step0; decide +kernel
      have hl : raw40661step1Labels = raw40661step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40661step0 raw40661step0Labels permutation56 hz
    mixedMoment B raw40661step1 raw40661step1Labels = mixedMoment B raw40661step2 raw40661step2Labels := by
      have ha : raw40661step2 = (fun i j => raw40661step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40661step2 raw40661step1; decide +kernel
      have hl : raw40661step2Labels = raw40661step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40661step1 raw40661step1Labels permutation15 permutation6
    mixedMoment B raw40661step2 raw40661step2Labels = mixedMoment B raw40661step3 raw40661step3Labels := by
      have ha : raw40661step3 = -raw40661step2 := by apply Matrix.ext; change ∀ i j, raw40661step3 i j = -(raw40661step2 i j); unfold raw40661step3 raw40661step2; decide +kernel
      have hl : raw40661step3Labels = raw40661step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2278 node2278Labels := by rfl

theorem canonical40662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40662 raw40662Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw40662 raw40662Labels = mixedMoment B raw40662step0 raw40662step0Labels := by
      have hz : ∀ j, raw40662 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40662step0 = (fun i j => raw40662 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40662step0 raw40662; decide +kernel
      have hl : raw40662step0Labels = raw40662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40662 raw40662Labels permutation265 hz
    mixedMoment B raw40662step0 raw40662step0Labels = mixedMoment B raw40662step1 raw40662step1Labels := by
      have ha : raw40662step1 = (fun i j => raw40662step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40662step1 raw40662step0; decide +kernel
      have hl : raw40662step1Labels = raw40662step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40662step0 raw40662step0Labels permutation32 permutation3
    _ = mixedMoment B node3910 node3910Labels := by rfl

theorem canonical40663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40663 raw40663Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw40663 raw40663Labels = mixedMoment B raw40663step0 raw40663step0Labels := by
      have hz : ∀ j, raw40663 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40663step0 = (fun i j => raw40663 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40663step0 raw40663; decide +kernel
      have hl : raw40663step0Labels = raw40663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40663 raw40663Labels permutation265 hz
    mixedMoment B raw40663step0 raw40663step0Labels = mixedMoment B raw40663step1 raw40663step1Labels := by
      have ha : raw40663step1 = (fun i j => raw40663step0 (permutation87 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40663step1 raw40663step0; decide +kernel
      have hl : raw40663step1Labels = raw40663step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40663step0 raw40663step0Labels permutation87 permutation6
    mixedMoment B raw40663step1 raw40663step1Labels = mixedMoment B raw40663step2 raw40663step2Labels := by
      have ha : raw40663step2 = -raw40663step1 := by apply Matrix.ext; change ∀ i j, raw40663step2 i j = -(raw40663step1 i j); unfold raw40663step2 raw40663step1; decide +kernel
      have hl : raw40663step2Labels = raw40663step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical40664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40664 raw40664Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw40664 raw40664Labels = mixedMoment B raw40664step0 raw40664step0Labels := by
      have hz : ∀ j, raw40664 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40664step0 = (fun i j => raw40664 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40664step0 raw40664; decide +kernel
      have hl : raw40664step0Labels = raw40664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40664 raw40664Labels permutation520 hz
    mixedMoment B raw40664step0 raw40664step0Labels = mixedMoment B raw40664step1 raw40664step1Labels := by
      have hz : ∀ j, raw40664step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40664step1 = (fun i j => raw40664step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40664step1 raw40664step0; decide +kernel
      have hl : raw40664step1Labels = raw40664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40664step0 raw40664step0Labels permutation104 hz
    mixedMoment B raw40664step1 raw40664step1Labels = mixedMoment B raw40664step2 raw40664step2Labels := by
      have hz : ∀ j, raw40664step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40664step2 = (fun i j => raw40664step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40664step2 raw40664step1; decide +kernel
      have hl : raw40664step2Labels = raw40664step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40664step1 raw40664step1Labels permutation20 hz
    mixedMoment B raw40664step2 raw40664step2Labels = mixedMoment B raw40664step3 raw40664step3Labels := by
      have ha : raw40664step3 = (fun i j => raw40664step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40664step3 raw40664step2; decide +kernel
      have hl : raw40664step3Labels = raw40664step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40664step2 raw40664step2Labels permutation7 permutation3
    mixedMoment B raw40664step3 raw40664step3Labels = mixedMoment B raw40664step4 raw40664step4Labels := by
      have ha : raw40664step4 = -raw40664step3 := by apply Matrix.ext; change ∀ i j, raw40664step4 i j = -(raw40664step3 i j); unfold raw40664step4 raw40664step3; decide +kernel
      have hl : raw40664step4Labels = raw40664step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2293 node2293Labels := by rfl

theorem canonical40665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40665 raw40665Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw40665 raw40665Labels = mixedMoment B raw40665step0 raw40665step0Labels := by
      have hz : ∀ j, raw40665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40665step0 = (fun i j => raw40665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40665step0 raw40665; decide +kernel
      have hl : raw40665step0Labels = raw40665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40665 raw40665Labels permutation434 hz
    mixedMoment B raw40665step0 raw40665step0Labels = mixedMoment B raw40665step1 raw40665step1Labels := by
      have hz : ∀ j, raw40665step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40665step1 = (fun i j => raw40665step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40665step1 raw40665step0; decide +kernel
      have hl : raw40665step1Labels = raw40665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40665step0 raw40665step0Labels permutation80 hz
    mixedMoment B raw40665step1 raw40665step1Labels = mixedMoment B raw40665step2 raw40665step2Labels := by
      have ha : raw40665step2 = (fun i j => raw40665step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40665step2 raw40665step1; decide +kernel
      have hl : raw40665step2Labels = raw40665step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40665step1 raw40665step1Labels permutation31 permutation3
    mixedMoment B raw40665step2 raw40665step2Labels = mixedMoment B raw40665step3 raw40665step3Labels := by
      have ha : raw40665step3 = -raw40665step2 := by apply Matrix.ext; change ∀ i j, raw40665step3 i j = -(raw40665step2 i j); unfold raw40665step3 raw40665step2; decide +kernel
      have hl : raw40665step3Labels = raw40665step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical40666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40666 raw40666Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw40666 raw40666Labels = mixedMoment B raw40666step0 raw40666step0Labels := by
      have hz : ∀ j, raw40666 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40666step0 = (fun i j => raw40666 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40666step0 raw40666; decide +kernel
      have hl : raw40666step0Labels = raw40666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40666 raw40666Labels permutation434 hz
    mixedMoment B raw40666step0 raw40666step0Labels = mixedMoment B raw40666step1 raw40666step1Labels := by
      have hz : ∀ j, raw40666step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40666step1 = (fun i j => raw40666step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40666step1 raw40666step0; decide +kernel
      have hl : raw40666step1Labels = raw40666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40666step0 raw40666step0Labels permutation80 hz
    mixedMoment B raw40666step1 raw40666step1Labels = mixedMoment B raw40666step2 raw40666step2Labels := by
      have ha : raw40666step2 = (fun i j => raw40666step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40666step2 raw40666step1; decide +kernel
      have hl : raw40666step2Labels = raw40666step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40666step1 raw40666step1Labels permutation31 permutation3
    mixedMoment B raw40666step2 raw40666step2Labels = mixedMoment B raw40666step3 raw40666step3Labels := by
      have ha : raw40666step3 = -raw40666step2 := by apply Matrix.ext; change ∀ i j, raw40666step3 i j = -(raw40666step2 i j); unfold raw40666step3 raw40666step2; decide +kernel
      have hl : raw40666step3Labels = raw40666step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3055 node3055Labels := by rfl

theorem canonical40667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40667 raw40667Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw40667 raw40667Labels = mixedMoment B raw40667step0 raw40667step0Labels := by
      have hz : ∀ j, raw40667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40667step0 = (fun i j => raw40667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40667step0 raw40667; decide +kernel
      have hl : raw40667step0Labels = raw40667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40667 raw40667Labels permutation434 hz
    mixedMoment B raw40667step0 raw40667step0Labels = mixedMoment B raw40667step1 raw40667step1Labels := by
      have hz : ∀ j, raw40667step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40667step1 = (fun i j => raw40667step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40667step1 raw40667step0; decide +kernel
      have hl : raw40667step1Labels = raw40667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40667step0 raw40667step0Labels permutation80 hz
    mixedMoment B raw40667step1 raw40667step1Labels = mixedMoment B raw40667step2 raw40667step2Labels := by
      have ha : raw40667step2 = (fun i j => raw40667step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40667step2 raw40667step1; decide +kernel
      have hl : raw40667step2Labels = raw40667step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40667step1 raw40667step1Labels permutation31 permutation3
    mixedMoment B raw40667step2 raw40667step2Labels = mixedMoment B raw40667step3 raw40667step3Labels := by
      have ha : raw40667step3 = -raw40667step2 := by apply Matrix.ext; change ∀ i j, raw40667step3 i j = -(raw40667step2 i j); unfold raw40667step3 raw40667step2; decide +kernel
      have hl : raw40667step3Labels = raw40667step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3817 node3817Labels := by rfl

theorem canonical40668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40668 raw40668Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw40668 raw40668Labels = mixedMoment B raw40668step0 raw40668step0Labels := by
      have hz : ∀ j, raw40668 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40668step0 = (fun i j => raw40668 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40668step0 raw40668; decide +kernel
      have hl : raw40668step0Labels = raw40668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40668 raw40668Labels permutation434 hz
    mixedMoment B raw40668step0 raw40668step0Labels = mixedMoment B raw40668step1 raw40668step1Labels := by
      have hz : ∀ j, raw40668step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40668step1 = (fun i j => raw40668step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40668step1 raw40668step0; decide +kernel
      have hl : raw40668step1Labels = raw40668step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40668step0 raw40668step0Labels permutation80 hz
    mixedMoment B raw40668step1 raw40668step1Labels = mixedMoment B raw40668step2 raw40668step2Labels := by
      have ha : raw40668step2 = (fun i j => raw40668step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40668step2 raw40668step1; decide +kernel
      have hl : raw40668step2Labels = raw40668step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40668step1 raw40668step1Labels permutation8 permutation3
    _ = mixedMoment B node3963 node3963Labels := by rfl

theorem canonical40669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40669 raw40669Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw40669 raw40669Labels = mixedMoment B raw40669step0 raw40669step0Labels := by
      have hz : ∀ j, raw40669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40669step0 = (fun i j => raw40669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40669step0 raw40669; decide +kernel
      have hl : raw40669step0Labels = raw40669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40669 raw40669Labels permutation346 hz
    mixedMoment B raw40669step0 raw40669step0Labels = mixedMoment B raw40669step1 raw40669step1Labels := by
      have ha : raw40669step1 = (fun i j => raw40669step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40669step1 raw40669step0; decide +kernel
      have hl : raw40669step1Labels = raw40669step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40669step0 raw40669step0Labels permutation145 permutation3
    mixedMoment B raw40669step1 raw40669step1Labels = mixedMoment B raw40669step2 raw40669step2Labels := by
      have ha : raw40669step2 = -raw40669step1 := by apply Matrix.ext; change ∀ i j, raw40669step2 i j = -(raw40669step1 i j); unfold raw40669step2 raw40669step1; decide +kernel
      have hl : raw40669step2Labels = raw40669step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3078 node3078Labels := by rfl

theorem canonical40670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40670 raw40670Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw40670 raw40670Labels = mixedMoment B raw40670step0 raw40670step0Labels := by
      have hz : ∀ j, raw40670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40670step0 = (fun i j => raw40670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40670step0 raw40670; decide +kernel
      have hl : raw40670step0Labels = raw40670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40670 raw40670Labels permutation346 hz
    mixedMoment B raw40670step0 raw40670step0Labels = mixedMoment B raw40670step1 raw40670step1Labels := by
      have ha : raw40670step1 = (fun i j => raw40670step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40670step1 raw40670step0; decide +kernel
      have hl : raw40670step1Labels = raw40670step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40670step0 raw40670step0Labels permutation151 permutation3
    mixedMoment B raw40670step1 raw40670step1Labels = mixedMoment B raw40670step2 raw40670step2Labels := by
      have ha : raw40670step2 = -raw40670step1 := by apply Matrix.ext; change ∀ i j, raw40670step2 i j = -(raw40670step1 i j); unfold raw40670step2 raw40670step1; decide +kernel
      have hl : raw40670step2Labels = raw40670step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical40671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40671 raw40671Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw40671 raw40671Labels = mixedMoment B raw40671step0 raw40671step0Labels := by
      have hz : ∀ j, raw40671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40671step0 = (fun i j => raw40671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40671step0 raw40671; decide +kernel
      have hl : raw40671step0Labels = raw40671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40671 raw40671Labels permutation346 hz
    mixedMoment B raw40671step0 raw40671step0Labels = mixedMoment B raw40671step1 raw40671step1Labels := by
      have ha : raw40671step1 = (fun i j => raw40671step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40671step1 raw40671step0; decide +kernel
      have hl : raw40671step1Labels = raw40671step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40671step0 raw40671step0Labels permutation32 permutation3
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical40672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40672 raw40672Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw40672 raw40672Labels = mixedMoment B raw40672step0 raw40672step0Labels := by
      have hz : ∀ j, raw40672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40672step0 = (fun i j => raw40672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40672step0 raw40672; decide +kernel
      have hl : raw40672step0Labels = raw40672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40672 raw40672Labels permutation346 hz
    mixedMoment B raw40672step0 raw40672step0Labels = mixedMoment B raw40672step1 raw40672step1Labels := by
      have ha : raw40672step1 = (fun i j => raw40672step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40672step1 raw40672step0; decide +kernel
      have hl : raw40672step1Labels = raw40672step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40672step0 raw40672step0Labels permutation32 permutation3
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical40673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40673 raw40673Labels = mixedMoment B node3962 node3962Labels := by
  calc
    mixedMoment B raw40673 raw40673Labels = mixedMoment B raw40673step0 raw40673step0Labels := by
      have hz : ∀ j, raw40673 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40673step0 = (fun i j => raw40673 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40673step0 raw40673; decide +kernel
      have hl : raw40673step0Labels = raw40673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40673 raw40673Labels permutation346 hz
    mixedMoment B raw40673step0 raw40673step0Labels = mixedMoment B raw40673step1 raw40673step1Labels := by
      have ha : raw40673step1 = (fun i j => raw40673step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40673step1 raw40673step0; decide +kernel
      have hl : raw40673step1Labels = raw40673step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40673step0 raw40673step0Labels permutation32 permutation3
    _ = mixedMoment B node3962 node3962Labels := by rfl

theorem canonical40674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40674 raw40674Labels = mixedMoment B node3953 node3953Labels := by
  calc
    mixedMoment B raw40674 raw40674Labels = mixedMoment B raw40674step0 raw40674step0Labels := by
      have ha : raw40674step0 = (fun i j => raw40674 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40674step0 raw40674; decide +kernel
      have hl : raw40674step0Labels = raw40674Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40674 raw40674Labels permutation152 permutation3
    _ = mixedMoment B node3953 node3953Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5922 raw5922Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw5922 raw5922Labels = mixedMoment B raw5922step0 raw5922step0Labels := by
      have hz : ∀ j, raw5922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5922step0 = (fun i j => raw5922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5922step0 raw5922; decide +kernel
      have hl : raw5922step0Labels = raw5922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5922 raw5922Labels permutation434 hz
    mixedMoment B raw5922step0 raw5922step0Labels = mixedMoment B raw5922step1 raw5922step1Labels := by
      have hz : ∀ j, raw5922step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5922step1 = (fun i j => raw5922step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5922step1 raw5922step0; decide +kernel
      have hl : raw5922step1Labels = raw5922step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5922step0 raw5922step0Labels permutation80 hz
    mixedMoment B raw5922step1 raw5922step1Labels = mixedMoment B raw5922step2 raw5922step2Labels := by
      have ha : raw5922step2 = (fun i j => raw5922step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5922step2 raw5922step1; decide +kernel
      have hl : raw5922step2Labels = raw5922step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5922step1 raw5922step1Labels permutation20 permutation6
    mixedMoment B raw5922step2 raw5922step2Labels = mixedMoment B raw5922step3 raw5922step3Labels := by
      have ha : raw5922step3 = -raw5922step2 := by apply Matrix.ext; change ∀ i j, raw5922step3 i j = -(raw5922step2 i j); unfold raw5922step3 raw5922step2; decide +kernel
      have hl : raw5922step3Labels = raw5922step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3584 node3584Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6278 raw6278Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw6278 raw6278Labels = mixedMoment B raw6278step0 raw6278step0Labels := by
      have hz : ∀ j, raw6278 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6278step0 = (fun i j => raw6278 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6278step0 raw6278; decide +kernel
      have hl : raw6278step0Labels = raw6278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6278 raw6278Labels permutation346 hz
    mixedMoment B raw6278step0 raw6278step0Labels = mixedMoment B raw6278step1 raw6278step1Labels := by
      have ha : raw6278step1 = (fun i j => raw6278step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6278step1 raw6278step0; decide +kernel
      have hl : raw6278step1Labels = raw6278step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6278step0 raw6278step0Labels permutation32 permutation3
    _ = mixedMoment B node3959 node3959Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6608 raw6608Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw6608 raw6608Labels = mixedMoment B raw6608step0 raw6608step0Labels := by
      have hz : ∀ j, raw6608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6608step0 = (fun i j => raw6608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6608step0 raw6608; decide +kernel
      have hl : raw6608step0Labels = raw6608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6608 raw6608Labels permutation346 hz
    mixedMoment B raw6608step0 raw6608step0Labels = mixedMoment B raw6608step1 raw6608step1Labels := by
      have ha : raw6608step1 = (fun i j => raw6608step0 (permutation85 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6608step1 raw6608step0; decide +kernel
      have hl : raw6608step1Labels = raw6608step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6608step0 raw6608step0Labels permutation85 permutation6
    mixedMoment B raw6608step1 raw6608step1Labels = mixedMoment B raw6608step2 raw6608step2Labels := by
      have ha : raw6608step2 = -raw6608step1 := by apply Matrix.ext; change ∀ i j, raw6608step2 i j = -(raw6608step1 i j); unfold raw6608step2 raw6608step1; decide +kernel
      have hl : raw6608step2Labels = raw6608step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3884 node3884Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6961 raw6961Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw6961 raw6961Labels = mixedMoment B raw6961step0 raw6961step0Labels := by
      have hz : ∀ j, raw6961 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6961step0 = (fun i j => raw6961 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6961step0 raw6961; decide +kernel
      have hl : raw6961step0Labels = raw6961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6961 raw6961Labels permutation346 hz
    mixedMoment B raw6961step0 raw6961step0Labels = mixedMoment B raw6961step1 raw6961step1Labels := by
      have ha : raw6961step1 = (fun i j => raw6961step0 (permutation82 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6961step1 raw6961step0; decide +kernel
      have hl : raw6961step1Labels = raw6961step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6961step0 raw6961step0Labels permutation82 permutation6
    mixedMoment B raw6961step1 raw6961step1Labels = mixedMoment B raw6961step2 raw6961step2Labels := by
      have ha : raw6961step2 = -raw6961step1 := by apply Matrix.ext; change ∀ i j, raw6961step2 i j = -(raw6961step1 i j); unfold raw6961step2 raw6961step1; decide +kernel
      have hl : raw6961step2Labels = raw6961step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3877 node3877Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7439 raw7439Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw7439 raw7439Labels = mixedMoment B raw7439step0 raw7439step0Labels := by
      have ha : raw7439step0 = (fun i j => raw7439 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7439step0 raw7439; decide +kernel
      have hl : raw7439step0Labels = raw7439Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7439 raw7439Labels permutation152 permutation3
    _ = mixedMoment B node3954 node3954Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1216 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1216) =
      Integer.Sparse.eval keyMomentRow1216 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1216).leftCharge (GramAssembly.key 1216).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3908) := by
    have ha : gramCharges (GramAssembly.key 1216).leftCharge (GramAssembly.key 1216).rightCharge = raw40648 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40648Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40648 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1216).leftCharge (GramAssembly.key 1216).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1216, Integer.Sparse.eval]

theorem keyMoment1217 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1217) =
      Integer.Sparse.eval keyMomentRow1217 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1217).leftCharge (GramAssembly.key 1217).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3814) := by
    have ha : gramCharges (GramAssembly.key 1217).leftCharge (GramAssembly.key 1217).rightCharge = raw40649 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40649Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40649 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1217).leftCharge (GramAssembly.key 1217).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1217, Integer.Sparse.eval]

theorem keyMoment1218 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1218) =
      Integer.Sparse.eval keyMomentRow1218 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1218).leftCharge (GramAssembly.key 1218).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3903) := by
    have ha : gramCharges (GramAssembly.key 1218).leftCharge (GramAssembly.key 1218).rightCharge = raw40650 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40650Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40650 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1218).leftCharge (GramAssembly.key 1218).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1218, Integer.Sparse.eval]

theorem keyMoment1219 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1219) =
      Integer.Sparse.eval keyMomentRow1219 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1219).leftCharge (GramAssembly.key 1219).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3904) := by
    have ha : gramCharges (GramAssembly.key 1219).leftCharge (GramAssembly.key 1219).rightCharge = raw40651 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40651Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40651 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1219).leftCharge (GramAssembly.key 1219).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1219, Integer.Sparse.eval]

theorem keyMoment1220 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1220) =
      Integer.Sparse.eval keyMomentRow1220 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1220).leftCharge (GramAssembly.key 1220).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3906) := by
    have ha : gramCharges (GramAssembly.key 1220).leftCharge (GramAssembly.key 1220).rightCharge = raw40652 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40652Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40652 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1220).leftCharge (GramAssembly.key 1220).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1220, Integer.Sparse.eval]

theorem keyMoment1221 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1221) =
      Integer.Sparse.eval keyMomentRow1221 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1221).leftCharge (GramAssembly.key 1221).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2277) := by
    have ha : gramCharges (GramAssembly.key 1221).leftCharge (GramAssembly.key 1221).rightCharge = raw40653 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40653Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40653 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1221).leftCharge (GramAssembly.key 1221).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1221, Integer.Sparse.eval]

theorem keyMoment1222 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1222) =
      Integer.Sparse.eval keyMomentRow1222 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1222).leftCharge (GramAssembly.key 1222).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3901) := by
    have ha : gramCharges (GramAssembly.key 1222).leftCharge (GramAssembly.key 1222).rightCharge = raw40654 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40654Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40654 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1222).leftCharge (GramAssembly.key 1222).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1222, Integer.Sparse.eval]

theorem keyMoment1223 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1223) =
      Integer.Sparse.eval keyMomentRow1223 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1223).leftCharge (GramAssembly.key 1223).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3812) := by
    have ha : gramCharges (GramAssembly.key 1223).leftCharge (GramAssembly.key 1223).rightCharge = raw40655 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40655Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40655 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1223).leftCharge (GramAssembly.key 1223).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1223, Integer.Sparse.eval]

theorem keyMoment1224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1224) =
      Integer.Sparse.eval keyMomentRow1224 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1224).leftCharge (GramAssembly.key 1224).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2281) := by
    have ha : gramCharges (GramAssembly.key 1224).leftCharge (GramAssembly.key 1224).rightCharge = raw40656 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40656Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40656 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1224).leftCharge (GramAssembly.key 1224).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1224, Integer.Sparse.eval]

theorem keyMoment1225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1225) =
      Integer.Sparse.eval keyMomentRow1225 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1225).leftCharge (GramAssembly.key 1225).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3633) := by
    have ha : gramCharges (GramAssembly.key 1225).leftCharge (GramAssembly.key 1225).rightCharge = raw40657 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40657Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40657 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1225).leftCharge (GramAssembly.key 1225).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1225, Integer.Sparse.eval]

theorem keyMoment1226 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1226) =
      Integer.Sparse.eval keyMomentRow1226 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1226).leftCharge (GramAssembly.key 1226).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3054) := by
    have ha : gramCharges (GramAssembly.key 1226).leftCharge (GramAssembly.key 1226).rightCharge = raw40658 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40658Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40658 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1226).leftCharge (GramAssembly.key 1226).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1226, Integer.Sparse.eval]

theorem keyMoment1227 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1227) =
      Integer.Sparse.eval keyMomentRow1227 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1227).leftCharge (GramAssembly.key 1227).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3913) := by
    have ha : gramCharges (GramAssembly.key 1227).leftCharge (GramAssembly.key 1227).rightCharge = raw40659 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40659Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40659 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1227).leftCharge (GramAssembly.key 1227).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1227, Integer.Sparse.eval]

theorem keyMoment1228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1228) =
      Integer.Sparse.eval keyMomentRow1228 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1228).leftCharge (GramAssembly.key 1228).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3907) := by
    have ha : gramCharges (GramAssembly.key 1228).leftCharge (GramAssembly.key 1228).rightCharge = raw40660 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40660Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40660 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1228).leftCharge (GramAssembly.key 1228).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1228, Integer.Sparse.eval]

theorem keyMoment1229 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1229) =
      Integer.Sparse.eval keyMomentRow1229 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1229).leftCharge (GramAssembly.key 1229).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2278) := by
    have ha : gramCharges (GramAssembly.key 1229).leftCharge (GramAssembly.key 1229).rightCharge = raw40661 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40661Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40661 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1229).leftCharge (GramAssembly.key 1229).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1229, Integer.Sparse.eval]

theorem keyMoment1230 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1230) =
      Integer.Sparse.eval keyMomentRow1230 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1230).leftCharge (GramAssembly.key 1230).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3910) := by
    have ha : gramCharges (GramAssembly.key 1230).leftCharge (GramAssembly.key 1230).rightCharge = raw40662 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40662Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40662 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1230).leftCharge (GramAssembly.key 1230).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1230, Integer.Sparse.eval]

theorem keyMoment1231 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1231) =
      Integer.Sparse.eval keyMomentRow1231 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1231).leftCharge (GramAssembly.key 1231).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3813) := by
    have ha : gramCharges (GramAssembly.key 1231).leftCharge (GramAssembly.key 1231).rightCharge = raw40663 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40663Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40663 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1231).leftCharge (GramAssembly.key 1231).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1231, Integer.Sparse.eval]

theorem keyMoment1232 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1232) =
      Integer.Sparse.eval keyMomentRow1232 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1232).leftCharge (GramAssembly.key 1232).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2293) := by
    have ha : gramCharges (GramAssembly.key 1232).leftCharge (GramAssembly.key 1232).rightCharge = raw40664 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40664Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40664 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1232).leftCharge (GramAssembly.key 1232).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1232, Integer.Sparse.eval]

theorem keyMoment1233 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1233) =
      Integer.Sparse.eval keyMomentRow1233 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1233).leftCharge (GramAssembly.key 1233).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2743) := by
    have ha : gramCharges (GramAssembly.key 1233).leftCharge (GramAssembly.key 1233).rightCharge = raw40665 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40665Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40665 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1233).leftCharge (GramAssembly.key 1233).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1233, Integer.Sparse.eval]

theorem keyMoment1234 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1234) =
      Integer.Sparse.eval keyMomentRow1234 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1234).leftCharge (GramAssembly.key 1234).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3055) := by
    have ha : gramCharges (GramAssembly.key 1234).leftCharge (GramAssembly.key 1234).rightCharge = raw40666 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40666Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40666 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1234).leftCharge (GramAssembly.key 1234).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1234, Integer.Sparse.eval]

theorem keyMoment1235 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1235) =
      Integer.Sparse.eval keyMomentRow1235 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1235).leftCharge (GramAssembly.key 1235).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3817) := by
    have ha : gramCharges (GramAssembly.key 1235).leftCharge (GramAssembly.key 1235).rightCharge = raw40667 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40667Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40667 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1235).leftCharge (GramAssembly.key 1235).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1235, Integer.Sparse.eval]

theorem keyMoment1236 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1236) =
      Integer.Sparse.eval keyMomentRow1236 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1236).leftCharge (GramAssembly.key 1236).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3963) := by
    have ha : gramCharges (GramAssembly.key 1236).leftCharge (GramAssembly.key 1236).rightCharge = raw40668 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40668Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40668 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1236).leftCharge (GramAssembly.key 1236).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1236, Integer.Sparse.eval]

theorem keyMoment1237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1237) =
      Integer.Sparse.eval keyMomentRow1237 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1237).leftCharge (GramAssembly.key 1237).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3584) := by
    have ha : gramCharges (GramAssembly.key 1237).leftCharge (GramAssembly.key 1237).rightCharge = raw5922 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw5922Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical5922 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1237).leftCharge (GramAssembly.key 1237).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1237, Integer.Sparse.eval]

theorem keyMoment1238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1238) =
      Integer.Sparse.eval keyMomentRow1238 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1238).leftCharge (GramAssembly.key 1238).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3078) := by
    have ha : gramCharges (GramAssembly.key 1238).leftCharge (GramAssembly.key 1238).rightCharge = raw40669 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40669Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40669 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1238).leftCharge (GramAssembly.key 1238).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1238, Integer.Sparse.eval]

theorem keyMoment1239 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1239) =
      Integer.Sparse.eval keyMomentRow1239 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1239).leftCharge (GramAssembly.key 1239).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3845) := by
    have ha : gramCharges (GramAssembly.key 1239).leftCharge (GramAssembly.key 1239).rightCharge = raw40670 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40670Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40670 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1239).leftCharge (GramAssembly.key 1239).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1239, Integer.Sparse.eval]

theorem keyMoment1240 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1240) =
      Integer.Sparse.eval keyMomentRow1240 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1240).leftCharge (GramAssembly.key 1240).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3958) := by
    have ha : gramCharges (GramAssembly.key 1240).leftCharge (GramAssembly.key 1240).rightCharge = raw40671 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40671Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40671 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1240).leftCharge (GramAssembly.key 1240).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1240, Integer.Sparse.eval]

theorem keyMoment1241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1241) =
      Integer.Sparse.eval keyMomentRow1241 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1241).leftCharge (GramAssembly.key 1241).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3959) := by
    have ha : gramCharges (GramAssembly.key 1241).leftCharge (GramAssembly.key 1241).rightCharge = raw6278 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw6278Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical6278 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1241).leftCharge (GramAssembly.key 1241).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1241, Integer.Sparse.eval]

theorem keyMoment1242 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1242) =
      Integer.Sparse.eval keyMomentRow1242 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1242).leftCharge (GramAssembly.key 1242).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3884) := by
    have ha : gramCharges (GramAssembly.key 1242).leftCharge (GramAssembly.key 1242).rightCharge = raw6608 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw6608Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical6608 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1242).leftCharge (GramAssembly.key 1242).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1242, Integer.Sparse.eval]

theorem keyMoment1243 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1243) =
      Integer.Sparse.eval keyMomentRow1243 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1243).leftCharge (GramAssembly.key 1243).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3877) := by
    have ha : gramCharges (GramAssembly.key 1243).leftCharge (GramAssembly.key 1243).rightCharge = raw6961 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw6961Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical6961 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1243).leftCharge (GramAssembly.key 1243).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1243, Integer.Sparse.eval]

theorem keyMoment1244 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1244) =
      Integer.Sparse.eval keyMomentRow1244 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1244).leftCharge (GramAssembly.key 1244).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3961) := by
    have ha : gramCharges (GramAssembly.key 1244).leftCharge (GramAssembly.key 1244).rightCharge = raw40672 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40672Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40672 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1244).leftCharge (GramAssembly.key 1244).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1244, Integer.Sparse.eval]

theorem keyMoment1245 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1245) =
      Integer.Sparse.eval keyMomentRow1245 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1245).leftCharge (GramAssembly.key 1245).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3962) := by
    have ha : gramCharges (GramAssembly.key 1245).leftCharge (GramAssembly.key 1245).rightCharge = raw40673 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40673Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40673 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1245).leftCharge (GramAssembly.key 1245).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1245, Integer.Sparse.eval]

theorem keyMoment1246 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1246) =
      Integer.Sparse.eval keyMomentRow1246 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1246).leftCharge (GramAssembly.key 1246).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3953) := by
    have ha : gramCharges (GramAssembly.key 1246).leftCharge (GramAssembly.key 1246).rightCharge = raw40674 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40674Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40674 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1246).leftCharge (GramAssembly.key 1246).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1246, Integer.Sparse.eval]

theorem keyMoment1247 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1247) =
      Integer.Sparse.eval keyMomentRow1247 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1247).leftCharge (GramAssembly.key 1247).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3954) := by
    have ha : gramCharges (GramAssembly.key 1247).leftCharge (GramAssembly.key 1247).rightCharge = raw7439 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw7439Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical7439 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1247).leftCharge (GramAssembly.key 1247).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1247, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1216 : keyMomentRows (1216 : Fin 2886) =
    keyMomentRow1216 := by decide +kernel

theorem keyMomentRowsAt1217 : keyMomentRows (1217 : Fin 2886) =
    keyMomentRow1217 := by decide +kernel

theorem keyMomentRowsAt1218 : keyMomentRows (1218 : Fin 2886) =
    keyMomentRow1218 := by decide +kernel

theorem keyMomentRowsAt1219 : keyMomentRows (1219 : Fin 2886) =
    keyMomentRow1219 := by decide +kernel

theorem keyMomentRowsAt1220 : keyMomentRows (1220 : Fin 2886) =
    keyMomentRow1220 := by decide +kernel

theorem keyMomentRowsAt1221 : keyMomentRows (1221 : Fin 2886) =
    keyMomentRow1221 := by decide +kernel

theorem keyMomentRowsAt1222 : keyMomentRows (1222 : Fin 2886) =
    keyMomentRow1222 := by decide +kernel

theorem keyMomentRowsAt1223 : keyMomentRows (1223 : Fin 2886) =
    keyMomentRow1223 := by decide +kernel

theorem keyMomentRowsAt1224 : keyMomentRows (1224 : Fin 2886) =
    keyMomentRow1224 := by decide +kernel

theorem keyMomentRowsAt1225 : keyMomentRows (1225 : Fin 2886) =
    keyMomentRow1225 := by decide +kernel

theorem keyMomentRowsAt1226 : keyMomentRows (1226 : Fin 2886) =
    keyMomentRow1226 := by decide +kernel

theorem keyMomentRowsAt1227 : keyMomentRows (1227 : Fin 2886) =
    keyMomentRow1227 := by decide +kernel

theorem keyMomentRowsAt1228 : keyMomentRows (1228 : Fin 2886) =
    keyMomentRow1228 := by decide +kernel

theorem keyMomentRowsAt1229 : keyMomentRows (1229 : Fin 2886) =
    keyMomentRow1229 := by decide +kernel

theorem keyMomentRowsAt1230 : keyMomentRows (1230 : Fin 2886) =
    keyMomentRow1230 := by decide +kernel

theorem keyMomentRowsAt1231 : keyMomentRows (1231 : Fin 2886) =
    keyMomentRow1231 := by decide +kernel

theorem keyMomentRowsAt1232 : keyMomentRows (1232 : Fin 2886) =
    keyMomentRow1232 := by decide +kernel

theorem keyMomentRowsAt1233 : keyMomentRows (1233 : Fin 2886) =
    keyMomentRow1233 := by decide +kernel

theorem keyMomentRowsAt1234 : keyMomentRows (1234 : Fin 2886) =
    keyMomentRow1234 := by decide +kernel

theorem keyMomentRowsAt1235 : keyMomentRows (1235 : Fin 2886) =
    keyMomentRow1235 := by decide +kernel

theorem keyMomentRowsAt1236 : keyMomentRows (1236 : Fin 2886) =
    keyMomentRow1236 := by decide +kernel

theorem keyMomentRowsAt1237 : keyMomentRows (1237 : Fin 2886) =
    keyMomentRow1237 := by decide +kernel

theorem keyMomentRowsAt1238 : keyMomentRows (1238 : Fin 2886) =
    keyMomentRow1238 := by decide +kernel

theorem keyMomentRowsAt1239 : keyMomentRows (1239 : Fin 2886) =
    keyMomentRow1239 := by decide +kernel

theorem keyMomentRowsAt1240 : keyMomentRows (1240 : Fin 2886) =
    keyMomentRow1240 := by decide +kernel

theorem keyMomentRowsAt1241 : keyMomentRows (1241 : Fin 2886) =
    keyMomentRow1241 := by decide +kernel

theorem keyMomentRowsAt1242 : keyMomentRows (1242 : Fin 2886) =
    keyMomentRow1242 := by decide +kernel

theorem keyMomentRowsAt1243 : keyMomentRows (1243 : Fin 2886) =
    keyMomentRow1243 := by decide +kernel

theorem keyMomentRowsAt1244 : keyMomentRows (1244 : Fin 2886) =
    keyMomentRow1244 := by decide +kernel

theorem keyMomentRowsAt1245 : keyMomentRows (1245 : Fin 2886) =
    keyMomentRow1245 := by decide +kernel

theorem keyMomentRowsAt1246 : keyMomentRows (1246 : Fin 2886) =
    keyMomentRow1246 := by decide +kernel

theorem keyMomentRowsAt1247 : keyMomentRows (1247 : Fin 2886) =
    keyMomentRow1247 := by decide +kernel

theorem keyMomentChunkSound38_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 38) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1216 ∨ k.val = 1217 ∨ k.val = 1218 ∨ k.val = 1219 ∨ k.val = 1220 ∨ k.val = 1221 ∨ k.val = 1222 ∨ k.val = 1223 ∨ k.val = 1224 ∨ k.val = 1225 ∨ k.val = 1226 ∨ k.val = 1227 ∨ k.val = 1228 ∨ k.val = 1229 ∨ k.val = 1230 ∨ k.val = 1231 ∨ k.val = 1232 ∨ k.val = 1233 ∨ k.val = 1234 ∨ k.val = 1235 ∨ k.val = 1236 ∨ k.val = 1237 ∨ k.val = 1238 ∨ k.val = 1239 ∨ k.val = 1240 ∨ k.val = 1241 ∨ k.val = 1242 ∨ k.val = 1243 ∨ k.val = 1244 ∨ k.val = 1245 ∨ k.val = 1246 ∨ k.val = 1247 := by omega
  rcases heq with h1216 | h1217 | h1218 | h1219 | h1220 | h1221 | h1222 | h1223 | h1224 | h1225 | h1226 | h1227 | h1228 | h1229 | h1230 | h1231 | h1232 | h1233 | h1234 | h1235 | h1236 | h1237 | h1238 | h1239 | h1240 | h1241 | h1242 | h1243 | h1244 | h1245 | h1246 | h1247
  · have he : k = (1216 : Fin 2886) := Fin.ext h1216
    subst k
    rw [keyMomentRowsAt1216]
    exact keyMoment1216 B hB
  · have he : k = (1217 : Fin 2886) := Fin.ext h1217
    subst k
    rw [keyMomentRowsAt1217]
    exact keyMoment1217 B hB
  · have he : k = (1218 : Fin 2886) := Fin.ext h1218
    subst k
    rw [keyMomentRowsAt1218]
    exact keyMoment1218 B hB
  · have he : k = (1219 : Fin 2886) := Fin.ext h1219
    subst k
    rw [keyMomentRowsAt1219]
    exact keyMoment1219 B hB
  · have he : k = (1220 : Fin 2886) := Fin.ext h1220
    subst k
    rw [keyMomentRowsAt1220]
    exact keyMoment1220 B hB
  · have he : k = (1221 : Fin 2886) := Fin.ext h1221
    subst k
    rw [keyMomentRowsAt1221]
    exact keyMoment1221 B hB
  · have he : k = (1222 : Fin 2886) := Fin.ext h1222
    subst k
    rw [keyMomentRowsAt1222]
    exact keyMoment1222 B hB
  · have he : k = (1223 : Fin 2886) := Fin.ext h1223
    subst k
    rw [keyMomentRowsAt1223]
    exact keyMoment1223 B hB
  · have he : k = (1224 : Fin 2886) := Fin.ext h1224
    subst k
    rw [keyMomentRowsAt1224]
    exact keyMoment1224 B hB
  · have he : k = (1225 : Fin 2886) := Fin.ext h1225
    subst k
    rw [keyMomentRowsAt1225]
    exact keyMoment1225 B hB
  · have he : k = (1226 : Fin 2886) := Fin.ext h1226
    subst k
    rw [keyMomentRowsAt1226]
    exact keyMoment1226 B hB
  · have he : k = (1227 : Fin 2886) := Fin.ext h1227
    subst k
    rw [keyMomentRowsAt1227]
    exact keyMoment1227 B hB
  · have he : k = (1228 : Fin 2886) := Fin.ext h1228
    subst k
    rw [keyMomentRowsAt1228]
    exact keyMoment1228 B hB
  · have he : k = (1229 : Fin 2886) := Fin.ext h1229
    subst k
    rw [keyMomentRowsAt1229]
    exact keyMoment1229 B hB
  · have he : k = (1230 : Fin 2886) := Fin.ext h1230
    subst k
    rw [keyMomentRowsAt1230]
    exact keyMoment1230 B hB
  · have he : k = (1231 : Fin 2886) := Fin.ext h1231
    subst k
    rw [keyMomentRowsAt1231]
    exact keyMoment1231 B hB
  · have he : k = (1232 : Fin 2886) := Fin.ext h1232
    subst k
    rw [keyMomentRowsAt1232]
    exact keyMoment1232 B hB
  · have he : k = (1233 : Fin 2886) := Fin.ext h1233
    subst k
    rw [keyMomentRowsAt1233]
    exact keyMoment1233 B hB
  · have he : k = (1234 : Fin 2886) := Fin.ext h1234
    subst k
    rw [keyMomentRowsAt1234]
    exact keyMoment1234 B hB
  · have he : k = (1235 : Fin 2886) := Fin.ext h1235
    subst k
    rw [keyMomentRowsAt1235]
    exact keyMoment1235 B hB
  · have he : k = (1236 : Fin 2886) := Fin.ext h1236
    subst k
    rw [keyMomentRowsAt1236]
    exact keyMoment1236 B hB
  · have he : k = (1237 : Fin 2886) := Fin.ext h1237
    subst k
    rw [keyMomentRowsAt1237]
    exact keyMoment1237 B hB
  · have he : k = (1238 : Fin 2886) := Fin.ext h1238
    subst k
    rw [keyMomentRowsAt1238]
    exact keyMoment1238 B hB
  · have he : k = (1239 : Fin 2886) := Fin.ext h1239
    subst k
    rw [keyMomentRowsAt1239]
    exact keyMoment1239 B hB
  · have he : k = (1240 : Fin 2886) := Fin.ext h1240
    subst k
    rw [keyMomentRowsAt1240]
    exact keyMoment1240 B hB
  · have he : k = (1241 : Fin 2886) := Fin.ext h1241
    subst k
    rw [keyMomentRowsAt1241]
    exact keyMoment1241 B hB
  · have he : k = (1242 : Fin 2886) := Fin.ext h1242
    subst k
    rw [keyMomentRowsAt1242]
    exact keyMoment1242 B hB
  · have he : k = (1243 : Fin 2886) := Fin.ext h1243
    subst k
    rw [keyMomentRowsAt1243]
    exact keyMoment1243 B hB
  · have he : k = (1244 : Fin 2886) := Fin.ext h1244
    subst k
    rw [keyMomentRowsAt1244]
    exact keyMoment1244 B hB
  · have he : k = (1245 : Fin 2886) := Fin.ext h1245
    subst k
    rw [keyMomentRowsAt1245]
    exact keyMoment1245 B hB
  · have he : k = (1246 : Fin 2886) := Fin.ext h1246
    subst k
    rw [keyMomentRowsAt1246]
    exact keyMoment1246 B hB
  · have he : k = (1247 : Fin 2886) := Fin.ext h1247
    subst k
    rw [keyMomentRowsAt1247]
    exact keyMoment1247 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound38_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound38_e_oai
