-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound49_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:12:22.395356+00:00
-- url     : https://prove2.me/submissions/a3861aa6-895b-4ff1-92d8-18359dae99a3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E087
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30961 raw30961Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw30961 raw30961Labels = mixedMoment B raw30961step0 raw30961step0Labels := by
      have hz : ∀ j, raw30961 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30961step0 = (fun i j => raw30961 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30961step0 raw30961; decide +kernel
      have hl : raw30961step0Labels = raw30961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30961 raw30961Labels permutation434 hz
    mixedMoment B raw30961step0 raw30961step0Labels = mixedMoment B raw30961step1 raw30961step1Labels := by
      have hz : ∀ j, raw30961step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30961step1 = (fun i j => raw30961step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30961step1 raw30961step0; decide +kernel
      have hl : raw30961step1Labels = raw30961step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30961step0 raw30961step0Labels permutation80 hz
    mixedMoment B raw30961step1 raw30961step1Labels = mixedMoment B raw30961step2 raw30961step2Labels := by
      have ha : raw30961step2 = (fun i j => raw30961step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30961step2 raw30961step1; decide +kernel
      have hl : raw30961step2Labels = raw30961step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30961step1 raw30961step1Labels permutation12 permutation6
    mixedMoment B raw30961step2 raw30961step2Labels = mixedMoment B raw30961step3 raw30961step3Labels := by
      have ha : raw30961step3 = -raw30961step2 := by apply Matrix.ext; change ∀ i j, raw30961step3 i j = -(raw30961step2 i j); unfold raw30961step3 raw30961step2; decide +kernel
      have hl : raw30961step3Labels = raw30961step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3055 node3055Labels := by rfl

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

theorem canonical40986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40986 raw40986Labels = mixedMoment B node618 node618Labels := by
  calc
    mixedMoment B raw40986 raw40986Labels = mixedMoment B raw40986step0 raw40986step0Labels := by
      have hz : ∀ j, raw40986 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40986step0 = (fun i j => raw40986 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40986step0 raw40986; decide +kernel
      have hl : raw40986step0Labels = raw40986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40986 raw40986Labels permutation434 hz
    mixedMoment B raw40986step0 raw40986step0Labels = mixedMoment B raw40986step1 raw40986step1Labels := by
      have hz : ∀ j, raw40986step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40986step1 = (fun i j => raw40986step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40986step1 raw40986step0; decide +kernel
      have hl : raw40986step1Labels = raw40986step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40986step0 raw40986step0Labels permutation80 hz
    mixedMoment B raw40986step1 raw40986step1Labels = mixedMoment B raw40986step2 raw40986step2Labels := by
      have hz : ∀ j, raw40986step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40986step2 = (fun i j => raw40986step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40986step2 raw40986step1; decide +kernel
      have hl : raw40986step2Labels = raw40986step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40986step1 raw40986step1Labels permutation14 hz
    mixedMoment B raw40986step2 raw40986step2Labels = mixedMoment B raw40986step3 raw40986step3Labels := by
      have ha : raw40986step3 = (fun i j => raw40986step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40986step3 raw40986step2; decide +kernel
      have hl : raw40986step3Labels = raw40986step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40986step2 raw40986step2Labels permutation6 permutation6
    _ = mixedMoment B node618 node618Labels := by rfl

theorem canonical40987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40987 raw40987Labels = mixedMoment B node613 node613Labels := by
  calc
    mixedMoment B raw40987 raw40987Labels = mixedMoment B raw40987step0 raw40987step0Labels := by
      have hz : ∀ j, raw40987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40987step0 = (fun i j => raw40987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40987step0 raw40987; decide +kernel
      have hl : raw40987step0Labels = raw40987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40987 raw40987Labels permutation346 hz
    mixedMoment B raw40987step0 raw40987step0Labels = mixedMoment B raw40987step1 raw40987step1Labels := by
      have hz : ∀ j, raw40987step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40987step1 = (fun i j => raw40987step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40987step1 raw40987step0; decide +kernel
      have hl : raw40987step1Labels = raw40987step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40987step0 raw40987step0Labels permutation56 hz
    mixedMoment B raw40987step1 raw40987step1Labels = mixedMoment B raw40987step2 raw40987step2Labels := by
      have ha : raw40987step2 = (fun i j => raw40987step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40987step2 raw40987step1; decide +kernel
      have hl : raw40987step2Labels = raw40987step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40987step1 raw40987step1Labels permutation28 permutation6
    _ = mixedMoment B node613 node613Labels := by rfl

theorem canonical40988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40988 raw40988Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw40988 raw40988Labels = mixedMoment B raw40988step0 raw40988step0Labels := by
      have hz : ∀ j, raw40988 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40988step0 = (fun i j => raw40988 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40988step0 raw40988; decide +kernel
      have hl : raw40988step0Labels = raw40988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40988 raw40988Labels permutation346 hz
    mixedMoment B raw40988step0 raw40988step0Labels = mixedMoment B raw40988step1 raw40988step1Labels := by
      have hz : ∀ j, raw40988step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40988step1 = (fun i j => raw40988step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40988step1 raw40988step0; decide +kernel
      have hl : raw40988step1Labels = raw40988step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40988step0 raw40988step0Labels permutation56 hz
    mixedMoment B raw40988step1 raw40988step1Labels = mixedMoment B raw40988step2 raw40988step2Labels := by
      have ha : raw40988step2 = (fun i j => raw40988step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40988step2 raw40988step1; decide +kernel
      have hl : raw40988step2Labels = raw40988step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40988step1 raw40988step1Labels permutation23 permutation6
    _ = mixedMoment B node1087 node1087Labels := by rfl

theorem canonical40989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40989 raw40989Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw40989 raw40989Labels = mixedMoment B raw40989step0 raw40989step0Labels := by
      have hz : ∀ j, raw40989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40989step0 = (fun i j => raw40989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40989step0 raw40989; decide +kernel
      have hl : raw40989step0Labels = raw40989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40989 raw40989Labels permutation346 hz
    mixedMoment B raw40989step0 raw40989step0Labels = mixedMoment B raw40989step1 raw40989step1Labels := by
      have hz : ∀ j, raw40989step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40989step1 = (fun i j => raw40989step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40989step1 raw40989step0; decide +kernel
      have hl : raw40989step1Labels = raw40989step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40989step0 raw40989step0Labels permutation56 hz
    mixedMoment B raw40989step1 raw40989step1Labels = mixedMoment B raw40989step2 raw40989step2Labels := by
      have ha : raw40989step2 = (fun i j => raw40989step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40989step2 raw40989step1; decide +kernel
      have hl : raw40989step2Labels = raw40989step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40989step1 raw40989step1Labels permutation24 permutation6
    _ = mixedMoment B node1049 node1049Labels := by rfl

theorem canonical40990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40990 raw40990Labels = mixedMoment B node937 node937Labels := by
  calc
    mixedMoment B raw40990 raw40990Labels = mixedMoment B raw40990step0 raw40990step0Labels := by
      have hz : ∀ j, raw40990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40990step0 = (fun i j => raw40990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40990step0 raw40990; decide +kernel
      have hl : raw40990step0Labels = raw40990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40990 raw40990Labels permutation346 hz
    mixedMoment B raw40990step0 raw40990step0Labels = mixedMoment B raw40990step1 raw40990step1Labels := by
      have hz : ∀ j, raw40990step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40990step1 = (fun i j => raw40990step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40990step1 raw40990step0; decide +kernel
      have hl : raw40990step1Labels = raw40990step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40990step0 raw40990step0Labels permutation56 hz
    mixedMoment B raw40990step1 raw40990step1Labels = mixedMoment B raw40990step2 raw40990step2Labels := by
      have ha : raw40990step2 = (fun i j => raw40990step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40990step2 raw40990step1; decide +kernel
      have hl : raw40990step2Labels = raw40990step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40990step1 raw40990step1Labels permutation24 permutation6
    _ = mixedMoment B node937 node937Labels := by rfl

theorem canonical40991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40991 raw40991Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw40991 raw40991Labels = mixedMoment B raw40991step0 raw40991step0Labels := by
      have hz : ∀ j, raw40991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40991step0 = (fun i j => raw40991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40991step0 raw40991; decide +kernel
      have hl : raw40991step0Labels = raw40991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40991 raw40991Labels permutation346 hz
    mixedMoment B raw40991step0 raw40991step0Labels = mixedMoment B raw40991step1 raw40991step1Labels := by
      have hz : ∀ j, raw40991step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40991step1 = (fun i j => raw40991step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40991step1 raw40991step0; decide +kernel
      have hl : raw40991step1Labels = raw40991step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40991step0 raw40991step0Labels permutation56 hz
    mixedMoment B raw40991step1 raw40991step1Labels = mixedMoment B raw40991step2 raw40991step2Labels := by
      have ha : raw40991step2 = (fun i j => raw40991step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40991step2 raw40991step1; decide +kernel
      have hl : raw40991step2Labels = raw40991step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40991step1 raw40991step1Labels permutation15 permutation6
    mixedMoment B raw40991step2 raw40991step2Labels = mixedMoment B raw40991step3 raw40991step3Labels := by
      have ha : raw40991step3 = -raw40991step2 := by apply Matrix.ext; change ∀ i j, raw40991step3 i j = -(raw40991step2 i j); unfold raw40991step3 raw40991step2; decide +kernel
      have hl : raw40991step3Labels = raw40991step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1818 node1818Labels := by rfl

theorem canonical40992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40992 raw40992Labels = mixedMoment B node610 node610Labels := by
  calc
    mixedMoment B raw40992 raw40992Labels = mixedMoment B raw40992step0 raw40992step0Labels := by
      have hz : ∀ j, raw40992 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40992step0 = (fun i j => raw40992 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40992step0 raw40992; decide +kernel
      have hl : raw40992step0Labels = raw40992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40992 raw40992Labels permutation265 hz
    mixedMoment B raw40992step0 raw40992step0Labels = mixedMoment B raw40992step1 raw40992step1Labels := by
      have ha : raw40992step1 = (fun i j => raw40992step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40992step1 raw40992step0; decide +kernel
      have hl : raw40992step1Labels = raw40992step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40992step0 raw40992step0Labels permutation137 permutation6
    _ = mixedMoment B node610 node610Labels := by rfl

theorem canonical40993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40993 raw40993Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw40993 raw40993Labels = mixedMoment B raw40993step0 raw40993step0Labels := by
      have hz : ∀ j, raw40993 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40993step0 = (fun i j => raw40993 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40993step0 raw40993; decide +kernel
      have hl : raw40993step0Labels = raw40993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40993 raw40993Labels permutation265 hz
    mixedMoment B raw40993step0 raw40993step0Labels = mixedMoment B raw40993step1 raw40993step1Labels := by
      have ha : raw40993step1 = (fun i j => raw40993step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40993step1 raw40993step0; decide +kernel
      have hl : raw40993step1Labels = raw40993step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40993step0 raw40993step0Labels permutation125 permutation6
    _ = mixedMoment B node1044 node1044Labels := by rfl

theorem canonical40994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40994 raw40994Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw40994 raw40994Labels = mixedMoment B raw40994step0 raw40994step0Labels := by
      have hz : ∀ j, raw40994 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40994step0 = (fun i j => raw40994 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40994step0 raw40994; decide +kernel
      have hl : raw40994step0Labels = raw40994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40994 raw40994Labels permutation265 hz
    mixedMoment B raw40994step0 raw40994step0Labels = mixedMoment B raw40994step1 raw40994step1Labels := by
      have ha : raw40994step1 = (fun i j => raw40994step0 (permutation124 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40994step1 raw40994step0; decide +kernel
      have hl : raw40994step1Labels = raw40994step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40994step0 raw40994step0Labels permutation124 permutation6
    _ = mixedMoment B node932 node932Labels := by rfl

theorem canonical40995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40995 raw40995Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw40995 raw40995Labels = mixedMoment B raw40995step0 raw40995step0Labels := by
      have hz : ∀ j, raw40995 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40995step0 = (fun i j => raw40995 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40995step0 raw40995; decide +kernel
      have hl : raw40995step0Labels = raw40995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40995 raw40995Labels permutation265 hz
    mixedMoment B raw40995step0 raw40995step0Labels = mixedMoment B raw40995step1 raw40995step1Labels := by
      have ha : raw40995step1 = (fun i j => raw40995step0 (permutation124 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40995step1 raw40995step0; decide +kernel
      have hl : raw40995step1Labels = raw40995step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40995step0 raw40995step0Labels permutation124 permutation6
    _ = mixedMoment B node2341 node2341Labels := by rfl

theorem canonical40996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40996 raw40996Labels = mixedMoment B node929 node929Labels := by
  calc
    mixedMoment B raw40996 raw40996Labels = mixedMoment B raw40996step0 raw40996step0Labels := by
      have ha : raw40996step0 = (fun i j => raw40996 (permutation577 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40996step0 raw40996; decide +kernel
      have hl : raw40996step0Labels = raw40996Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40996 raw40996Labels permutation577 permutation6
    _ = mixedMoment B node929 node929Labels := by rfl

theorem canonical40997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40997 raw40997Labels = mixedMoment B node2338 node2338Labels := by
  calc
    mixedMoment B raw40997 raw40997Labels = mixedMoment B raw40997step0 raw40997step0Labels := by
      have ha : raw40997step0 = (fun i j => raw40997 (permutation577 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40997step0 raw40997; decide +kernel
      have hl : raw40997step0Labels = raw40997Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40997 raw40997Labels permutation577 permutation6
    _ = mixedMoment B node2338 node2338Labels := by rfl

theorem canonical40998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40998 raw40998Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw40998 raw40998Labels = mixedMoment B raw40998step0 raw40998step0Labels := by
      have hz : ∀ j, raw40998 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40998step0 = (fun i j => raw40998 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40998step0 raw40998; decide +kernel
      have hl : raw40998step0Labels = raw40998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40998 raw40998Labels permutation520 hz
    mixedMoment B raw40998step0 raw40998step0Labels = mixedMoment B raw40998step1 raw40998step1Labels := by
      have hz : ∀ j, raw40998step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40998step1 = (fun i j => raw40998step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40998step1 raw40998step0; decide +kernel
      have hl : raw40998step1Labels = raw40998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40998step0 raw40998step0Labels permutation104 hz
    mixedMoment B raw40998step1 raw40998step1Labels = mixedMoment B raw40998step2 raw40998step2Labels := by
      have hz : ∀ j, raw40998step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40998step2 = (fun i j => raw40998step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40998step2 raw40998step1; decide +kernel
      have hl : raw40998step2Labels = raw40998step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40998step1 raw40998step1Labels permutation20 hz
    mixedMoment B raw40998step2 raw40998step2Labels = mixedMoment B raw40998step3 raw40998step3Labels := by
      have ha : raw40998step3 = (fun i j => raw40998step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40998step3 raw40998step2; decide +kernel
      have hl : raw40998step3Labels = raw40998step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40998step2 raw40998step2Labels permutation7 permutation3
    mixedMoment B raw40998step3 raw40998step3Labels = mixedMoment B raw40998step4 raw40998step4Labels := by
      have ha : raw40998step4 = -raw40998step3 := by apply Matrix.ext; change ∀ i j, raw40998step4 i j = -(raw40998step3 i j); unfold raw40998step4 raw40998step3; decide +kernel
      have hl : raw40998step4Labels = raw40998step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2789 node2789Labels := by rfl

theorem canonical40999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40999 raw40999Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw40999 raw40999Labels = mixedMoment B raw40999step0 raw40999step0Labels := by
      have hz : ∀ j, raw40999 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40999step0 = (fun i j => raw40999 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40999step0 raw40999; decide +kernel
      have hl : raw40999step0Labels = raw40999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40999 raw40999Labels permutation434 hz
    mixedMoment B raw40999step0 raw40999step0Labels = mixedMoment B raw40999step1 raw40999step1Labels := by
      have hz : ∀ j, raw40999step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40999step1 = (fun i j => raw40999step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40999step1 raw40999step0; decide +kernel
      have hl : raw40999step1Labels = raw40999step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40999step0 raw40999step0Labels permutation80 hz
    mixedMoment B raw40999step1 raw40999step1Labels = mixedMoment B raw40999step2 raw40999step2Labels := by
      have ha : raw40999step2 = (fun i j => raw40999step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40999step2 raw40999step1; decide +kernel
      have hl : raw40999step2Labels = raw40999step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40999step1 raw40999step1Labels permutation11 permutation6
    mixedMoment B raw40999step2 raw40999step2Labels = mixedMoment B raw40999step3 raw40999step3Labels := by
      have ha : raw40999step3 = -raw40999step2 := by apply Matrix.ext; change ∀ i j, raw40999step3 i j = -(raw40999step2 i j); unfold raw40999step3 raw40999step2; decide +kernel
      have hl : raw40999step3Labels = raw40999step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2967 node2967Labels := by rfl

theorem canonical41000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41000 raw41000Labels = mixedMoment B node2888 node2888Labels := by
  calc
    mixedMoment B raw41000 raw41000Labels = mixedMoment B raw41000step0 raw41000step0Labels := by
      have hz : ∀ j, raw41000 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41000step0 = (fun i j => raw41000 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41000step0 raw41000; decide +kernel
      have hl : raw41000step0Labels = raw41000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41000 raw41000Labels permutation434 hz
    mixedMoment B raw41000step0 raw41000step0Labels = mixedMoment B raw41000step1 raw41000step1Labels := by
      have hz : ∀ j, raw41000step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41000step1 = (fun i j => raw41000step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41000step1 raw41000step0; decide +kernel
      have hl : raw41000step1Labels = raw41000step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41000step0 raw41000step0Labels permutation80 hz
    mixedMoment B raw41000step1 raw41000step1Labels = mixedMoment B raw41000step2 raw41000step2Labels := by
      have ha : raw41000step2 = (fun i j => raw41000step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41000step2 raw41000step1; decide +kernel
      have hl : raw41000step2Labels = raw41000step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41000step1 raw41000step1Labels permutation11 permutation6
    mixedMoment B raw41000step2 raw41000step2Labels = mixedMoment B raw41000step3 raw41000step3Labels := by
      have ha : raw41000step3 = -raw41000step2 := by apply Matrix.ext; change ∀ i j, raw41000step3 i j = -(raw41000step2 i j); unfold raw41000step3 raw41000step2; decide +kernel
      have hl : raw41000step3Labels = raw41000step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2888 node2888Labels := by rfl

theorem canonical41001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41001 raw41001Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw41001 raw41001Labels = mixedMoment B raw41001step0 raw41001step0Labels := by
      have hz : ∀ j, raw41001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41001step0 = (fun i j => raw41001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41001step0 raw41001; decide +kernel
      have hl : raw41001step0Labels = raw41001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41001 raw41001Labels permutation346 hz
    mixedMoment B raw41001step0 raw41001step0Labels = mixedMoment B raw41001step1 raw41001step1Labels := by
      have ha : raw41001step1 = (fun i j => raw41001step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41001step1 raw41001step0; decide +kernel
      have hl : raw41001step1Labels = raw41001step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41001step0 raw41001step0Labels permutation43 permutation6
    mixedMoment B raw41001step1 raw41001step1Labels = mixedMoment B raw41001step2 raw41001step2Labels := by
      have ha : raw41001step2 = -raw41001step1 := by apply Matrix.ext; change ∀ i j, raw41001step2 i j = -(raw41001step1 i j); unfold raw41001step2 raw41001step1; decide +kernel
      have hl : raw41001step2Labels = raw41001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2952 node2952Labels := by rfl

theorem canonical41002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41002 raw41002Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw41002 raw41002Labels = mixedMoment B raw41002step0 raw41002step0Labels := by
      have hz : ∀ j, raw41002 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41002step0 = (fun i j => raw41002 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41002step0 raw41002; decide +kernel
      have hl : raw41002step0Labels = raw41002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41002 raw41002Labels permutation346 hz
    mixedMoment B raw41002step0 raw41002step0Labels = mixedMoment B raw41002step1 raw41002step1Labels := by
      have ha : raw41002step1 = (fun i j => raw41002step0 (permutation41 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41002step1 raw41002step0; decide +kernel
      have hl : raw41002step1Labels = raw41002step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41002step0 raw41002step0Labels permutation41 permutation6
    mixedMoment B raw41002step1 raw41002step1Labels = mixedMoment B raw41002step2 raw41002step2Labels := by
      have ha : raw41002step2 = -raw41002step1 := by apply Matrix.ext; change ∀ i j, raw41002step2 i j = -(raw41002step1 i j); unfold raw41002step2 raw41002step1; decide +kernel
      have hl : raw41002step2Labels = raw41002step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2930 node2930Labels := by rfl

theorem canonical41003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41003 raw41003Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw41003 raw41003Labels = mixedMoment B raw41003step0 raw41003step0Labels := by
      have hz : ∀ j, raw41003 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41003step0 = (fun i j => raw41003 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41003step0 raw41003; decide +kernel
      have hl : raw41003step0Labels = raw41003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41003 raw41003Labels permutation520 hz
    mixedMoment B raw41003step0 raw41003step0Labels = mixedMoment B raw41003step1 raw41003step1Labels := by
      have hz : ∀ j, raw41003step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41003step1 = (fun i j => raw41003step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41003step1 raw41003step0; decide +kernel
      have hl : raw41003step1Labels = raw41003step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41003step0 raw41003step0Labels permutation104 hz
    mixedMoment B raw41003step1 raw41003step1Labels = mixedMoment B raw41003step2 raw41003step2Labels := by
      have ha : raw41003step2 = (fun i j => raw41003step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41003step2 raw41003step1; decide +kernel
      have hl : raw41003step2Labels = raw41003step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41003step1 raw41003step1Labels permutation31 permutation3
    mixedMoment B raw41003step2 raw41003step2Labels = mixedMoment B raw41003step3 raw41003step3Labels := by
      have ha : raw41003step3 = -raw41003step2 := by apply Matrix.ext; change ∀ i j, raw41003step3 i j = -(raw41003step2 i j); unfold raw41003step3 raw41003step2; decide +kernel
      have hl : raw41003step3Labels = raw41003step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2769 node2769Labels := by rfl

theorem canonical41004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41004 raw41004Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw41004 raw41004Labels = mixedMoment B raw41004step0 raw41004step0Labels := by
      have hz : ∀ j, raw41004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41004step0 = (fun i j => raw41004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41004step0 raw41004; decide +kernel
      have hl : raw41004step0Labels = raw41004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41004 raw41004Labels permutation434 hz
    mixedMoment B raw41004step0 raw41004step0Labels = mixedMoment B raw41004step1 raw41004step1Labels := by
      have ha : raw41004step1 = (fun i j => raw41004step0 (permutation46 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41004step1 raw41004step0; decide +kernel
      have hl : raw41004step1Labels = raw41004step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41004step0 raw41004step0Labels permutation46 permutation6
    mixedMoment B raw41004step1 raw41004step1Labels = mixedMoment B raw41004step2 raw41004step2Labels := by
      have ha : raw41004step2 = -raw41004step1 := by apply Matrix.ext; change ∀ i j, raw41004step2 i j = -(raw41004step1 i j); unfold raw41004step2 raw41004step1; decide +kernel
      have hl : raw41004step2Labels = raw41004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2964 node2964Labels := by rfl

theorem canonical41005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41005 raw41005Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw41005 raw41005Labels = mixedMoment B raw41005step0 raw41005step0Labels := by
      have hz : ∀ j, raw41005 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41005step0 = (fun i j => raw41005 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41005step0 raw41005; decide +kernel
      have hl : raw41005step0Labels = raw41005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41005 raw41005Labels permutation434 hz
    mixedMoment B raw41005step0 raw41005step0Labels = mixedMoment B raw41005step1 raw41005step1Labels := by
      have ha : raw41005step1 = (fun i j => raw41005step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41005step1 raw41005step0; decide +kernel
      have hl : raw41005step1Labels = raw41005step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41005step0 raw41005step0Labels permutation55 permutation6
    mixedMoment B raw41005step1 raw41005step1Labels = mixedMoment B raw41005step2 raw41005step2Labels := by
      have ha : raw41005step2 = -raw41005step1 := by apply Matrix.ext; change ∀ i j, raw41005step2 i j = -(raw41005step1 i j); unfold raw41005step2 raw41005step1; decide +kernel
      have hl : raw41005step2Labels = raw41005step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical41006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41006 raw41006Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw41006 raw41006Labels = mixedMoment B raw41006step0 raw41006step0Labels := by
      have hz : ∀ j, raw41006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41006step0 = (fun i j => raw41006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41006step0 raw41006; decide +kernel
      have hl : raw41006step0Labels = raw41006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41006 raw41006Labels permutation434 hz
    mixedMoment B raw41006step0 raw41006step0Labels = mixedMoment B raw41006step1 raw41006step1Labels := by
      have ha : raw41006step1 = (fun i j => raw41006step0 (permutation46 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41006step1 raw41006step0; decide +kernel
      have hl : raw41006step1Labels = raw41006step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41006step0 raw41006step0Labels permutation46 permutation6
    mixedMoment B raw41006step1 raw41006step1Labels = mixedMoment B raw41006step2 raw41006step2Labels := by
      have ha : raw41006step2 = -raw41006step1 := by apply Matrix.ext; change ∀ i j, raw41006step2 i j = -(raw41006step1 i j); unfold raw41006step2 raw41006step1; decide +kernel
      have hl : raw41006step2Labels = raw41006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2885 node2885Labels := by rfl

theorem canonical41007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41007 raw41007Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw41007 raw41007Labels = mixedMoment B raw41007step0 raw41007step0Labels := by
      have ha : raw41007step0 = (fun i j => raw41007 (permutation223 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41007step0 raw41007; decide +kernel
      have hl : raw41007step0Labels = raw41007Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41007 raw41007Labels permutation223 permutation6
    mixedMoment B raw41007step0 raw41007step0Labels = mixedMoment B raw41007step1 raw41007step1Labels := by
      have ha : raw41007step1 = -raw41007step0 := by apply Matrix.ext; change ∀ i j, raw41007step1 i j = -(raw41007step0 i j); unfold raw41007step1 raw41007step0; decide +kernel
      have hl : raw41007step1Labels = raw41007step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2951 node2951Labels := by rfl

theorem canonical41008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41008 raw41008Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw41008 raw41008Labels = mixedMoment B raw41008step0 raw41008step0Labels := by
      have ha : raw41008step0 = (fun i j => raw41008 (permutation214 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41008step0 raw41008; decide +kernel
      have hl : raw41008step0Labels = raw41008Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41008 raw41008Labels permutation214 permutation6
    mixedMoment B raw41008step0 raw41008step0Labels = mixedMoment B raw41008step1 raw41008step1Labels := by
      have ha : raw41008step1 = -raw41008step0 := by apply Matrix.ext; change ∀ i j, raw41008step1 i j = -(raw41008step0 i j); unfold raw41008step1 raw41008step0; decide +kernel
      have hl : raw41008step1Labels = raw41008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2928 node2928Labels := by rfl

theorem canonical41009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41009 raw41009Labels = mixedMoment B node2878 node2878Labels := by
  calc
    mixedMoment B raw41009 raw41009Labels = mixedMoment B raw41009step0 raw41009step0Labels := by
      have ha : raw41009step0 = (fun i j => raw41009 (permutation259 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41009step0 raw41009; decide +kernel
      have hl : raw41009step0Labels = raw41009Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41009 raw41009Labels permutation259 permutation6
    mixedMoment B raw41009step0 raw41009step0Labels = mixedMoment B raw41009step1 raw41009step1Labels := by
      have ha : raw41009step1 = -raw41009step0 := by apply Matrix.ext; change ∀ i j, raw41009step1 i j = -(raw41009step0 i j); unfold raw41009step1 raw41009step0; decide +kernel
      have hl : raw41009step1Labels = raw41009step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2878 node2878Labels := by rfl

theorem canonical41010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41010 raw41010Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw41010 raw41010Labels = mixedMoment B raw41010step0 raw41010step0Labels := by
      have ha : raw41010step0 = (fun i j => raw41010 (permutation245 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41010step0 raw41010; decide +kernel
      have hl : raw41010step0Labels = raw41010Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41010 raw41010Labels permutation245 permutation6
    mixedMoment B raw41010step0 raw41010step0Labels = mixedMoment B raw41010step1 raw41010step1Labels := by
      have ha : raw41010step1 = -raw41010step0 := by apply Matrix.ext; change ∀ i j, raw41010step1 i j = -(raw41010step0 i j); unfold raw41010step1 raw41010step0; decide +kernel
      have hl : raw41010step1Labels = raw41010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3074 node3074Labels := by rfl

theorem canonical41011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41011 raw41011Labels = mixedMoment B node2886 node2886Labels := by
  calc
    mixedMoment B raw41011 raw41011Labels = mixedMoment B raw41011step0 raw41011step0Labels := by
      have hz : ∀ j, raw41011 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41011step0 = (fun i j => raw41011 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41011step0 raw41011; decide +kernel
      have hl : raw41011step0Labels = raw41011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41011 raw41011Labels permutation434 hz
    mixedMoment B raw41011step0 raw41011step0Labels = mixedMoment B raw41011step1 raw41011step1Labels := by
      have hz : ∀ j, raw41011step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41011step1 = (fun i j => raw41011step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41011step1 raw41011step0; decide +kernel
      have hl : raw41011step1Labels = raw41011step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41011step0 raw41011step0Labels permutation80 hz
    mixedMoment B raw41011step1 raw41011step1Labels = mixedMoment B raw41011step2 raw41011step2Labels := by
      have ha : raw41011step2 = (fun i j => raw41011step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41011step2 raw41011step1; decide +kernel
      have hl : raw41011step2Labels = raw41011step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41011step1 raw41011step1Labels permutation29 permutation6
    _ = mixedMoment B node2886 node2886Labels := by rfl

theorem canonical41012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41012 raw41012Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw41012 raw41012Labels = mixedMoment B raw41012step0 raw41012step0Labels := by
      have hz : ∀ j, raw41012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41012step0 = (fun i j => raw41012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41012step0 raw41012; decide +kernel
      have hl : raw41012step0Labels = raw41012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41012 raw41012Labels permutation346 hz
    mixedMoment B raw41012step0 raw41012step0Labels = mixedMoment B raw41012step1 raw41012step1Labels := by
      have ha : raw41012step1 = (fun i j => raw41012step0 (permutation42 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41012step1 raw41012step0; decide +kernel
      have hl : raw41012step1Labels = raw41012step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41012step0 raw41012step0Labels permutation42 permutation6
    mixedMoment B raw41012step1 raw41012step1Labels = mixedMoment B raw41012step2 raw41012step2Labels := by
      have ha : raw41012step2 = -raw41012step1 := by apply Matrix.ext; change ∀ i j, raw41012step2 i j = -(raw41012step1 i j); unfold raw41012step2 raw41012step1; decide +kernel
      have hl : raw41012step2Labels = raw41012step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2955 node2955Labels := by rfl

theorem canonical41013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41013 raw41013Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw41013 raw41013Labels = mixedMoment B raw41013step0 raw41013step0Labels := by
      have hz : ∀ j, raw41013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41013step0 = (fun i j => raw41013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41013step0 raw41013; decide +kernel
      have hl : raw41013step0Labels = raw41013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41013 raw41013Labels permutation346 hz
    mixedMoment B raw41013step0 raw41013step0Labels = mixedMoment B raw41013step1 raw41013step1Labels := by
      have ha : raw41013step1 = (fun i j => raw41013step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41013step1 raw41013step0; decide +kernel
      have hl : raw41013step1Labels = raw41013step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41013step0 raw41013step0Labels permutation139 permutation6
    _ = mixedMoment B node2865 node2865Labels := by rfl

theorem canonical41014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41014 raw41014Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw41014 raw41014Labels = mixedMoment B raw41014step0 raw41014step0Labels := by
      have hz : ∀ j, raw41014 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41014step0 = (fun i j => raw41014 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41014step0 raw41014; decide +kernel
      have hl : raw41014step0Labels = raw41014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41014 raw41014Labels permutation346 hz
    mixedMoment B raw41014step0 raw41014step0Labels = mixedMoment B raw41014step1 raw41014step1Labels := by
      have ha : raw41014step1 = (fun i j => raw41014step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41014step1 raw41014step0; decide +kernel
      have hl : raw41014step1Labels = raw41014step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41014step0 raw41014step0Labels permutation54 permutation6
    mixedMoment B raw41014step1 raw41014step1Labels = mixedMoment B raw41014step2 raw41014step2Labels := by
      have ha : raw41014step2 = -raw41014step1 := by apply Matrix.ext; change ∀ i j, raw41014step2 i j = -(raw41014step1 i j); unfold raw41014step2 raw41014step1; decide +kernel
      have hl : raw41014step2Labels = raw41014step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2882 node2882Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10829 raw10829Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw10829 raw10829Labels = mixedMoment B raw10829step0 raw10829step0Labels := by
      have hz : ∀ j, raw10829 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10829step0 = (fun i j => raw10829 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10829step0 raw10829; decide +kernel
      have hl : raw10829step0Labels = raw10829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10829 raw10829Labels permutation434 hz
    mixedMoment B raw10829step0 raw10829step0Labels = mixedMoment B raw10829step1 raw10829step1Labels := by
      have hz : ∀ j, raw10829step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10829step1 = (fun i j => raw10829step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10829step1 raw10829step0; decide +kernel
      have hl : raw10829step1Labels = raw10829step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10829step0 raw10829step0Labels permutation80 hz
    mixedMoment B raw10829step1 raw10829step1Labels = mixedMoment B raw10829step2 raw10829step2Labels := by
      have ha : raw10829step2 = (fun i j => raw10829step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10829step2 raw10829step1; decide +kernel
      have hl : raw10829step2Labels = raw10829step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10829step1 raw10829step1Labels permutation11 permutation6
    mixedMoment B raw10829step2 raw10829step2Labels = mixedMoment B raw10829step3 raw10829step3Labels := by
      have ha : raw10829step3 = -raw10829step2 := by apply Matrix.ext; change ∀ i j, raw10829step3 i j = -(raw10829step2 i j); unfold raw10829step3 raw10829step2; decide +kernel
      have hl : raw10829step3Labels = raw10829step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3098 node3098Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11232 raw11232Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw11232 raw11232Labels = mixedMoment B raw11232step0 raw11232step0Labels := by
      have hz : ∀ j, raw11232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11232step0 = (fun i j => raw11232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11232step0 raw11232; decide +kernel
      have hl : raw11232step0Labels = raw11232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11232 raw11232Labels permutation434 hz
    mixedMoment B raw11232step0 raw11232step0Labels = mixedMoment B raw11232step1 raw11232step1Labels := by
      have ha : raw11232step1 = (fun i j => raw11232step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11232step1 raw11232step0; decide +kernel
      have hl : raw11232step1Labels = raw11232step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11232step0 raw11232step0Labels permutation49 permutation6
    mixedMoment B raw11232step1 raw11232step1Labels = mixedMoment B raw11232step2 raw11232step2Labels := by
      have ha : raw11232step2 = -raw11232step1 := by apply Matrix.ext; change ∀ i j, raw11232step2 i j = -(raw11232step1 i j); unfold raw11232step2 raw11232step1; decide +kernel
      have hl : raw11232step2Labels = raw11232step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3097 node3097Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1568 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1568) =
      Integer.Sparse.eval keyMomentRow1568 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1568).leftCharge (GramAssembly.key 1568).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 618) := by
    have ha : gramCharges (GramAssembly.key 1568).leftCharge (GramAssembly.key 1568).rightCharge = raw40986 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40986Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40986 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1568).leftCharge (GramAssembly.key 1568).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1568, Integer.Sparse.eval]

theorem keyMoment1569 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1569) =
      Integer.Sparse.eval keyMomentRow1569 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1569).leftCharge (GramAssembly.key 1569).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 613) := by
    have ha : gramCharges (GramAssembly.key 1569).leftCharge (GramAssembly.key 1569).rightCharge = raw40987 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40987Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40987 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1569).leftCharge (GramAssembly.key 1569).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1569, Integer.Sparse.eval]

theorem keyMoment1570 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1570) =
      Integer.Sparse.eval keyMomentRow1570 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1570).leftCharge (GramAssembly.key 1570).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1087) := by
    have ha : gramCharges (GramAssembly.key 1570).leftCharge (GramAssembly.key 1570).rightCharge = raw40988 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40988Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40988 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1570).leftCharge (GramAssembly.key 1570).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1570, Integer.Sparse.eval]

theorem keyMoment1571 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1571) =
      Integer.Sparse.eval keyMomentRow1571 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1571).leftCharge (GramAssembly.key 1571).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1049) := by
    have ha : gramCharges (GramAssembly.key 1571).leftCharge (GramAssembly.key 1571).rightCharge = raw40989 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40989Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40989 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1571).leftCharge (GramAssembly.key 1571).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1571, Integer.Sparse.eval]

theorem keyMoment1572 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1572) =
      Integer.Sparse.eval keyMomentRow1572 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1572).leftCharge (GramAssembly.key 1572).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 937) := by
    have ha : gramCharges (GramAssembly.key 1572).leftCharge (GramAssembly.key 1572).rightCharge = raw40990 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40990Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40990 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1572).leftCharge (GramAssembly.key 1572).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1572, Integer.Sparse.eval]

theorem keyMoment1573 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1573) =
      Integer.Sparse.eval keyMomentRow1573 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1573).leftCharge (GramAssembly.key 1573).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1818) := by
    have ha : gramCharges (GramAssembly.key 1573).leftCharge (GramAssembly.key 1573).rightCharge = raw40991 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40991Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40991 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1573).leftCharge (GramAssembly.key 1573).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1573, Integer.Sparse.eval]

theorem keyMoment1574 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1574) =
      Integer.Sparse.eval keyMomentRow1574 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1574).leftCharge (GramAssembly.key 1574).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 610) := by
    have ha : gramCharges (GramAssembly.key 1574).leftCharge (GramAssembly.key 1574).rightCharge = raw40992 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40992Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40992 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1574).leftCharge (GramAssembly.key 1574).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1574, Integer.Sparse.eval]

theorem keyMoment1575 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1575) =
      Integer.Sparse.eval keyMomentRow1575 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1575).leftCharge (GramAssembly.key 1575).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1044) := by
    have ha : gramCharges (GramAssembly.key 1575).leftCharge (GramAssembly.key 1575).rightCharge = raw40993 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40993Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40993 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1575).leftCharge (GramAssembly.key 1575).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1575, Integer.Sparse.eval]

theorem keyMoment1576 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1576) =
      Integer.Sparse.eval keyMomentRow1576 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1576).leftCharge (GramAssembly.key 1576).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 932) := by
    have ha : gramCharges (GramAssembly.key 1576).leftCharge (GramAssembly.key 1576).rightCharge = raw40994 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40994Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40994 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1576).leftCharge (GramAssembly.key 1576).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1576, Integer.Sparse.eval]

theorem keyMoment1577 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1577) =
      Integer.Sparse.eval keyMomentRow1577 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1577).leftCharge (GramAssembly.key 1577).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2341) := by
    have ha : gramCharges (GramAssembly.key 1577).leftCharge (GramAssembly.key 1577).rightCharge = raw40995 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40995Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40995 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1577).leftCharge (GramAssembly.key 1577).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1577, Integer.Sparse.eval]

theorem keyMoment1578 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1578) =
      Integer.Sparse.eval keyMomentRow1578 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1578).leftCharge (GramAssembly.key 1578).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 929) := by
    have ha : gramCharges (GramAssembly.key 1578).leftCharge (GramAssembly.key 1578).rightCharge = raw40996 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40996Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40996 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1578).leftCharge (GramAssembly.key 1578).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1578, Integer.Sparse.eval]

theorem keyMoment1579 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1579) =
      Integer.Sparse.eval keyMomentRow1579 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1579).leftCharge (GramAssembly.key 1579).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2338) := by
    have ha : gramCharges (GramAssembly.key 1579).leftCharge (GramAssembly.key 1579).rightCharge = raw40997 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40997Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40997 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1579).leftCharge (GramAssembly.key 1579).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1579, Integer.Sparse.eval]

theorem keyMoment1580 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1580) =
      Integer.Sparse.eval keyMomentRow1580 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1580).leftCharge (GramAssembly.key 1580).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2789) := by
    have ha : gramCharges (GramAssembly.key 1580).leftCharge (GramAssembly.key 1580).rightCharge = raw40998 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40998Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40998 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1580).leftCharge (GramAssembly.key 1580).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1580, Integer.Sparse.eval]

theorem keyMoment1581 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1581) =
      Integer.Sparse.eval keyMomentRow1581 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1581).leftCharge (GramAssembly.key 1581).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2967) := by
    have ha : gramCharges (GramAssembly.key 1581).leftCharge (GramAssembly.key 1581).rightCharge = raw40999 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40999Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40999 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1581).leftCharge (GramAssembly.key 1581).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1581, Integer.Sparse.eval]

theorem keyMoment1582 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1582) =
      Integer.Sparse.eval keyMomentRow1582 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1582).leftCharge (GramAssembly.key 1582).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3098) := by
    have ha : gramCharges (GramAssembly.key 1582).leftCharge (GramAssembly.key 1582).rightCharge = raw10829 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw10829Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical10829 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1582).leftCharge (GramAssembly.key 1582).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1582, Integer.Sparse.eval]

theorem keyMoment1583 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1583) =
      Integer.Sparse.eval keyMomentRow1583 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1583).leftCharge (GramAssembly.key 1583).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2888) := by
    have ha : gramCharges (GramAssembly.key 1583).leftCharge (GramAssembly.key 1583).rightCharge = raw41000 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41000Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41000 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1583).leftCharge (GramAssembly.key 1583).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1583, Integer.Sparse.eval]

theorem keyMoment1584 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1584) =
      Integer.Sparse.eval keyMomentRow1584 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1584).leftCharge (GramAssembly.key 1584).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2952) := by
    have ha : gramCharges (GramAssembly.key 1584).leftCharge (GramAssembly.key 1584).rightCharge = raw41001 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41001Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41001 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1584).leftCharge (GramAssembly.key 1584).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1584, Integer.Sparse.eval]

theorem keyMoment1585 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1585) =
      Integer.Sparse.eval keyMomentRow1585 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1585).leftCharge (GramAssembly.key 1585).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2930) := by
    have ha : gramCharges (GramAssembly.key 1585).leftCharge (GramAssembly.key 1585).rightCharge = raw41002 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41002Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41002 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1585).leftCharge (GramAssembly.key 1585).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1585, Integer.Sparse.eval]

theorem keyMoment1586 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1586) =
      Integer.Sparse.eval keyMomentRow1586 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1586).leftCharge (GramAssembly.key 1586).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2769) := by
    have ha : gramCharges (GramAssembly.key 1586).leftCharge (GramAssembly.key 1586).rightCharge = raw41003 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41003Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41003 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1586).leftCharge (GramAssembly.key 1586).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1586, Integer.Sparse.eval]

theorem keyMoment1587 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1587) =
      Integer.Sparse.eval keyMomentRow1587 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1587).leftCharge (GramAssembly.key 1587).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2964) := by
    have ha : gramCharges (GramAssembly.key 1587).leftCharge (GramAssembly.key 1587).rightCharge = raw41004 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41004Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41004 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1587).leftCharge (GramAssembly.key 1587).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1587, Integer.Sparse.eval]

theorem keyMoment1588 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1588) =
      Integer.Sparse.eval keyMomentRow1588 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1588).leftCharge (GramAssembly.key 1588).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3051) := by
    have ha : gramCharges (GramAssembly.key 1588).leftCharge (GramAssembly.key 1588).rightCharge = raw41005 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41005Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41005 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1588).leftCharge (GramAssembly.key 1588).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1588, Integer.Sparse.eval]

theorem keyMoment1589 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1589) =
      Integer.Sparse.eval keyMomentRow1589 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1589).leftCharge (GramAssembly.key 1589).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3097) := by
    have ha : gramCharges (GramAssembly.key 1589).leftCharge (GramAssembly.key 1589).rightCharge = raw11232 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw11232Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical11232 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1589).leftCharge (GramAssembly.key 1589).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1589, Integer.Sparse.eval]

theorem keyMoment1590 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1590) =
      Integer.Sparse.eval keyMomentRow1590 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1590).leftCharge (GramAssembly.key 1590).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2885) := by
    have ha : gramCharges (GramAssembly.key 1590).leftCharge (GramAssembly.key 1590).rightCharge = raw41006 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41006Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41006 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1590).leftCharge (GramAssembly.key 1590).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1590, Integer.Sparse.eval]

theorem keyMoment1591 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1591) =
      Integer.Sparse.eval keyMomentRow1591 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1591).leftCharge (GramAssembly.key 1591).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2951) := by
    have ha : gramCharges (GramAssembly.key 1591).leftCharge (GramAssembly.key 1591).rightCharge = raw41007 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41007Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41007 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1591).leftCharge (GramAssembly.key 1591).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1591, Integer.Sparse.eval]

theorem keyMoment1592 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1592) =
      Integer.Sparse.eval keyMomentRow1592 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1592).leftCharge (GramAssembly.key 1592).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2928) := by
    have ha : gramCharges (GramAssembly.key 1592).leftCharge (GramAssembly.key 1592).rightCharge = raw41008 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41008Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41008 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1592).leftCharge (GramAssembly.key 1592).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1592, Integer.Sparse.eval]

theorem keyMoment1593 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1593) =
      Integer.Sparse.eval keyMomentRow1593 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1593).leftCharge (GramAssembly.key 1593).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2878) := by
    have ha : gramCharges (GramAssembly.key 1593).leftCharge (GramAssembly.key 1593).rightCharge = raw41009 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41009Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41009 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1593).leftCharge (GramAssembly.key 1593).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1593, Integer.Sparse.eval]

theorem keyMoment1594 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1594) =
      Integer.Sparse.eval keyMomentRow1594 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1594).leftCharge (GramAssembly.key 1594).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3074) := by
    have ha : gramCharges (GramAssembly.key 1594).leftCharge (GramAssembly.key 1594).rightCharge = raw41010 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41010Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41010 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1594).leftCharge (GramAssembly.key 1594).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1594, Integer.Sparse.eval]

theorem keyMoment1595 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1595) =
      Integer.Sparse.eval keyMomentRow1595 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1595).leftCharge (GramAssembly.key 1595).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3055) := by
    have ha : gramCharges (GramAssembly.key 1595).leftCharge (GramAssembly.key 1595).rightCharge = raw30961 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw30961Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical30961 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1595).leftCharge (GramAssembly.key 1595).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1595, Integer.Sparse.eval]

theorem keyMoment1596 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1596) =
      Integer.Sparse.eval keyMomentRow1596 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1596).leftCharge (GramAssembly.key 1596).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2886) := by
    have ha : gramCharges (GramAssembly.key 1596).leftCharge (GramAssembly.key 1596).rightCharge = raw41011 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41011Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41011 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1596).leftCharge (GramAssembly.key 1596).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1596, Integer.Sparse.eval]

theorem keyMoment1597 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1597) =
      Integer.Sparse.eval keyMomentRow1597 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1597).leftCharge (GramAssembly.key 1597).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2955) := by
    have ha : gramCharges (GramAssembly.key 1597).leftCharge (GramAssembly.key 1597).rightCharge = raw41012 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41012Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41012 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1597).leftCharge (GramAssembly.key 1597).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1597, Integer.Sparse.eval]

theorem keyMoment1598 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1598) =
      Integer.Sparse.eval keyMomentRow1598 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1598).leftCharge (GramAssembly.key 1598).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2865) := by
    have ha : gramCharges (GramAssembly.key 1598).leftCharge (GramAssembly.key 1598).rightCharge = raw41013 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41013Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41013 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1598).leftCharge (GramAssembly.key 1598).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1598, Integer.Sparse.eval]

theorem keyMoment1599 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1599) =
      Integer.Sparse.eval keyMomentRow1599 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1599).leftCharge (GramAssembly.key 1599).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2882) := by
    have ha : gramCharges (GramAssembly.key 1599).leftCharge (GramAssembly.key 1599).rightCharge = raw41014 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41014Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41014 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1599).leftCharge (GramAssembly.key 1599).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1599, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1568 : keyMomentRows (1568 : Fin 2886) =
    keyMomentRow1568 := by decide +kernel

theorem keyMomentRowsAt1569 : keyMomentRows (1569 : Fin 2886) =
    keyMomentRow1569 := by decide +kernel

theorem keyMomentRowsAt1570 : keyMomentRows (1570 : Fin 2886) =
    keyMomentRow1570 := by decide +kernel

theorem keyMomentRowsAt1571 : keyMomentRows (1571 : Fin 2886) =
    keyMomentRow1571 := by decide +kernel

theorem keyMomentRowsAt1572 : keyMomentRows (1572 : Fin 2886) =
    keyMomentRow1572 := by decide +kernel

theorem keyMomentRowsAt1573 : keyMomentRows (1573 : Fin 2886) =
    keyMomentRow1573 := by decide +kernel

theorem keyMomentRowsAt1574 : keyMomentRows (1574 : Fin 2886) =
    keyMomentRow1574 := by decide +kernel

theorem keyMomentRowsAt1575 : keyMomentRows (1575 : Fin 2886) =
    keyMomentRow1575 := by decide +kernel

theorem keyMomentRowsAt1576 : keyMomentRows (1576 : Fin 2886) =
    keyMomentRow1576 := by decide +kernel

theorem keyMomentRowsAt1577 : keyMomentRows (1577 : Fin 2886) =
    keyMomentRow1577 := by decide +kernel

theorem keyMomentRowsAt1578 : keyMomentRows (1578 : Fin 2886) =
    keyMomentRow1578 := by decide +kernel

theorem keyMomentRowsAt1579 : keyMomentRows (1579 : Fin 2886) =
    keyMomentRow1579 := by decide +kernel

theorem keyMomentRowsAt1580 : keyMomentRows (1580 : Fin 2886) =
    keyMomentRow1580 := by decide +kernel

theorem keyMomentRowsAt1581 : keyMomentRows (1581 : Fin 2886) =
    keyMomentRow1581 := by decide +kernel

theorem keyMomentRowsAt1582 : keyMomentRows (1582 : Fin 2886) =
    keyMomentRow1582 := by decide +kernel

theorem keyMomentRowsAt1583 : keyMomentRows (1583 : Fin 2886) =
    keyMomentRow1583 := by decide +kernel

theorem keyMomentRowsAt1584 : keyMomentRows (1584 : Fin 2886) =
    keyMomentRow1584 := by decide +kernel

theorem keyMomentRowsAt1585 : keyMomentRows (1585 : Fin 2886) =
    keyMomentRow1585 := by decide +kernel

theorem keyMomentRowsAt1586 : keyMomentRows (1586 : Fin 2886) =
    keyMomentRow1586 := by decide +kernel

theorem keyMomentRowsAt1587 : keyMomentRows (1587 : Fin 2886) =
    keyMomentRow1587 := by decide +kernel

theorem keyMomentRowsAt1588 : keyMomentRows (1588 : Fin 2886) =
    keyMomentRow1588 := by decide +kernel

theorem keyMomentRowsAt1589 : keyMomentRows (1589 : Fin 2886) =
    keyMomentRow1589 := by decide +kernel

theorem keyMomentRowsAt1590 : keyMomentRows (1590 : Fin 2886) =
    keyMomentRow1590 := by decide +kernel

theorem keyMomentRowsAt1591 : keyMomentRows (1591 : Fin 2886) =
    keyMomentRow1591 := by decide +kernel

theorem keyMomentRowsAt1592 : keyMomentRows (1592 : Fin 2886) =
    keyMomentRow1592 := by decide +kernel

theorem keyMomentRowsAt1593 : keyMomentRows (1593 : Fin 2886) =
    keyMomentRow1593 := by decide +kernel

theorem keyMomentRowsAt1594 : keyMomentRows (1594 : Fin 2886) =
    keyMomentRow1594 := by decide +kernel

theorem keyMomentRowsAt1595 : keyMomentRows (1595 : Fin 2886) =
    keyMomentRow1595 := by decide +kernel

theorem keyMomentRowsAt1596 : keyMomentRows (1596 : Fin 2886) =
    keyMomentRow1596 := by decide +kernel

theorem keyMomentRowsAt1597 : keyMomentRows (1597 : Fin 2886) =
    keyMomentRow1597 := by decide +kernel

theorem keyMomentRowsAt1598 : keyMomentRows (1598 : Fin 2886) =
    keyMomentRow1598 := by decide +kernel

theorem keyMomentRowsAt1599 : keyMomentRows (1599 : Fin 2886) =
    keyMomentRow1599 := by decide +kernel

theorem keyMomentChunkSound49_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 49) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1568 ∨ k.val = 1569 ∨ k.val = 1570 ∨ k.val = 1571 ∨ k.val = 1572 ∨ k.val = 1573 ∨ k.val = 1574 ∨ k.val = 1575 ∨ k.val = 1576 ∨ k.val = 1577 ∨ k.val = 1578 ∨ k.val = 1579 ∨ k.val = 1580 ∨ k.val = 1581 ∨ k.val = 1582 ∨ k.val = 1583 ∨ k.val = 1584 ∨ k.val = 1585 ∨ k.val = 1586 ∨ k.val = 1587 ∨ k.val = 1588 ∨ k.val = 1589 ∨ k.val = 1590 ∨ k.val = 1591 ∨ k.val = 1592 ∨ k.val = 1593 ∨ k.val = 1594 ∨ k.val = 1595 ∨ k.val = 1596 ∨ k.val = 1597 ∨ k.val = 1598 ∨ k.val = 1599 := by omega
  rcases heq with h1568 | h1569 | h1570 | h1571 | h1572 | h1573 | h1574 | h1575 | h1576 | h1577 | h1578 | h1579 | h1580 | h1581 | h1582 | h1583 | h1584 | h1585 | h1586 | h1587 | h1588 | h1589 | h1590 | h1591 | h1592 | h1593 | h1594 | h1595 | h1596 | h1597 | h1598 | h1599
  · have he : k = (1568 : Fin 2886) := Fin.ext h1568
    subst k
    rw [keyMomentRowsAt1568]
    exact keyMoment1568 B hB
  · have he : k = (1569 : Fin 2886) := Fin.ext h1569
    subst k
    rw [keyMomentRowsAt1569]
    exact keyMoment1569 B hB
  · have he : k = (1570 : Fin 2886) := Fin.ext h1570
    subst k
    rw [keyMomentRowsAt1570]
    exact keyMoment1570 B hB
  · have he : k = (1571 : Fin 2886) := Fin.ext h1571
    subst k
    rw [keyMomentRowsAt1571]
    exact keyMoment1571 B hB
  · have he : k = (1572 : Fin 2886) := Fin.ext h1572
    subst k
    rw [keyMomentRowsAt1572]
    exact keyMoment1572 B hB
  · have he : k = (1573 : Fin 2886) := Fin.ext h1573
    subst k
    rw [keyMomentRowsAt1573]
    exact keyMoment1573 B hB
  · have he : k = (1574 : Fin 2886) := Fin.ext h1574
    subst k
    rw [keyMomentRowsAt1574]
    exact keyMoment1574 B hB
  · have he : k = (1575 : Fin 2886) := Fin.ext h1575
    subst k
    rw [keyMomentRowsAt1575]
    exact keyMoment1575 B hB
  · have he : k = (1576 : Fin 2886) := Fin.ext h1576
    subst k
    rw [keyMomentRowsAt1576]
    exact keyMoment1576 B hB
  · have he : k = (1577 : Fin 2886) := Fin.ext h1577
    subst k
    rw [keyMomentRowsAt1577]
    exact keyMoment1577 B hB
  · have he : k = (1578 : Fin 2886) := Fin.ext h1578
    subst k
    rw [keyMomentRowsAt1578]
    exact keyMoment1578 B hB
  · have he : k = (1579 : Fin 2886) := Fin.ext h1579
    subst k
    rw [keyMomentRowsAt1579]
    exact keyMoment1579 B hB
  · have he : k = (1580 : Fin 2886) := Fin.ext h1580
    subst k
    rw [keyMomentRowsAt1580]
    exact keyMoment1580 B hB
  · have he : k = (1581 : Fin 2886) := Fin.ext h1581
    subst k
    rw [keyMomentRowsAt1581]
    exact keyMoment1581 B hB
  · have he : k = (1582 : Fin 2886) := Fin.ext h1582
    subst k
    rw [keyMomentRowsAt1582]
    exact keyMoment1582 B hB
  · have he : k = (1583 : Fin 2886) := Fin.ext h1583
    subst k
    rw [keyMomentRowsAt1583]
    exact keyMoment1583 B hB
  · have he : k = (1584 : Fin 2886) := Fin.ext h1584
    subst k
    rw [keyMomentRowsAt1584]
    exact keyMoment1584 B hB
  · have he : k = (1585 : Fin 2886) := Fin.ext h1585
    subst k
    rw [keyMomentRowsAt1585]
    exact keyMoment1585 B hB
  · have he : k = (1586 : Fin 2886) := Fin.ext h1586
    subst k
    rw [keyMomentRowsAt1586]
    exact keyMoment1586 B hB
  · have he : k = (1587 : Fin 2886) := Fin.ext h1587
    subst k
    rw [keyMomentRowsAt1587]
    exact keyMoment1587 B hB
  · have he : k = (1588 : Fin 2886) := Fin.ext h1588
    subst k
    rw [keyMomentRowsAt1588]
    exact keyMoment1588 B hB
  · have he : k = (1589 : Fin 2886) := Fin.ext h1589
    subst k
    rw [keyMomentRowsAt1589]
    exact keyMoment1589 B hB
  · have he : k = (1590 : Fin 2886) := Fin.ext h1590
    subst k
    rw [keyMomentRowsAt1590]
    exact keyMoment1590 B hB
  · have he : k = (1591 : Fin 2886) := Fin.ext h1591
    subst k
    rw [keyMomentRowsAt1591]
    exact keyMoment1591 B hB
  · have he : k = (1592 : Fin 2886) := Fin.ext h1592
    subst k
    rw [keyMomentRowsAt1592]
    exact keyMoment1592 B hB
  · have he : k = (1593 : Fin 2886) := Fin.ext h1593
    subst k
    rw [keyMomentRowsAt1593]
    exact keyMoment1593 B hB
  · have he : k = (1594 : Fin 2886) := Fin.ext h1594
    subst k
    rw [keyMomentRowsAt1594]
    exact keyMoment1594 B hB
  · have he : k = (1595 : Fin 2886) := Fin.ext h1595
    subst k
    rw [keyMomentRowsAt1595]
    exact keyMoment1595 B hB
  · have he : k = (1596 : Fin 2886) := Fin.ext h1596
    subst k
    rw [keyMomentRowsAt1596]
    exact keyMoment1596 B hB
  · have he : k = (1597 : Fin 2886) := Fin.ext h1597
    subst k
    rw [keyMomentRowsAt1597]
    exact keyMoment1597 B hB
  · have he : k = (1598 : Fin 2886) := Fin.ext h1598
    subst k
    rw [keyMomentRowsAt1598]
    exact keyMoment1598 B hB
  · have he : k = (1599 : Fin 2886) := Fin.ext h1599
    subst k
    rw [keyMomentRowsAt1599]
    exact keyMoment1599 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound49_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound49_e_oai
