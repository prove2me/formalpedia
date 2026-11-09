-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound56_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:58:11.093532+00:00
-- url     : https://prove2.me/submissions/0804defb-bf61-4e38-ae7a-21d7f901deb6

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

theorem canonical41205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41205 raw41205Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw41205 raw41205Labels = mixedMoment B raw41205step0 raw41205step0Labels := by
      have hz : ∀ j, raw41205 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41205step0 = (fun i j => raw41205 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41205step0 raw41205; decide +kernel
      have hl : raw41205step0Labels = raw41205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41205 raw41205Labels permutation434 hz
    mixedMoment B raw41205step0 raw41205step0Labels = mixedMoment B raw41205step1 raw41205step1Labels := by
      have hz : ∀ j, raw41205step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41205step1 = (fun i j => raw41205step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41205step1 raw41205step0; decide +kernel
      have hl : raw41205step1Labels = raw41205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41205step0 raw41205step0Labels permutation80 hz
    mixedMoment B raw41205step1 raw41205step1Labels = mixedMoment B raw41205step2 raw41205step2Labels := by
      have ha : raw41205step2 = (fun i j => raw41205step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41205step2 raw41205step1; decide +kernel
      have hl : raw41205step2Labels = raw41205step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41205step1 raw41205step1Labels permutation13 permutation6
    _ = mixedMoment B node3583 node3583Labels := by rfl

theorem canonical41206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41206 raw41206Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw41206 raw41206Labels = mixedMoment B raw41206step0 raw41206step0Labels := by
      have hz : ∀ j, raw41206 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41206step0 = (fun i j => raw41206 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41206step0 raw41206; decide +kernel
      have hl : raw41206step0Labels = raw41206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41206 raw41206Labels permutation434 hz
    mixedMoment B raw41206step0 raw41206step0Labels = mixedMoment B raw41206step1 raw41206step1Labels := by
      have hz : ∀ j, raw41206step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41206step1 = (fun i j => raw41206step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41206step1 raw41206step0; decide +kernel
      have hl : raw41206step1Labels = raw41206step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41206step0 raw41206step0Labels permutation80 hz
    mixedMoment B raw41206step1 raw41206step1Labels = mixedMoment B raw41206step2 raw41206step2Labels := by
      have ha : raw41206step2 = (fun i j => raw41206step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41206step2 raw41206step1; decide +kernel
      have hl : raw41206step2Labels = raw41206step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41206step1 raw41206step1Labels permutation12 permutation6
    _ = mixedMoment B node3397 node3397Labels := by rfl

theorem canonical41207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41207 raw41207Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw41207 raw41207Labels = mixedMoment B raw41207step0 raw41207step0Labels := by
      have hz : ∀ j, raw41207 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41207step0 = (fun i j => raw41207 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41207step0 raw41207; decide +kernel
      have hl : raw41207step0Labels = raw41207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41207 raw41207Labels permutation434 hz
    mixedMoment B raw41207step0 raw41207step0Labels = mixedMoment B raw41207step1 raw41207step1Labels := by
      have hz : ∀ j, raw41207step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41207step1 = (fun i j => raw41207step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41207step1 raw41207step0; decide +kernel
      have hl : raw41207step1Labels = raw41207step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41207step0 raw41207step0Labels permutation80 hz
    mixedMoment B raw41207step1 raw41207step1Labels = mixedMoment B raw41207step2 raw41207step2Labels := by
      have ha : raw41207step2 = (fun i j => raw41207step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41207step2 raw41207step1; decide +kernel
      have hl : raw41207step2Labels = raw41207step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41207step1 raw41207step1Labels permutation11 permutation6
    _ = mixedMoment B node3548 node3548Labels := by rfl

theorem canonical41208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41208 raw41208Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw41208 raw41208Labels = mixedMoment B raw41208step0 raw41208step0Labels := by
      have hz : ∀ j, raw41208 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41208step0 = (fun i j => raw41208 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41208step0 raw41208; decide +kernel
      have hl : raw41208step0Labels = raw41208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41208 raw41208Labels permutation434 hz
    mixedMoment B raw41208step0 raw41208step0Labels = mixedMoment B raw41208step1 raw41208step1Labels := by
      have hz : ∀ j, raw41208step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41208step1 = (fun i j => raw41208step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41208step1 raw41208step0; decide +kernel
      have hl : raw41208step1Labels = raw41208step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41208step0 raw41208step0Labels permutation80 hz
    mixedMoment B raw41208step1 raw41208step1Labels = mixedMoment B raw41208step2 raw41208step2Labels := by
      have ha : raw41208step2 = (fun i j => raw41208step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41208step2 raw41208step1; decide +kernel
      have hl : raw41208step2Labels = raw41208step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41208step1 raw41208step1Labels permutation11 permutation6
    _ = mixedMoment B node3623 node3623Labels := by rfl

theorem canonical41209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41209 raw41209Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw41209 raw41209Labels = mixedMoment B raw41209step0 raw41209step0Labels := by
      have hz : ∀ j, raw41209 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41209step0 = (fun i j => raw41209 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41209step0 raw41209; decide +kernel
      have hl : raw41209step0Labels = raw41209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41209 raw41209Labels permutation346 hz
    mixedMoment B raw41209step0 raw41209step0Labels = mixedMoment B raw41209step1 raw41209step1Labels := by
      have ha : raw41209step1 = (fun i j => raw41209step0 (permutation53 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41209step1 raw41209step0; decide +kernel
      have hl : raw41209step1Labels = raw41209step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41209step0 raw41209step0Labels permutation53 permutation6
    _ = mixedMoment B node3394 node3394Labels := by rfl

theorem canonical41210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41210 raw41210Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw41210 raw41210Labels = mixedMoment B raw41210step0 raw41210step0Labels := by
      have hz : ∀ j, raw41210 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41210step0 = (fun i j => raw41210 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41210step0 raw41210; decide +kernel
      have hl : raw41210step0Labels = raw41210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41210 raw41210Labels permutation346 hz
    mixedMoment B raw41210step0 raw41210step0Labels = mixedMoment B raw41210step1 raw41210step1Labels := by
      have ha : raw41210step1 = (fun i j => raw41210step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41210step1 raw41210step0; decide +kernel
      have hl : raw41210step1Labels = raw41210step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41210step0 raw41210step0Labels permutation49 permutation6
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical41211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41211 raw41211Labels = mixedMoment B node3496 node3496Labels := by
  calc
    mixedMoment B raw41211 raw41211Labels = mixedMoment B raw41211step0 raw41211step0Labels := by
      have ha : raw41211step0 = (fun i j => raw41211 (permutation243 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41211step0 raw41211; decide +kernel
      have hl : raw41211step0Labels = raw41211Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41211 raw41211Labels permutation243 permutation6
    _ = mixedMoment B node3496 node3496Labels := by rfl

theorem canonical41212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41212 raw41212Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw41212 raw41212Labels = mixedMoment B raw41212step0 raw41212step0Labels := by
      have hz : ∀ j, raw41212 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41212step0 = (fun i j => raw41212 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41212step0 raw41212; decide +kernel
      have hl : raw41212step0Labels = raw41212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41212 raw41212Labels permutation520 hz
    mixedMoment B raw41212step0 raw41212step0Labels = mixedMoment B raw41212step1 raw41212step1Labels := by
      have hz : ∀ j, raw41212step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41212step1 = (fun i j => raw41212step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41212step1 raw41212step0; decide +kernel
      have hl : raw41212step1Labels = raw41212step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41212step0 raw41212step0Labels permutation104 hz
    mixedMoment B raw41212step1 raw41212step1Labels = mixedMoment B raw41212step2 raw41212step2Labels := by
      have hz : ∀ j, raw41212step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41212step2 = (fun i j => raw41212step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41212step2 raw41212step1; decide +kernel
      have hl : raw41212step2Labels = raw41212step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41212step1 raw41212step1Labels permutation20 hz
    mixedMoment B raw41212step2 raw41212step2Labels = mixedMoment B raw41212step3 raw41212step3Labels := by
      have ha : raw41212step3 = (fun i j => raw41212step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41212step3 raw41212step2; decide +kernel
      have hl : raw41212step3Labels = raw41212step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41212step2 raw41212step2Labels permutation5 permutation6
    mixedMoment B raw41212step3 raw41212step3Labels = mixedMoment B raw41212step4 raw41212step4Labels := by
      have ha : raw41212step4 = -raw41212step3 := by apply Matrix.ext; change ∀ i j, raw41212step4 i j = -(raw41212step3 i j); unfold raw41212step4 raw41212step3; decide +kernel
      have hl : raw41212step4Labels = raw41212step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2783 node2783Labels := by rfl

theorem canonical41213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41213 raw41213Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw41213 raw41213Labels = mixedMoment B raw41213step0 raw41213step0Labels := by
      have hz : ∀ j, raw41213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41213step0 = (fun i j => raw41213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41213step0 raw41213; decide +kernel
      have hl : raw41213step0Labels = raw41213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41213 raw41213Labels permutation434 hz
    mixedMoment B raw41213step0 raw41213step0Labels = mixedMoment B raw41213step1 raw41213step1Labels := by
      have hz : ∀ j, raw41213step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41213step1 = (fun i j => raw41213step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41213step1 raw41213step0; decide +kernel
      have hl : raw41213step1Labels = raw41213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41213step0 raw41213step0Labels permutation80 hz
    mixedMoment B raw41213step1 raw41213step1Labels = mixedMoment B raw41213step2 raw41213step2Labels := by
      have ha : raw41213step2 = (fun i j => raw41213step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41213step2 raw41213step1; decide +kernel
      have hl : raw41213step2Labels = raw41213step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41213step1 raw41213step1Labels permutation17 permutation6
    mixedMoment B raw41213step2 raw41213step2Labels = mixedMoment B raw41213step3 raw41213step3Labels := by
      have ha : raw41213step3 = -raw41213step2 := by apply Matrix.ext; change ∀ i j, raw41213step3 i j = -(raw41213step2 i j); unfold raw41213step3 raw41213step2; decide +kernel
      have hl : raw41213step3Labels = raw41213step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2522 node2522Labels := by rfl

theorem canonical41214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41214 raw41214Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw41214 raw41214Labels = mixedMoment B raw41214step0 raw41214step0Labels := by
      have hz : ∀ j, raw41214 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41214step0 = (fun i j => raw41214 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41214step0 raw41214; decide +kernel
      have hl : raw41214step0Labels = raw41214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41214 raw41214Labels permutation434 hz
    mixedMoment B raw41214step0 raw41214step0Labels = mixedMoment B raw41214step1 raw41214step1Labels := by
      have hz : ∀ j, raw41214step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41214step1 = (fun i j => raw41214step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41214step1 raw41214step0; decide +kernel
      have hl : raw41214step1Labels = raw41214step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41214step0 raw41214step0Labels permutation80 hz
    mixedMoment B raw41214step1 raw41214step1Labels = mixedMoment B raw41214step2 raw41214step2Labels := by
      have ha : raw41214step2 = (fun i j => raw41214step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41214step2 raw41214step1; decide +kernel
      have hl : raw41214step2Labels = raw41214step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41214step1 raw41214step1Labels permutation19 permutation6
    mixedMoment B raw41214step2 raw41214step2Labels = mixedMoment B raw41214step3 raw41214step3Labels := by
      have ha : raw41214step3 = -raw41214step2 := by apply Matrix.ext; change ∀ i j, raw41214step3 i j = -(raw41214step2 i j); unfold raw41214step3 raw41214step2; decide +kernel
      have hl : raw41214step3Labels = raw41214step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical41215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41215 raw41215Labels = mixedMoment B node1094 node1094Labels := by
  calc
    mixedMoment B raw41215 raw41215Labels = mixedMoment B raw41215step0 raw41215step0Labels := by
      have hz : ∀ j, raw41215 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41215step0 = (fun i j => raw41215 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41215step0 raw41215; decide +kernel
      have hl : raw41215step0Labels = raw41215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41215 raw41215Labels permutation520 hz
    mixedMoment B raw41215step0 raw41215step0Labels = mixedMoment B raw41215step1 raw41215step1Labels := by
      have hz : ∀ j, raw41215step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41215step1 = (fun i j => raw41215step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41215step1 raw41215step0; decide +kernel
      have hl : raw41215step1Labels = raw41215step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41215step0 raw41215step0Labels permutation104 hz
    mixedMoment B raw41215step1 raw41215step1Labels = mixedMoment B raw41215step2 raw41215step2Labels := by
      have hz : ∀ j, raw41215step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41215step2 = (fun i j => raw41215step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41215step2 raw41215step1; decide +kernel
      have hl : raw41215step2Labels = raw41215step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41215step1 raw41215step1Labels permutation20 hz
    mixedMoment B raw41215step2 raw41215step2Labels = mixedMoment B raw41215step3 raw41215step3Labels := by
      have ha : raw41215step3 = (fun i j => raw41215step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41215step3 raw41215step2; decide +kernel
      have hl : raw41215step3Labels = raw41215step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41215step2 raw41215step2Labels permutation5 permutation6
    mixedMoment B raw41215step3 raw41215step3Labels = mixedMoment B raw41215step4 raw41215step4Labels := by
      have ha : raw41215step4 = -raw41215step3 := by apply Matrix.ext; change ∀ i j, raw41215step4 i j = -(raw41215step3 i j); unfold raw41215step4 raw41215step3; decide +kernel
      have hl : raw41215step4Labels = raw41215step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1094 node1094Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical322
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41216 raw41216Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw41216 raw41216Labels = mixedMoment B raw41216step0 raw41216step0Labels := by
      have hz : ∀ j, raw41216 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41216step0 = (fun i j => raw41216 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41216step0 raw41216; decide +kernel
      have hl : raw41216step0Labels = raw41216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41216 raw41216Labels permutation520 hz
    mixedMoment B raw41216step0 raw41216step0Labels = mixedMoment B raw41216step1 raw41216step1Labels := by
      have hz : ∀ j, raw41216step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41216step1 = (fun i j => raw41216step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41216step1 raw41216step0; decide +kernel
      have hl : raw41216step1Labels = raw41216step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41216step0 raw41216step0Labels permutation104 hz
    mixedMoment B raw41216step1 raw41216step1Labels = mixedMoment B raw41216step2 raw41216step2Labels := by
      have ha : raw41216step2 = (fun i j => raw41216step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41216step2 raw41216step1; decide +kernel
      have hl : raw41216step2Labels = raw41216step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41216step1 raw41216step1Labels permutation31 permutation3
    mixedMoment B raw41216step2 raw41216step2Labels = mixedMoment B raw41216step3 raw41216step3Labels := by
      have ha : raw41216step3 = -raw41216step2 := by apply Matrix.ext; change ∀ i j, raw41216step3 i j = -(raw41216step2 i j); unfold raw41216step3 raw41216step2; decide +kernel
      have hl : raw41216step3Labels = raw41216step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical41217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41217 raw41217Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw41217 raw41217Labels = mixedMoment B raw41217step0 raw41217step0Labels := by
      have hz : ∀ j, raw41217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41217step0 = (fun i j => raw41217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41217step0 raw41217; decide +kernel
      have hl : raw41217step0Labels = raw41217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41217 raw41217Labels permutation434 hz
    mixedMoment B raw41217step0 raw41217step0Labels = mixedMoment B raw41217step1 raw41217step1Labels := by
      have ha : raw41217step1 = (fun i j => raw41217step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41217step1 raw41217step0; decide +kernel
      have hl : raw41217step1Labels = raw41217step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41217step0 raw41217step0Labels permutation151 permutation3
    mixedMoment B raw41217step1 raw41217step1Labels = mixedMoment B raw41217step2 raw41217step2Labels := by
      have ha : raw41217step2 = -raw41217step1 := by apply Matrix.ext; change ∀ i j, raw41217step2 i j = -(raw41217step1 i j); unfold raw41217step2 raw41217step1; decide +kernel
      have hl : raw41217step2Labels = raw41217step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical41218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41218 raw41218Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw41218 raw41218Labels = mixedMoment B raw41218step0 raw41218step0Labels := by
      have hz : ∀ j, raw41218 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41218step0 = (fun i j => raw41218 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41218step0 raw41218; decide +kernel
      have hl : raw41218step0Labels = raw41218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41218 raw41218Labels permutation434 hz
    mixedMoment B raw41218step0 raw41218step0Labels = mixedMoment B raw41218step1 raw41218step1Labels := by
      have ha : raw41218step1 = (fun i j => raw41218step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41218step1 raw41218step0; decide +kernel
      have hl : raw41218step1Labels = raw41218step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41218step0 raw41218step0Labels permutation151 permutation3
    mixedMoment B raw41218step1 raw41218step1Labels = mixedMoment B raw41218step2 raw41218step2Labels := by
      have ha : raw41218step2 = -raw41218step1 := by apply Matrix.ext; change ∀ i j, raw41218step2 i j = -(raw41218step1 i j); unfold raw41218step2 raw41218step1; decide +kernel
      have hl : raw41218step2Labels = raw41218step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical41219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41219 raw41219Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw41219 raw41219Labels = mixedMoment B raw41219step0 raw41219step0Labels := by
      have hz : ∀ j, raw41219 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41219step0 = (fun i j => raw41219 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41219step0 raw41219; decide +kernel
      have hl : raw41219step0Labels = raw41219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41219 raw41219Labels permutation434 hz
    mixedMoment B raw41219step0 raw41219step0Labels = mixedMoment B raw41219step1 raw41219step1Labels := by
      have ha : raw41219step1 = (fun i j => raw41219step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41219step1 raw41219step0; decide +kernel
      have hl : raw41219step1Labels = raw41219step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41219step0 raw41219step0Labels permutation151 permutation3
    mixedMoment B raw41219step1 raw41219step1Labels = mixedMoment B raw41219step2 raw41219step2Labels := by
      have ha : raw41219step2 = -raw41219step1 := by apply Matrix.ext; change ∀ i j, raw41219step2 i j = -(raw41219step1 i j); unfold raw41219step2 raw41219step1; decide +kernel
      have hl : raw41219step2Labels = raw41219step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical41220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41220 raw41220Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw41220 raw41220Labels = mixedMoment B raw41220step0 raw41220step0Labels := by
      have hz : ∀ j, raw41220 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41220step0 = (fun i j => raw41220 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41220step0 raw41220; decide +kernel
      have hl : raw41220step0Labels = raw41220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41220 raw41220Labels permutation434 hz
    mixedMoment B raw41220step0 raw41220step0Labels = mixedMoment B raw41220step1 raw41220step1Labels := by
      have ha : raw41220step1 = (fun i j => raw41220step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41220step1 raw41220step0; decide +kernel
      have hl : raw41220step1Labels = raw41220step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41220step0 raw41220step0Labels permutation151 permutation3
    mixedMoment B raw41220step1 raw41220step1Labels = mixedMoment B raw41220step2 raw41220step2Labels := by
      have ha : raw41220step2 = -raw41220step1 := by apply Matrix.ext; change ∀ i j, raw41220step2 i j = -(raw41220step1 i j); unfold raw41220step2 raw41220step1; decide +kernel
      have hl : raw41220step2Labels = raw41220step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical41221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41221 raw41221Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw41221 raw41221Labels = mixedMoment B raw41221step0 raw41221step0Labels := by
      have hz : ∀ j, raw41221 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41221step0 = (fun i j => raw41221 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41221step0 raw41221; decide +kernel
      have hl : raw41221step0Labels = raw41221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41221 raw41221Labels permutation434 hz
    mixedMoment B raw41221step0 raw41221step0Labels = mixedMoment B raw41221step1 raw41221step1Labels := by
      have ha : raw41221step1 = (fun i j => raw41221step0 (permutation118 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41221step1 raw41221step0; decide +kernel
      have hl : raw41221step1Labels = raw41221step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41221step0 raw41221step0Labels permutation118 permutation6
    mixedMoment B raw41221step1 raw41221step1Labels = mixedMoment B raw41221step2 raw41221step2Labels := by
      have ha : raw41221step2 = -raw41221step1 := by apply Matrix.ext; change ∀ i j, raw41221step2 i j = -(raw41221step1 i j); unfold raw41221step2 raw41221step1; decide +kernel
      have hl : raw41221step2Labels = raw41221step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3535 node3535Labels := by rfl

theorem canonical41222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41222 raw41222Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw41222 raw41222Labels = mixedMoment B raw41222step0 raw41222step0Labels := by
      have ha : raw41222step0 = (fun i j => raw41222 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41222step0 raw41222; decide +kernel
      have hl : raw41222step0Labels = raw41222Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41222 raw41222Labels permutation664 permutation3
    mixedMoment B raw41222step0 raw41222step0Labels = mixedMoment B raw41222step1 raw41222step1Labels := by
      have ha : raw41222step1 = -raw41222step0 := by apply Matrix.ext; change ∀ i j, raw41222step1 i j = -(raw41222step0 i j); unfold raw41222step1 raw41222step0; decide +kernel
      have hl : raw41222step1Labels = raw41222step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3074 node3074Labels := by rfl

theorem canonical41223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41223 raw41223Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw41223 raw41223Labels = mixedMoment B raw41223step0 raw41223step0Labels := by
      have ha : raw41223step0 = (fun i j => raw41223 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41223step0 raw41223; decide +kernel
      have hl : raw41223step0Labels = raw41223Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41223 raw41223Labels permutation688 permutation3
    mixedMoment B raw41223step0 raw41223step0Labels = mixedMoment B raw41223step1 raw41223step1Labels := by
      have ha : raw41223step1 = -raw41223step0 := by apply Matrix.ext; change ∀ i j, raw41223step1 i j = -(raw41223step0 i j); unfold raw41223step1 raw41223step0; decide +kernel
      have hl : raw41223step1Labels = raw41223step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical41224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41224 raw41224Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw41224 raw41224Labels = mixedMoment B raw41224step0 raw41224step0Labels := by
      have ha : raw41224step0 = (fun i j => raw41224 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41224step0 raw41224; decide +kernel
      have hl : raw41224step0Labels = raw41224Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41224 raw41224Labels permutation688 permutation3
    mixedMoment B raw41224step0 raw41224step0Labels = mixedMoment B raw41224step1 raw41224step1Labels := by
      have ha : raw41224step1 = -raw41224step0 := by apply Matrix.ext; change ∀ i j, raw41224step1 i j = -(raw41224step0 i j); unfold raw41224step1 raw41224step0; decide +kernel
      have hl : raw41224step1Labels = raw41224step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4024 node4024Labels := by rfl

theorem canonical41225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41225 raw41225Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw41225 raw41225Labels = mixedMoment B raw41225step0 raw41225step0Labels := by
      have ha : raw41225step0 = (fun i j => raw41225 (permutation477 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41225step0 raw41225; decide +kernel
      have hl : raw41225step0Labels = raw41225Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41225 raw41225Labels permutation477 permutation6
    mixedMoment B raw41225step0 raw41225step0Labels = mixedMoment B raw41225step1 raw41225step1Labels := by
      have ha : raw41225step1 = -raw41225step0 := by apply Matrix.ext; change ∀ i j, raw41225step1 i j = -(raw41225step0 i j); unfold raw41225step1 raw41225step0; decide +kernel
      have hl : raw41225step1Labels = raw41225step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3839 node3839Labels := by rfl

theorem canonical41226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41226 raw41226Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw41226 raw41226Labels = mixedMoment B raw41226step0 raw41226step0Labels := by
      have hz : ∀ j, raw41226 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41226step0 = (fun i j => raw41226 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41226step0 raw41226; decide +kernel
      have hl : raw41226step0Labels = raw41226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41226 raw41226Labels permutation520 hz
    mixedMoment B raw41226step0 raw41226step0Labels = mixedMoment B raw41226step1 raw41226step1Labels := by
      have hz : ∀ j, raw41226step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41226step1 = (fun i j => raw41226step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41226step1 raw41226step0; decide +kernel
      have hl : raw41226step1Labels = raw41226step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41226step0 raw41226step0Labels permutation104 hz
    mixedMoment B raw41226step1 raw41226step1Labels = mixedMoment B raw41226step2 raw41226step2Labels := by
      have ha : raw41226step2 = (fun i j => raw41226step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41226step2 raw41226step1; decide +kernel
      have hl : raw41226step2Labels = raw41226step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41226step1 raw41226step1Labels permutation31 permutation3
    mixedMoment B raw41226step2 raw41226step2Labels = mixedMoment B raw41226step3 raw41226step3Labels := by
      have ha : raw41226step3 = -raw41226step2 := by apply Matrix.ext; change ∀ i j, raw41226step3 i j = -(raw41226step2 i j); unfold raw41226step3 raw41226step2; decide +kernel
      have hl : raw41226step3Labels = raw41226step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2782 node2782Labels := by rfl

theorem canonical41227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41227 raw41227Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw41227 raw41227Labels = mixedMoment B raw41227step0 raw41227step0Labels := by
      have hz : ∀ j, raw41227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41227step0 = (fun i j => raw41227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41227step0 raw41227; decide +kernel
      have hl : raw41227step0Labels = raw41227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41227 raw41227Labels permutation434 hz
    mixedMoment B raw41227step0 raw41227step0Labels = mixedMoment B raw41227step1 raw41227step1Labels := by
      have ha : raw41227step1 = (fun i j => raw41227step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41227step1 raw41227step0; decide +kernel
      have hl : raw41227step1Labels = raw41227step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41227step0 raw41227step0Labels permutation151 permutation3
    mixedMoment B raw41227step1 raw41227step1Labels = mixedMoment B raw41227step2 raw41227step2Labels := by
      have ha : raw41227step2 = -raw41227step1 := by apply Matrix.ext; change ∀ i j, raw41227step2 i j = -(raw41227step1 i j); unfold raw41227step2 raw41227step1; decide +kernel
      have hl : raw41227step2Labels = raw41227step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3097 node3097Labels := by rfl

theorem canonical41228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41228 raw41228Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw41228 raw41228Labels = mixedMoment B raw41228step0 raw41228step0Labels := by
      have hz : ∀ j, raw41228 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41228step0 = (fun i j => raw41228 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41228step0 raw41228; decide +kernel
      have hl : raw41228step0Labels = raw41228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41228 raw41228Labels permutation434 hz
    mixedMoment B raw41228step0 raw41228step0Labels = mixedMoment B raw41228step1 raw41228step1Labels := by
      have ha : raw41228step1 = (fun i j => raw41228step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41228step1 raw41228step0; decide +kernel
      have hl : raw41228step1Labels = raw41228step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41228step0 raw41228step0Labels permutation151 permutation3
    mixedMoment B raw41228step1 raw41228step1Labels = mixedMoment B raw41228step2 raw41228step2Labels := by
      have ha : raw41228step2 = -raw41228step1 := by apply Matrix.ext; change ∀ i j, raw41228step2 i j = -(raw41228step1 i j); unfold raw41228step2 raw41228step1; decide +kernel
      have hl : raw41228step2Labels = raw41228step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical41229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41229 raw41229Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw41229 raw41229Labels = mixedMoment B raw41229step0 raw41229step0Labels := by
      have hz : ∀ j, raw41229 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41229step0 = (fun i j => raw41229 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41229step0 raw41229; decide +kernel
      have hl : raw41229step0Labels = raw41229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41229 raw41229Labels permutation434 hz
    mixedMoment B raw41229step0 raw41229step0Labels = mixedMoment B raw41229step1 raw41229step1Labels := by
      have ha : raw41229step1 = (fun i j => raw41229step0 (permutation94 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41229step1 raw41229step0; decide +kernel
      have hl : raw41229step1Labels = raw41229step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41229step0 raw41229step0Labels permutation94 permutation6
    mixedMoment B raw41229step1 raw41229step1Labels = mixedMoment B raw41229step2 raw41229step2Labels := by
      have ha : raw41229step2 = -raw41229step1 := by apply Matrix.ext; change ∀ i j, raw41229step2 i j = -(raw41229step1 i j); unfold raw41229step2 raw41229step1; decide +kernel
      have hl : raw41229step2Labels = raw41229step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3959 node3959Labels := by rfl

theorem canonical41230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41230 raw41230Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw41230 raw41230Labels = mixedMoment B raw41230step0 raw41230step0Labels := by
      have ha : raw41230step0 = (fun i j => raw41230 (permutation391 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41230step0 raw41230; decide +kernel
      have hl : raw41230step0Labels = raw41230Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41230 raw41230Labels permutation391 permutation6
    mixedMoment B raw41230step0 raw41230step0Labels = mixedMoment B raw41230step1 raw41230step1Labels := by
      have ha : raw41230step1 = -raw41230step0 := by apply Matrix.ext; change ∀ i j, raw41230step1 i j = -(raw41230step0 i j); unfold raw41230step1 raw41230step0; decide +kernel
      have hl : raw41230step1Labels = raw41230step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3972 node3972Labels := by rfl

theorem canonical41231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41231 raw41231Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw41231 raw41231Labels = mixedMoment B raw41231step0 raw41231step0Labels := by
      have hz : ∀ j, raw41231 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41231step0 = (fun i j => raw41231 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41231step0 raw41231; decide +kernel
      have hl : raw41231step0Labels = raw41231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41231 raw41231Labels permutation520 hz
    mixedMoment B raw41231step0 raw41231step0Labels = mixedMoment B raw41231step1 raw41231step1Labels := by
      have hz : ∀ j, raw41231step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41231step1 = (fun i j => raw41231step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41231step1 raw41231step0; decide +kernel
      have hl : raw41231step1Labels = raw41231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41231step0 raw41231step0Labels permutation104 hz
    mixedMoment B raw41231step1 raw41231step1Labels = mixedMoment B raw41231step2 raw41231step2Labels := by
      have ha : raw41231step2 = (fun i j => raw41231step1 (permutation22 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41231step2 raw41231step1; decide +kernel
      have hl : raw41231step2Labels = raw41231step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41231step1 raw41231step1Labels permutation22 permutation6
    mixedMoment B raw41231step2 raw41231step2Labels = mixedMoment B raw41231step3 raw41231step3Labels := by
      have ha : raw41231step3 = -raw41231step2 := by apply Matrix.ext; change ∀ i j, raw41231step3 i j = -(raw41231step2 i j); unfold raw41231step3 raw41231step2; decide +kernel
      have hl : raw41231step3Labels = raw41231step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2769 node2769Labels := by rfl

theorem canonical41232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41232 raw41232Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw41232 raw41232Labels = mixedMoment B raw41232step0 raw41232step0Labels := by
      have hz : ∀ j, raw41232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41232step0 = (fun i j => raw41232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41232step0 raw41232; decide +kernel
      have hl : raw41232step0Labels = raw41232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41232 raw41232Labels permutation434 hz
    mixedMoment B raw41232step0 raw41232step0Labels = mixedMoment B raw41232step1 raw41232step1Labels := by
      have ha : raw41232step1 = (fun i j => raw41232step0 (permutation94 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41232step1 raw41232step0; decide +kernel
      have hl : raw41232step1Labels = raw41232step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41232step0 raw41232step0Labels permutation94 permutation6
    mixedMoment B raw41232step1 raw41232step1Labels = mixedMoment B raw41232step2 raw41232step2Labels := by
      have ha : raw41232step2 = -raw41232step1 := by apply Matrix.ext; change ∀ i j, raw41232step2 i j = -(raw41232step1 i j); unfold raw41232step2 raw41232step1; decide +kernel
      have hl : raw41232step2Labels = raw41232step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2724 node2724Labels := by rfl

theorem canonical41233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41233 raw41233Labels = mixedMoment B node3908 node3908Labels := by
  calc
    mixedMoment B raw41233 raw41233Labels = mixedMoment B raw41233step0 raw41233step0Labels := by
      have hz : ∀ j, raw41233 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41233step0 = (fun i j => raw41233 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41233step0 raw41233; decide +kernel
      have hl : raw41233step0Labels = raw41233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41233 raw41233Labels permutation434 hz
    mixedMoment B raw41233step0 raw41233step0Labels = mixedMoment B raw41233step1 raw41233step1Labels := by
      have hz : ∀ j, raw41233step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41233step1 = (fun i j => raw41233step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41233step1 raw41233step0; decide +kernel
      have hl : raw41233step1Labels = raw41233step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41233step0 raw41233step0Labels permutation80 hz
    mixedMoment B raw41233step1 raw41233step1Labels = mixedMoment B raw41233step2 raw41233step2Labels := by
      have ha : raw41233step2 = (fun i j => raw41233step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41233step2 raw41233step1; decide +kernel
      have hl : raw41233step2Labels = raw41233step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41233step1 raw41233step1Labels permutation31 permutation3
    mixedMoment B raw41233step2 raw41233step2Labels = mixedMoment B raw41233step3 raw41233step3Labels := by
      have ha : raw41233step3 = -raw41233step2 := by apply Matrix.ext; change ∀ i j, raw41233step3 i j = -(raw41233step2 i j); unfold raw41233step3 raw41233step2; decide +kernel
      have hl : raw41233step3Labels = raw41233step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3908 node3908Labels := by rfl

theorem canonical41234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41234 raw41234Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw41234 raw41234Labels = mixedMoment B raw41234step0 raw41234step0Labels := by
      have hz : ∀ j, raw41234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41234step0 = (fun i j => raw41234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41234step0 raw41234; decide +kernel
      have hl : raw41234step0Labels = raw41234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41234 raw41234Labels permutation434 hz
    mixedMoment B raw41234step0 raw41234step0Labels = mixedMoment B raw41234step1 raw41234step1Labels := by
      have hz : ∀ j, raw41234step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41234step1 = (fun i j => raw41234step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41234step1 raw41234step0; decide +kernel
      have hl : raw41234step1Labels = raw41234step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41234step0 raw41234step0Labels permutation80 hz
    mixedMoment B raw41234step1 raw41234step1Labels = mixedMoment B raw41234step2 raw41234step2Labels := by
      have ha : raw41234step2 = (fun i j => raw41234step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41234step2 raw41234step1; decide +kernel
      have hl : raw41234step2Labels = raw41234step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41234step1 raw41234step1Labels permutation23 permutation6
    mixedMoment B raw41234step2 raw41234step2Labels = mixedMoment B raw41234step3 raw41234step3Labels := by
      have ha : raw41234step3 = -raw41234step2 := by apply Matrix.ext; change ∀ i j, raw41234step3 i j = -(raw41234step2 i j); unfold raw41234step3 raw41234step2; decide +kernel
      have hl : raw41234step3Labels = raw41234step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3913 node3913Labels := by rfl

theorem canonical41235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41235 raw41235Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw41235 raw41235Labels = mixedMoment B raw41235step0 raw41235step0Labels := by
      have hz : ∀ j, raw41235 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41235step0 = (fun i j => raw41235 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41235step0 raw41235; decide +kernel
      have hl : raw41235step0Labels = raw41235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41235 raw41235Labels permutation434 hz
    mixedMoment B raw41235step0 raw41235step0Labels = mixedMoment B raw41235step1 raw41235step1Labels := by
      have hz : ∀ j, raw41235step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41235step1 = (fun i j => raw41235step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41235step1 raw41235step0; decide +kernel
      have hl : raw41235step1Labels = raw41235step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41235step0 raw41235step0Labels permutation80 hz
    mixedMoment B raw41235step1 raw41235step1Labels = mixedMoment B raw41235step2 raw41235step2Labels := by
      have ha : raw41235step2 = (fun i j => raw41235step1 (permutation22 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41235step2 raw41235step1; decide +kernel
      have hl : raw41235step2Labels = raw41235step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41235step1 raw41235step1Labels permutation22 permutation6
    mixedMoment B raw41235step2 raw41235step2Labels = mixedMoment B raw41235step3 raw41235step3Labels := by
      have ha : raw41235step3 = -raw41235step2 := by apply Matrix.ext; change ∀ i j, raw41235step3 i j = -(raw41235step2 i j); unfold raw41235step3 raw41235step2; decide +kernel
      have hl : raw41235step3Labels = raw41235step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical41236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41236 raw41236Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw41236 raw41236Labels = mixedMoment B raw41236step0 raw41236step0Labels := by
      have hz : ∀ j, raw41236 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41236step0 = (fun i j => raw41236 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41236step0 raw41236; decide +kernel
      have hl : raw41236step0Labels = raw41236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41236 raw41236Labels permutation434 hz
    mixedMoment B raw41236step0 raw41236step0Labels = mixedMoment B raw41236step1 raw41236step1Labels := by
      have hz : ∀ j, raw41236step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41236step1 = (fun i j => raw41236step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41236step1 raw41236step0; decide +kernel
      have hl : raw41236step1Labels = raw41236step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41236step0 raw41236step0Labels permutation80 hz
    mixedMoment B raw41236step1 raw41236step1Labels = mixedMoment B raw41236step2 raw41236step2Labels := by
      have ha : raw41236step2 = (fun i j => raw41236step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41236step2 raw41236step1; decide +kernel
      have hl : raw41236step2Labels = raw41236step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41236step1 raw41236step1Labels permutation29 permutation6
    mixedMoment B raw41236step2 raw41236step2Labels = mixedMoment B raw41236step3 raw41236step3Labels := by
      have ha : raw41236step3 = -raw41236step2 := by apply Matrix.ext; change ∀ i j, raw41236step3 i j = -(raw41236step2 i j); unfold raw41236step3 raw41236step2; decide +kernel
      have hl : raw41236step3Labels = raw41236step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3627 node3627Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1792 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1792) =
      Integer.Sparse.eval keyMomentRow1792 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1792).leftCharge (GramAssembly.key 1792).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3583) := by
    have ha : gramCharges (GramAssembly.key 1792).leftCharge (GramAssembly.key 1792).rightCharge = raw41205 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41205Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41205 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1792).leftCharge (GramAssembly.key 1792).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1792, Integer.Sparse.eval]

theorem keyMoment1793 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1793) =
      Integer.Sparse.eval keyMomentRow1793 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1793).leftCharge (GramAssembly.key 1793).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3397) := by
    have ha : gramCharges (GramAssembly.key 1793).leftCharge (GramAssembly.key 1793).rightCharge = raw41206 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41206Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41206 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1793).leftCharge (GramAssembly.key 1793).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1793, Integer.Sparse.eval]

theorem keyMoment1794 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1794) =
      Integer.Sparse.eval keyMomentRow1794 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1794).leftCharge (GramAssembly.key 1794).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3548) := by
    have ha : gramCharges (GramAssembly.key 1794).leftCharge (GramAssembly.key 1794).rightCharge = raw41207 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41207Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41207 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1794).leftCharge (GramAssembly.key 1794).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1794, Integer.Sparse.eval]

theorem keyMoment1795 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1795) =
      Integer.Sparse.eval keyMomentRow1795 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1795).leftCharge (GramAssembly.key 1795).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3623) := by
    have ha : gramCharges (GramAssembly.key 1795).leftCharge (GramAssembly.key 1795).rightCharge = raw41208 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41208Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41208 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1795).leftCharge (GramAssembly.key 1795).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1795, Integer.Sparse.eval]

theorem keyMoment1796 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1796) =
      Integer.Sparse.eval keyMomentRow1796 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1796).leftCharge (GramAssembly.key 1796).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3394) := by
    have ha : gramCharges (GramAssembly.key 1796).leftCharge (GramAssembly.key 1796).rightCharge = raw41209 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41209Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41209 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1796).leftCharge (GramAssembly.key 1796).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1796, Integer.Sparse.eval]

theorem keyMoment1797 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1797) =
      Integer.Sparse.eval keyMomentRow1797 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1797).leftCharge (GramAssembly.key 1797).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3534) := by
    have ha : gramCharges (GramAssembly.key 1797).leftCharge (GramAssembly.key 1797).rightCharge = raw41210 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41210Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41210 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1797).leftCharge (GramAssembly.key 1797).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1797, Integer.Sparse.eval]

theorem keyMoment1798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1798) =
      Integer.Sparse.eval keyMomentRow1798 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1798).leftCharge (GramAssembly.key 1798).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3496) := by
    have ha : gramCharges (GramAssembly.key 1798).leftCharge (GramAssembly.key 1798).rightCharge = raw41211 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41211Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41211 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1798).leftCharge (GramAssembly.key 1798).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1798, Integer.Sparse.eval]

theorem keyMoment1799 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1799) =
      Integer.Sparse.eval keyMomentRow1799 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1799).leftCharge (GramAssembly.key 1799).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2783) := by
    have ha : gramCharges (GramAssembly.key 1799).leftCharge (GramAssembly.key 1799).rightCharge = raw41212 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41212Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41212 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1799).leftCharge (GramAssembly.key 1799).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1799, Integer.Sparse.eval]

theorem keyMoment1800 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1800) =
      Integer.Sparse.eval keyMomentRow1800 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1800).leftCharge (GramAssembly.key 1800).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2522) := by
    have ha : gramCharges (GramAssembly.key 1800).leftCharge (GramAssembly.key 1800).rightCharge = raw41213 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41213Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41213 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1800).leftCharge (GramAssembly.key 1800).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1800, Integer.Sparse.eval]

theorem keyMoment1801 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1801) =
      Integer.Sparse.eval keyMomentRow1801 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1801).leftCharge (GramAssembly.key 1801).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2740) := by
    have ha : gramCharges (GramAssembly.key 1801).leftCharge (GramAssembly.key 1801).rightCharge = raw41214 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41214Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41214 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1801).leftCharge (GramAssembly.key 1801).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1801, Integer.Sparse.eval]

theorem keyMoment1802 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1802) =
      Integer.Sparse.eval keyMomentRow1802 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1802).leftCharge (GramAssembly.key 1802).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1094) := by
    have ha : gramCharges (GramAssembly.key 1802).leftCharge (GramAssembly.key 1802).rightCharge = raw41215 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41215Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41215 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1802).leftCharge (GramAssembly.key 1802).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1802, Integer.Sparse.eval]

theorem keyMoment1803 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1803) =
      Integer.Sparse.eval keyMomentRow1803 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1803).leftCharge (GramAssembly.key 1803).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2291) := by
    have ha : gramCharges (GramAssembly.key 1803).leftCharge (GramAssembly.key 1803).rightCharge = raw41216 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41216Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41216 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1803).leftCharge (GramAssembly.key 1803).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1803, Integer.Sparse.eval]

theorem keyMoment1804 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1804) =
      Integer.Sparse.eval keyMomentRow1804 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1804).leftCharge (GramAssembly.key 1804).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2739) := by
    have ha : gramCharges (GramAssembly.key 1804).leftCharge (GramAssembly.key 1804).rightCharge = raw41217 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41217Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41217 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1804).leftCharge (GramAssembly.key 1804).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1804, Integer.Sparse.eval]

theorem keyMoment1805 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1805) =
      Integer.Sparse.eval keyMomentRow1805 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1805).leftCharge (GramAssembly.key 1805).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3051) := by
    have ha : gramCharges (GramAssembly.key 1805).leftCharge (GramAssembly.key 1805).rightCharge = raw41218 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41218Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41218 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1805).leftCharge (GramAssembly.key 1805).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1805, Integer.Sparse.eval]

theorem keyMoment1806 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1806) =
      Integer.Sparse.eval keyMomentRow1806 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1806).leftCharge (GramAssembly.key 1806).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3816) := by
    have ha : gramCharges (GramAssembly.key 1806).leftCharge (GramAssembly.key 1806).rightCharge = raw41219 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41219Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41219 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1806).leftCharge (GramAssembly.key 1806).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1806, Integer.Sparse.eval]

theorem keyMoment1807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1807) =
      Integer.Sparse.eval keyMomentRow1807 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1807).leftCharge (GramAssembly.key 1807).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3961) := by
    have ha : gramCharges (GramAssembly.key 1807).leftCharge (GramAssembly.key 1807).rightCharge = raw41220 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41220Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41220 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1807).leftCharge (GramAssembly.key 1807).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1807, Integer.Sparse.eval]

theorem keyMoment1808 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1808) =
      Integer.Sparse.eval keyMomentRow1808 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1808).leftCharge (GramAssembly.key 1808).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3535) := by
    have ha : gramCharges (GramAssembly.key 1808).leftCharge (GramAssembly.key 1808).rightCharge = raw41221 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41221Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41221 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1808).leftCharge (GramAssembly.key 1808).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1808, Integer.Sparse.eval]

theorem keyMoment1809 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1809) =
      Integer.Sparse.eval keyMomentRow1809 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1809).leftCharge (GramAssembly.key 1809).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3074) := by
    have ha : gramCharges (GramAssembly.key 1809).leftCharge (GramAssembly.key 1809).rightCharge = raw41222 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41222Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41222 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1809).leftCharge (GramAssembly.key 1809).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1809, Integer.Sparse.eval]

theorem keyMoment1810 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1810) =
      Integer.Sparse.eval keyMomentRow1810 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1810).leftCharge (GramAssembly.key 1810).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3974) := by
    have ha : gramCharges (GramAssembly.key 1810).leftCharge (GramAssembly.key 1810).rightCharge = raw41223 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41223Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41223 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1810).leftCharge (GramAssembly.key 1810).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1810, Integer.Sparse.eval]

theorem keyMoment1811 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1811) =
      Integer.Sparse.eval keyMomentRow1811 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1811).leftCharge (GramAssembly.key 1811).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4024) := by
    have ha : gramCharges (GramAssembly.key 1811).leftCharge (GramAssembly.key 1811).rightCharge = raw41224 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41224Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41224 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1811).leftCharge (GramAssembly.key 1811).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1811, Integer.Sparse.eval]

theorem keyMoment1812 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1812) =
      Integer.Sparse.eval keyMomentRow1812 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1812).leftCharge (GramAssembly.key 1812).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3839) := by
    have ha : gramCharges (GramAssembly.key 1812).leftCharge (GramAssembly.key 1812).rightCharge = raw41225 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41225Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41225 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1812).leftCharge (GramAssembly.key 1812).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1812, Integer.Sparse.eval]

theorem keyMoment1813 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1813) =
      Integer.Sparse.eval keyMomentRow1813 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1813).leftCharge (GramAssembly.key 1813).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2782) := by
    have ha : gramCharges (GramAssembly.key 1813).leftCharge (GramAssembly.key 1813).rightCharge = raw41226 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41226Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41226 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1813).leftCharge (GramAssembly.key 1813).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1813, Integer.Sparse.eval]

theorem keyMoment1814 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1814) =
      Integer.Sparse.eval keyMomentRow1814 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1814).leftCharge (GramAssembly.key 1814).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3097) := by
    have ha : gramCharges (GramAssembly.key 1814).leftCharge (GramAssembly.key 1814).rightCharge = raw41227 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41227Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41227 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1814).leftCharge (GramAssembly.key 1814).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1814, Integer.Sparse.eval]

theorem keyMoment1815 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1815) =
      Integer.Sparse.eval keyMomentRow1815 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1815).leftCharge (GramAssembly.key 1815).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3983) := by
    have ha : gramCharges (GramAssembly.key 1815).leftCharge (GramAssembly.key 1815).rightCharge = raw41228 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41228Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41228 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1815).leftCharge (GramAssembly.key 1815).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1815, Integer.Sparse.eval]

theorem keyMoment1816 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1816) =
      Integer.Sparse.eval keyMomentRow1816 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1816).leftCharge (GramAssembly.key 1816).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3959) := by
    have ha : gramCharges (GramAssembly.key 1816).leftCharge (GramAssembly.key 1816).rightCharge = raw41229 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41229Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41229 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1816).leftCharge (GramAssembly.key 1816).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1816, Integer.Sparse.eval]

theorem keyMoment1817 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1817) =
      Integer.Sparse.eval keyMomentRow1817 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1817).leftCharge (GramAssembly.key 1817).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3972) := by
    have ha : gramCharges (GramAssembly.key 1817).leftCharge (GramAssembly.key 1817).rightCharge = raw41230 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41230Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41230 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1817).leftCharge (GramAssembly.key 1817).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1817, Integer.Sparse.eval]

theorem keyMoment1818 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1818) =
      Integer.Sparse.eval keyMomentRow1818 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1818).leftCharge (GramAssembly.key 1818).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2769) := by
    have ha : gramCharges (GramAssembly.key 1818).leftCharge (GramAssembly.key 1818).rightCharge = raw41231 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41231Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41231 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1818).leftCharge (GramAssembly.key 1818).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1818, Integer.Sparse.eval]

theorem keyMoment1819 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1819) =
      Integer.Sparse.eval keyMomentRow1819 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1819).leftCharge (GramAssembly.key 1819).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2724) := by
    have ha : gramCharges (GramAssembly.key 1819).leftCharge (GramAssembly.key 1819).rightCharge = raw41232 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41232Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41232 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1819).leftCharge (GramAssembly.key 1819).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1819, Integer.Sparse.eval]

theorem keyMoment1820 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1820) =
      Integer.Sparse.eval keyMomentRow1820 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1820).leftCharge (GramAssembly.key 1820).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3908) := by
    have ha : gramCharges (GramAssembly.key 1820).leftCharge (GramAssembly.key 1820).rightCharge = raw41233 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41233Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41233 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1820).leftCharge (GramAssembly.key 1820).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1820, Integer.Sparse.eval]

theorem keyMoment1821 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1821) =
      Integer.Sparse.eval keyMomentRow1821 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1821).leftCharge (GramAssembly.key 1821).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3913) := by
    have ha : gramCharges (GramAssembly.key 1821).leftCharge (GramAssembly.key 1821).rightCharge = raw41234 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41234Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41234 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1821).leftCharge (GramAssembly.key 1821).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1821, Integer.Sparse.eval]

theorem keyMoment1822 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1822) =
      Integer.Sparse.eval keyMomentRow1822 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1822).leftCharge (GramAssembly.key 1822).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2266) := by
    have ha : gramCharges (GramAssembly.key 1822).leftCharge (GramAssembly.key 1822).rightCharge = raw41235 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41235Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41235 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1822).leftCharge (GramAssembly.key 1822).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1822, Integer.Sparse.eval]

theorem keyMoment1823 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1823) =
      Integer.Sparse.eval keyMomentRow1823 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1823).leftCharge (GramAssembly.key 1823).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3627) := by
    have ha : gramCharges (GramAssembly.key 1823).leftCharge (GramAssembly.key 1823).rightCharge = raw41236 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41236Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41236 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1823).leftCharge (GramAssembly.key 1823).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1823, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1792 : keyMomentRows (1792 : Fin 2886) =
    keyMomentRow1792 := by decide +kernel

theorem keyMomentRowsAt1793 : keyMomentRows (1793 : Fin 2886) =
    keyMomentRow1793 := by decide +kernel

theorem keyMomentRowsAt1794 : keyMomentRows (1794 : Fin 2886) =
    keyMomentRow1794 := by decide +kernel

theorem keyMomentRowsAt1795 : keyMomentRows (1795 : Fin 2886) =
    keyMomentRow1795 := by decide +kernel

theorem keyMomentRowsAt1796 : keyMomentRows (1796 : Fin 2886) =
    keyMomentRow1796 := by decide +kernel

theorem keyMomentRowsAt1797 : keyMomentRows (1797 : Fin 2886) =
    keyMomentRow1797 := by decide +kernel

theorem keyMomentRowsAt1798 : keyMomentRows (1798 : Fin 2886) =
    keyMomentRow1798 := by decide +kernel

theorem keyMomentRowsAt1799 : keyMomentRows (1799 : Fin 2886) =
    keyMomentRow1799 := by decide +kernel

theorem keyMomentRowsAt1800 : keyMomentRows (1800 : Fin 2886) =
    keyMomentRow1800 := by decide +kernel

theorem keyMomentRowsAt1801 : keyMomentRows (1801 : Fin 2886) =
    keyMomentRow1801 := by decide +kernel

theorem keyMomentRowsAt1802 : keyMomentRows (1802 : Fin 2886) =
    keyMomentRow1802 := by decide +kernel

theorem keyMomentRowsAt1803 : keyMomentRows (1803 : Fin 2886) =
    keyMomentRow1803 := by decide +kernel

theorem keyMomentRowsAt1804 : keyMomentRows (1804 : Fin 2886) =
    keyMomentRow1804 := by decide +kernel

theorem keyMomentRowsAt1805 : keyMomentRows (1805 : Fin 2886) =
    keyMomentRow1805 := by decide +kernel

theorem keyMomentRowsAt1806 : keyMomentRows (1806 : Fin 2886) =
    keyMomentRow1806 := by decide +kernel

theorem keyMomentRowsAt1807 : keyMomentRows (1807 : Fin 2886) =
    keyMomentRow1807 := by decide +kernel

theorem keyMomentRowsAt1808 : keyMomentRows (1808 : Fin 2886) =
    keyMomentRow1808 := by decide +kernel

theorem keyMomentRowsAt1809 : keyMomentRows (1809 : Fin 2886) =
    keyMomentRow1809 := by decide +kernel

theorem keyMomentRowsAt1810 : keyMomentRows (1810 : Fin 2886) =
    keyMomentRow1810 := by decide +kernel

theorem keyMomentRowsAt1811 : keyMomentRows (1811 : Fin 2886) =
    keyMomentRow1811 := by decide +kernel

theorem keyMomentRowsAt1812 : keyMomentRows (1812 : Fin 2886) =
    keyMomentRow1812 := by decide +kernel

theorem keyMomentRowsAt1813 : keyMomentRows (1813 : Fin 2886) =
    keyMomentRow1813 := by decide +kernel

theorem keyMomentRowsAt1814 : keyMomentRows (1814 : Fin 2886) =
    keyMomentRow1814 := by decide +kernel

theorem keyMomentRowsAt1815 : keyMomentRows (1815 : Fin 2886) =
    keyMomentRow1815 := by decide +kernel

theorem keyMomentRowsAt1816 : keyMomentRows (1816 : Fin 2886) =
    keyMomentRow1816 := by decide +kernel

theorem keyMomentRowsAt1817 : keyMomentRows (1817 : Fin 2886) =
    keyMomentRow1817 := by decide +kernel

theorem keyMomentRowsAt1818 : keyMomentRows (1818 : Fin 2886) =
    keyMomentRow1818 := by decide +kernel

theorem keyMomentRowsAt1819 : keyMomentRows (1819 : Fin 2886) =
    keyMomentRow1819 := by decide +kernel

theorem keyMomentRowsAt1820 : keyMomentRows (1820 : Fin 2886) =
    keyMomentRow1820 := by decide +kernel

theorem keyMomentRowsAt1821 : keyMomentRows (1821 : Fin 2886) =
    keyMomentRow1821 := by decide +kernel

theorem keyMomentRowsAt1822 : keyMomentRows (1822 : Fin 2886) =
    keyMomentRow1822 := by decide +kernel

theorem keyMomentRowsAt1823 : keyMomentRows (1823 : Fin 2886) =
    keyMomentRow1823 := by decide +kernel

theorem keyMomentChunkSound56_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 56) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1792 ∨ k.val = 1793 ∨ k.val = 1794 ∨ k.val = 1795 ∨ k.val = 1796 ∨ k.val = 1797 ∨ k.val = 1798 ∨ k.val = 1799 ∨ k.val = 1800 ∨ k.val = 1801 ∨ k.val = 1802 ∨ k.val = 1803 ∨ k.val = 1804 ∨ k.val = 1805 ∨ k.val = 1806 ∨ k.val = 1807 ∨ k.val = 1808 ∨ k.val = 1809 ∨ k.val = 1810 ∨ k.val = 1811 ∨ k.val = 1812 ∨ k.val = 1813 ∨ k.val = 1814 ∨ k.val = 1815 ∨ k.val = 1816 ∨ k.val = 1817 ∨ k.val = 1818 ∨ k.val = 1819 ∨ k.val = 1820 ∨ k.val = 1821 ∨ k.val = 1822 ∨ k.val = 1823 := by omega
  rcases heq with h1792 | h1793 | h1794 | h1795 | h1796 | h1797 | h1798 | h1799 | h1800 | h1801 | h1802 | h1803 | h1804 | h1805 | h1806 | h1807 | h1808 | h1809 | h1810 | h1811 | h1812 | h1813 | h1814 | h1815 | h1816 | h1817 | h1818 | h1819 | h1820 | h1821 | h1822 | h1823
  · have he : k = (1792 : Fin 2886) := Fin.ext h1792
    subst k
    rw [keyMomentRowsAt1792]
    exact keyMoment1792 B hB
  · have he : k = (1793 : Fin 2886) := Fin.ext h1793
    subst k
    rw [keyMomentRowsAt1793]
    exact keyMoment1793 B hB
  · have he : k = (1794 : Fin 2886) := Fin.ext h1794
    subst k
    rw [keyMomentRowsAt1794]
    exact keyMoment1794 B hB
  · have he : k = (1795 : Fin 2886) := Fin.ext h1795
    subst k
    rw [keyMomentRowsAt1795]
    exact keyMoment1795 B hB
  · have he : k = (1796 : Fin 2886) := Fin.ext h1796
    subst k
    rw [keyMomentRowsAt1796]
    exact keyMoment1796 B hB
  · have he : k = (1797 : Fin 2886) := Fin.ext h1797
    subst k
    rw [keyMomentRowsAt1797]
    exact keyMoment1797 B hB
  · have he : k = (1798 : Fin 2886) := Fin.ext h1798
    subst k
    rw [keyMomentRowsAt1798]
    exact keyMoment1798 B hB
  · have he : k = (1799 : Fin 2886) := Fin.ext h1799
    subst k
    rw [keyMomentRowsAt1799]
    exact keyMoment1799 B hB
  · have he : k = (1800 : Fin 2886) := Fin.ext h1800
    subst k
    rw [keyMomentRowsAt1800]
    exact keyMoment1800 B hB
  · have he : k = (1801 : Fin 2886) := Fin.ext h1801
    subst k
    rw [keyMomentRowsAt1801]
    exact keyMoment1801 B hB
  · have he : k = (1802 : Fin 2886) := Fin.ext h1802
    subst k
    rw [keyMomentRowsAt1802]
    exact keyMoment1802 B hB
  · have he : k = (1803 : Fin 2886) := Fin.ext h1803
    subst k
    rw [keyMomentRowsAt1803]
    exact keyMoment1803 B hB
  · have he : k = (1804 : Fin 2886) := Fin.ext h1804
    subst k
    rw [keyMomentRowsAt1804]
    exact keyMoment1804 B hB
  · have he : k = (1805 : Fin 2886) := Fin.ext h1805
    subst k
    rw [keyMomentRowsAt1805]
    exact keyMoment1805 B hB
  · have he : k = (1806 : Fin 2886) := Fin.ext h1806
    subst k
    rw [keyMomentRowsAt1806]
    exact keyMoment1806 B hB
  · have he : k = (1807 : Fin 2886) := Fin.ext h1807
    subst k
    rw [keyMomentRowsAt1807]
    exact keyMoment1807 B hB
  · have he : k = (1808 : Fin 2886) := Fin.ext h1808
    subst k
    rw [keyMomentRowsAt1808]
    exact keyMoment1808 B hB
  · have he : k = (1809 : Fin 2886) := Fin.ext h1809
    subst k
    rw [keyMomentRowsAt1809]
    exact keyMoment1809 B hB
  · have he : k = (1810 : Fin 2886) := Fin.ext h1810
    subst k
    rw [keyMomentRowsAt1810]
    exact keyMoment1810 B hB
  · have he : k = (1811 : Fin 2886) := Fin.ext h1811
    subst k
    rw [keyMomentRowsAt1811]
    exact keyMoment1811 B hB
  · have he : k = (1812 : Fin 2886) := Fin.ext h1812
    subst k
    rw [keyMomentRowsAt1812]
    exact keyMoment1812 B hB
  · have he : k = (1813 : Fin 2886) := Fin.ext h1813
    subst k
    rw [keyMomentRowsAt1813]
    exact keyMoment1813 B hB
  · have he : k = (1814 : Fin 2886) := Fin.ext h1814
    subst k
    rw [keyMomentRowsAt1814]
    exact keyMoment1814 B hB
  · have he : k = (1815 : Fin 2886) := Fin.ext h1815
    subst k
    rw [keyMomentRowsAt1815]
    exact keyMoment1815 B hB
  · have he : k = (1816 : Fin 2886) := Fin.ext h1816
    subst k
    rw [keyMomentRowsAt1816]
    exact keyMoment1816 B hB
  · have he : k = (1817 : Fin 2886) := Fin.ext h1817
    subst k
    rw [keyMomentRowsAt1817]
    exact keyMoment1817 B hB
  · have he : k = (1818 : Fin 2886) := Fin.ext h1818
    subst k
    rw [keyMomentRowsAt1818]
    exact keyMoment1818 B hB
  · have he : k = (1819 : Fin 2886) := Fin.ext h1819
    subst k
    rw [keyMomentRowsAt1819]
    exact keyMoment1819 B hB
  · have he : k = (1820 : Fin 2886) := Fin.ext h1820
    subst k
    rw [keyMomentRowsAt1820]
    exact keyMoment1820 B hB
  · have he : k = (1821 : Fin 2886) := Fin.ext h1821
    subst k
    rw [keyMomentRowsAt1821]
    exact keyMoment1821 B hB
  · have he : k = (1822 : Fin 2886) := Fin.ext h1822
    subst k
    rw [keyMomentRowsAt1822]
    exact keyMoment1822 B hB
  · have he : k = (1823 : Fin 2886) := Fin.ext h1823
    subst k
    rw [keyMomentRowsAt1823]
    exact keyMoment1823 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound56_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound56_e_oai
