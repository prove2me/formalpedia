-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound4_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:54:37.282548+00:00
-- url     : https://prove2.me/submissions/a43a1833-ab65-43f1-be54-e13c40411b24

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical309
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39578 raw39578Labels = mixedMoment B node154 node154Labels := by
  calc
    mixedMoment B raw39578 raw39578Labels = mixedMoment B raw39578step0 raw39578step0Labels := by
      have hz : ∀ j, raw39578 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39578step0 = (fun i j => raw39578 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39578step0 raw39578; decide +kernel
      have hl : raw39578step0Labels = raw39578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39578 raw39578Labels permutation434 hz
    mixedMoment B raw39578step0 raw39578step0Labels = mixedMoment B raw39578step1 raw39578step1Labels := by
      have hz : ∀ j, raw39578step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39578step1 = (fun i j => raw39578step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39578step1 raw39578step0; decide +kernel
      have hl : raw39578step1Labels = raw39578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39578step0 raw39578step0Labels permutation80 hz
    mixedMoment B raw39578step1 raw39578step1Labels = mixedMoment B raw39578step2 raw39578step2Labels := by
      have hz : ∀ j, raw39578step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39578step2 = (fun i j => raw39578step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39578step2 raw39578step1; decide +kernel
      have hl : raw39578step2Labels = raw39578step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39578step1 raw39578step1Labels permutation14 hz
    mixedMoment B raw39578step2 raw39578step2Labels = mixedMoment B raw39578step3 raw39578step3Labels := by
      have ha : raw39578step3 = (fun i j => raw39578step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39578step3 raw39578step2; decide +kernel
      have hl : raw39578step3Labels = raw39578step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39578step2 raw39578step2Labels permutation7 permutation7
    _ = mixedMoment B node154 node154Labels := by rfl

theorem canonical39579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39579 raw39579Labels = mixedMoment B node41 node41Labels := by
  calc
    mixedMoment B raw39579 raw39579Labels = mixedMoment B raw39579step0 raw39579step0Labels := by
      have hz : ∀ j, raw39579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39579step0 = (fun i j => raw39579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39579step0 raw39579; decide +kernel
      have hl : raw39579step0Labels = raw39579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39579 raw39579Labels permutation434 hz
    mixedMoment B raw39579step0 raw39579step0Labels = mixedMoment B raw39579step1 raw39579step1Labels := by
      have hz : ∀ j, raw39579step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39579step1 = (fun i j => raw39579step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39579step1 raw39579step0; decide +kernel
      have hl : raw39579step1Labels = raw39579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39579step0 raw39579step0Labels permutation80 hz
    mixedMoment B raw39579step1 raw39579step1Labels = mixedMoment B raw39579step2 raw39579step2Labels := by
      have hz : ∀ j, raw39579step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39579step2 = (fun i j => raw39579step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39579step2 raw39579step1; decide +kernel
      have hl : raw39579step2Labels = raw39579step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39579step1 raw39579step1Labels permutation14 hz
    mixedMoment B raw39579step2 raw39579step2Labels = mixedMoment B raw39579step3 raw39579step3Labels := by
      have ha : raw39579step3 = (fun i j => raw39579step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39579step3 raw39579step2; decide +kernel
      have hl : raw39579step3Labels = raw39579step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39579step2 raw39579step2Labels permutation7 permutation6
    _ = mixedMoment B node41 node41Labels := by rfl

theorem canonical39580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39580 raw39580Labels = mixedMoment B node102 node102Labels := by
  calc
    mixedMoment B raw39580 raw39580Labels = mixedMoment B raw39580step0 raw39580step0Labels := by
      have hz : ∀ j, raw39580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39580step0 = (fun i j => raw39580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39580step0 raw39580; decide +kernel
      have hl : raw39580step0Labels = raw39580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39580 raw39580Labels permutation346 hz
    mixedMoment B raw39580step0 raw39580step0Labels = mixedMoment B raw39580step1 raw39580step1Labels := by
      have hz : ∀ j, raw39580step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39580step1 = (fun i j => raw39580step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39580step1 raw39580step0; decide +kernel
      have hl : raw39580step1Labels = raw39580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39580step0 raw39580step0Labels permutation56 hz
    mixedMoment B raw39580step1 raw39580step1Labels = mixedMoment B raw39580step2 raw39580step2Labels := by
      have ha : raw39580step2 = (fun i j => raw39580step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39580step2 raw39580step1; decide +kernel
      have hl : raw39580step2Labels = raw39580step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39580step1 raw39580step1Labels permutation25 permutation6
    _ = mixedMoment B node102 node102Labels := by rfl

theorem canonical39581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39581 raw39581Labels = mixedMoment B node143 node143Labels := by
  calc
    mixedMoment B raw39581 raw39581Labels = mixedMoment B raw39581step0 raw39581step0Labels := by
      have hz : ∀ j, raw39581 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39581step0 = (fun i j => raw39581 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39581step0 raw39581; decide +kernel
      have hl : raw39581step0Labels = raw39581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39581 raw39581Labels permutation346 hz
    mixedMoment B raw39581step0 raw39581step0Labels = mixedMoment B raw39581step1 raw39581step1Labels := by
      have hz : ∀ j, raw39581step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39581step1 = (fun i j => raw39581step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39581step1 raw39581step0; decide +kernel
      have hl : raw39581step1Labels = raw39581step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39581step0 raw39581step0Labels permutation56 hz
    mixedMoment B raw39581step1 raw39581step1Labels = mixedMoment B raw39581step2 raw39581step2Labels := by
      have ha : raw39581step2 = (fun i j => raw39581step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39581step2 raw39581step1; decide +kernel
      have hl : raw39581step2Labels = raw39581step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39581step1 raw39581step1Labels permutation31 permutation7
    _ = mixedMoment B node143 node143Labels := by rfl

theorem canonical39582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39582 raw39582Labels = mixedMoment B node32 node32Labels := by
  calc
    mixedMoment B raw39582 raw39582Labels = mixedMoment B raw39582step0 raw39582step0Labels := by
      have hz : ∀ j, raw39582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39582step0 = (fun i j => raw39582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39582step0 raw39582; decide +kernel
      have hl : raw39582step0Labels = raw39582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39582 raw39582Labels permutation346 hz
    mixedMoment B raw39582step0 raw39582step0Labels = mixedMoment B raw39582step1 raw39582step1Labels := by
      have hz : ∀ j, raw39582step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39582step1 = (fun i j => raw39582step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39582step1 raw39582step0; decide +kernel
      have hl : raw39582step1Labels = raw39582step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39582step0 raw39582step0Labels permutation56 hz
    mixedMoment B raw39582step1 raw39582step1Labels = mixedMoment B raw39582step2 raw39582step2Labels := by
      have ha : raw39582step2 = (fun i j => raw39582step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39582step2 raw39582step1; decide +kernel
      have hl : raw39582step2Labels = raw39582step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39582step1 raw39582step1Labels permutation29 permutation6
    _ = mixedMoment B node32 node32Labels := by rfl

theorem canonical39583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39583 raw39583Labels = mixedMoment B node19 node19Labels := by
  calc
    mixedMoment B raw39583 raw39583Labels = mixedMoment B raw39583step0 raw39583step0Labels := by
      have hz : ∀ j, raw39583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39583step0 = (fun i j => raw39583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39583step0 raw39583; decide +kernel
      have hl : raw39583step0Labels = raw39583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39583 raw39583Labels permutation346 hz
    mixedMoment B raw39583step0 raw39583step0Labels = mixedMoment B raw39583step1 raw39583step1Labels := by
      have hz : ∀ j, raw39583step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39583step1 = (fun i j => raw39583step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39583step1 raw39583step0; decide +kernel
      have hl : raw39583step1Labels = raw39583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39583step0 raw39583step0Labels permutation56 hz
    mixedMoment B raw39583step1 raw39583step1Labels = mixedMoment B raw39583step2 raw39583step2Labels := by
      have ha : raw39583step2 = (fun i j => raw39583step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39583step2 raw39583step1; decide +kernel
      have hl : raw39583step2Labels = raw39583step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39583step1 raw39583step1Labels permutation31 permutation6
    _ = mixedMoment B node19 node19Labels := by rfl

theorem canonical39584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39584 raw39584Labels = mixedMoment B node73 node73Labels := by
  calc
    mixedMoment B raw39584 raw39584Labels = mixedMoment B raw39584step0 raw39584step0Labels := by
      have hz : ∀ j, raw39584 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39584step0 = (fun i j => raw39584 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39584step0 raw39584; decide +kernel
      have hl : raw39584step0Labels = raw39584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39584 raw39584Labels permutation346 hz
    mixedMoment B raw39584step0 raw39584step0Labels = mixedMoment B raw39584step1 raw39584step1Labels := by
      have hz : ∀ j, raw39584step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39584step1 = (fun i j => raw39584step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39584step1 raw39584step0; decide +kernel
      have hl : raw39584step1Labels = raw39584step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39584step0 raw39584step0Labels permutation56 hz
    mixedMoment B raw39584step1 raw39584step1Labels = mixedMoment B raw39584step2 raw39584step2Labels := by
      have ha : raw39584step2 = (fun i j => raw39584step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39584step2 raw39584step1; decide +kernel
      have hl : raw39584step2Labels = raw39584step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39584step1 raw39584step1Labels permutation17 permutation6
    _ = mixedMoment B node73 node73Labels := by rfl

theorem canonical39585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39585 raw39585Labels = mixedMoment B node97 node97Labels := by
  calc
    mixedMoment B raw39585 raw39585Labels = mixedMoment B raw39585step0 raw39585step0Labels := by
      have hz : ∀ j, raw39585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39585step0 = (fun i j => raw39585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39585step0 raw39585; decide +kernel
      have hl : raw39585step0Labels = raw39585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39585 raw39585Labels permutation346 hz
    mixedMoment B raw39585step0 raw39585step0Labels = mixedMoment B raw39585step1 raw39585step1Labels := by
      have hz : ∀ j, raw39585step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39585step1 = (fun i j => raw39585step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39585step1 raw39585step0; decide +kernel
      have hl : raw39585step1Labels = raw39585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39585step0 raw39585step0Labels permutation56 hz
    mixedMoment B raw39585step1 raw39585step1Labels = mixedMoment B raw39585step2 raw39585step2Labels := by
      have ha : raw39585step2 = (fun i j => raw39585step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39585step2 raw39585step1; decide +kernel
      have hl : raw39585step2Labels = raw39585step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39585step1 raw39585step1Labels permutation17 permutation6
    _ = mixedMoment B node97 node97Labels := by rfl

theorem canonical39586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39586 raw39586Labels = mixedMoment B node197 node197Labels := by
  calc
    mixedMoment B raw39586 raw39586Labels = mixedMoment B raw39586step0 raw39586step0Labels := by
      have hz : ∀ j, raw39586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39586step0 = (fun i j => raw39586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39586step0 raw39586; decide +kernel
      have hl : raw39586step0Labels = raw39586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39586 raw39586Labels permutation346 hz
    mixedMoment B raw39586step0 raw39586step0Labels = mixedMoment B raw39586step1 raw39586step1Labels := by
      have hz : ∀ j, raw39586step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39586step1 = (fun i j => raw39586step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39586step1 raw39586step0; decide +kernel
      have hl : raw39586step1Labels = raw39586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39586step0 raw39586step0Labels permutation56 hz
    mixedMoment B raw39586step1 raw39586step1Labels = mixedMoment B raw39586step2 raw39586step2Labels := by
      have ha : raw39586step2 = (fun i j => raw39586step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39586step2 raw39586step1; decide +kernel
      have hl : raw39586step2Labels = raw39586step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39586step1 raw39586step1Labels permutation13 permutation7
    mixedMoment B raw39586step2 raw39586step2Labels = mixedMoment B raw39586step3 raw39586step3Labels := by
      have ha : raw39586step3 = -raw39586step2 := by apply Matrix.ext; change ∀ i j, raw39586step3 i j = -(raw39586step2 i j); unfold raw39586step3 raw39586step2; decide +kernel
      have hl : raw39586step3Labels = raw39586step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node197 node197Labels := by rfl

theorem canonical39587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39587 raw39587Labels = mixedMoment B node249 node249Labels := by
  calc
    mixedMoment B raw39587 raw39587Labels = mixedMoment B raw39587step0 raw39587step0Labels := by
      have hz : ∀ j, raw39587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39587step0 = (fun i j => raw39587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39587step0 raw39587; decide +kernel
      have hl : raw39587step0Labels = raw39587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39587 raw39587Labels permutation346 hz
    mixedMoment B raw39587step0 raw39587step0Labels = mixedMoment B raw39587step1 raw39587step1Labels := by
      have hz : ∀ j, raw39587step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39587step1 = (fun i j => raw39587step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39587step1 raw39587step0; decide +kernel
      have hl : raw39587step1Labels = raw39587step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39587step0 raw39587step0Labels permutation56 hz
    mixedMoment B raw39587step1 raw39587step1Labels = mixedMoment B raw39587step2 raw39587step2Labels := by
      have ha : raw39587step2 = (fun i j => raw39587step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39587step2 raw39587step1; decide +kernel
      have hl : raw39587step2Labels = raw39587step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39587step1 raw39587step1Labels permutation13 permutation7
    mixedMoment B raw39587step2 raw39587step2Labels = mixedMoment B raw39587step3 raw39587step3Labels := by
      have ha : raw39587step3 = -raw39587step2 := by apply Matrix.ext; change ∀ i j, raw39587step3 i j = -(raw39587step2 i j); unfold raw39587step3 raw39587step2; decide +kernel
      have hl : raw39587step3Labels = raw39587step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node249 node249Labels := by rfl

theorem canonical39588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39588 raw39588Labels = mixedMoment B node14 node14Labels := by
  calc
    mixedMoment B raw39588 raw39588Labels = mixedMoment B raw39588step0 raw39588step0Labels := by
      have hz : ∀ j, raw39588 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39588step0 = (fun i j => raw39588 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39588step0 raw39588; decide +kernel
      have hl : raw39588step0Labels = raw39588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39588 raw39588Labels permutation265 hz
    mixedMoment B raw39588step0 raw39588step0Labels = mixedMoment B raw39588step1 raw39588step1Labels := by
      have ha : raw39588step1 = (fun i j => raw39588step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39588step1 raw39588step0; decide +kernel
      have hl : raw39588step1Labels = raw39588step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39588step0 raw39588step0Labels permutation149 permutation6
    _ = mixedMoment B node14 node14Labels := by rfl

theorem canonical39589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39589 raw39589Labels = mixedMoment B node67 node67Labels := by
  calc
    mixedMoment B raw39589 raw39589Labels = mixedMoment B raw39589step0 raw39589step0Labels := by
      have hz : ∀ j, raw39589 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39589step0 = (fun i j => raw39589 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39589step0 raw39589; decide +kernel
      have hl : raw39589step0Labels = raw39589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39589 raw39589Labels permutation265 hz
    mixedMoment B raw39589step0 raw39589step0Labels = mixedMoment B raw39589step1 raw39589step1Labels := by
      have ha : raw39589step1 = (fun i j => raw39589step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39589step1 raw39589step0; decide +kernel
      have hl : raw39589step1Labels = raw39589step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39589step0 raw39589step0Labels permutation95 permutation6
    _ = mixedMoment B node67 node67Labels := by rfl

theorem canonical39590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39590 raw39590Labels = mixedMoment B node87 node87Labels := by
  calc
    mixedMoment B raw39590 raw39590Labels = mixedMoment B raw39590step0 raw39590step0Labels := by
      have hz : ∀ j, raw39590 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39590step0 = (fun i j => raw39590 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39590step0 raw39590; decide +kernel
      have hl : raw39590step0Labels = raw39590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39590 raw39590Labels permutation265 hz
    mixedMoment B raw39590step0 raw39590step0Labels = mixedMoment B raw39590step1 raw39590step1Labels := by
      have ha : raw39590step1 = (fun i j => raw39590step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39590step1 raw39590step0; decide +kernel
      have hl : raw39590step1Labels = raw39590step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39590step0 raw39590step0Labels permutation97 permutation6
    _ = mixedMoment B node87 node87Labels := by rfl

theorem canonical39591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39591 raw39591Labels = mixedMoment B node227 node227Labels := by
  calc
    mixedMoment B raw39591 raw39591Labels = mixedMoment B raw39591step0 raw39591step0Labels := by
      have hz : ∀ j, raw39591 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39591step0 = (fun i j => raw39591 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39591step0 raw39591; decide +kernel
      have hl : raw39591step0Labels = raw39591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39591 raw39591Labels permutation265 hz
    mixedMoment B raw39591step0 raw39591step0Labels = mixedMoment B raw39591step1 raw39591step1Labels := by
      have ha : raw39591step1 = (fun i j => raw39591step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39591step1 raw39591step0; decide +kernel
      have hl : raw39591step1Labels = raw39591step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39591step0 raw39591step0Labels permutation36 permutation7
    mixedMoment B raw39591step1 raw39591step1Labels = mixedMoment B raw39591step2 raw39591step2Labels := by
      have ha : raw39591step2 = -raw39591step1 := by apply Matrix.ext; change ∀ i j, raw39591step2 i j = -(raw39591step1 i j); unfold raw39591step2 raw39591step1; decide +kernel
      have hl : raw39591step2Labels = raw39591step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node227 node227Labels := by rfl

theorem canonical39592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39592 raw39592Labels = mixedMoment B node60 node60Labels := by
  calc
    mixedMoment B raw39592 raw39592Labels = mixedMoment B raw39592step0 raw39592step0Labels := by
      have hz : ∀ j, raw39592 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39592step0 = (fun i j => raw39592 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39592step0 raw39592; decide +kernel
      have hl : raw39592step0Labels = raw39592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39592 raw39592Labels permutation265 hz
    mixedMoment B raw39592step0 raw39592step0Labels = mixedMoment B raw39592step1 raw39592step1Labels := by
      have ha : raw39592step1 = (fun i j => raw39592step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39592step1 raw39592step0; decide +kernel
      have hl : raw39592step1Labels = raw39592step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39592step0 raw39592step0Labels permutation97 permutation6
    _ = mixedMoment B node60 node60Labels := by rfl

theorem canonical39593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39593 raw39593Labels = mixedMoment B node169 node169Labels := by
  calc
    mixedMoment B raw39593 raw39593Labels = mixedMoment B raw39593step0 raw39593step0Labels := by
      have hz : ∀ j, raw39593 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39593step0 = (fun i j => raw39593 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39593step0 raw39593; decide +kernel
      have hl : raw39593step0Labels = raw39593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39593 raw39593Labels permutation265 hz
    mixedMoment B raw39593step0 raw39593step0Labels = mixedMoment B raw39593step1 raw39593step1Labels := by
      have ha : raw39593step1 = (fun i j => raw39593step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39593step1 raw39593step0; decide +kernel
      have hl : raw39593step1Labels = raw39593step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39593step0 raw39593step0Labels permutation37 permutation7
    mixedMoment B raw39593step1 raw39593step1Labels = mixedMoment B raw39593step2 raw39593step2Labels := by
      have ha : raw39593step2 = -raw39593step1 := by apply Matrix.ext; change ∀ i j, raw39593step2 i j = -(raw39593step1 i j); unfold raw39593step2 raw39593step1; decide +kernel
      have hl : raw39593step2Labels = raw39593step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node169 node169Labels := by rfl

theorem canonical39594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39594 raw39594Labels = mixedMoment B node58 node58Labels := by
  calc
    mixedMoment B raw39594 raw39594Labels = mixedMoment B raw39594step0 raw39594step0Labels := by
      have ha : raw39594step0 = (fun i j => raw39594 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39594step0 raw39594; decide +kernel
      have hl : raw39594step0Labels = raw39594Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39594 raw39594Labels permutation502 permutation6
    _ = mixedMoment B node58 node58Labels := by rfl

theorem canonical39595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39595 raw39595Labels = mixedMoment B node102 node102Labels := by
  calc
    mixedMoment B raw39595 raw39595Labels = mixedMoment B raw39595step0 raw39595step0Labels := by
      have hz : ∀ j, raw39595 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39595step0 = (fun i j => raw39595 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39595step0 raw39595; decide +kernel
      have hl : raw39595step0Labels = raw39595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39595 raw39595Labels permutation434 hz
    mixedMoment B raw39595step0 raw39595step0Labels = mixedMoment B raw39595step1 raw39595step1Labels := by
      have hz : ∀ j, raw39595step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39595step1 = (fun i j => raw39595step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39595step1 raw39595step0; decide +kernel
      have hl : raw39595step1Labels = raw39595step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39595step0 raw39595step0Labels permutation80 hz
    mixedMoment B raw39595step1 raw39595step1Labels = mixedMoment B raw39595step2 raw39595step2Labels := by
      have ha : raw39595step2 = (fun i j => raw39595step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39595step2 raw39595step1; decide +kernel
      have hl : raw39595step2Labels = raw39595step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39595step1 raw39595step1Labels permutation13 permutation7
    mixedMoment B raw39595step2 raw39595step2Labels = mixedMoment B raw39595step3 raw39595step3Labels := by
      have ha : raw39595step3 = -raw39595step2 := by apply Matrix.ext; change ∀ i j, raw39595step3 i j = -(raw39595step2 i j); unfold raw39595step3 raw39595step2; decide +kernel
      have hl : raw39595step3Labels = raw39595step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node102 node102Labels := by rfl

theorem canonical39596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39596 raw39596Labels = mixedMoment B node97 node97Labels := by
  calc
    mixedMoment B raw39596 raw39596Labels = mixedMoment B raw39596step0 raw39596step0Labels := by
      have hz : ∀ j, raw39596 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39596step0 = (fun i j => raw39596 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39596step0 raw39596; decide +kernel
      have hl : raw39596step0Labels = raw39596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39596 raw39596Labels permutation434 hz
    mixedMoment B raw39596step0 raw39596step0Labels = mixedMoment B raw39596step1 raw39596step1Labels := by
      have hz : ∀ j, raw39596step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39596step1 = (fun i j => raw39596step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39596step1 raw39596step0; decide +kernel
      have hl : raw39596step1Labels = raw39596step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39596step0 raw39596step0Labels permutation80 hz
    mixedMoment B raw39596step1 raw39596step1Labels = mixedMoment B raw39596step2 raw39596step2Labels := by
      have ha : raw39596step2 = (fun i j => raw39596step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39596step2 raw39596step1; decide +kernel
      have hl : raw39596step2Labels = raw39596step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39596step1 raw39596step1Labels permutation11 permutation7
    mixedMoment B raw39596step2 raw39596step2Labels = mixedMoment B raw39596step3 raw39596step3Labels := by
      have ha : raw39596step3 = -raw39596step2 := by apply Matrix.ext; change ∀ i j, raw39596step3 i j = -(raw39596step2 i j); unfold raw39596step3 raw39596step2; decide +kernel
      have hl : raw39596step3Labels = raw39596step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node97 node97Labels := by rfl

theorem canonical39597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39597 raw39597Labels = mixedMoment B node76 node76Labels := by
  calc
    mixedMoment B raw39597 raw39597Labels = mixedMoment B raw39597step0 raw39597step0Labels := by
      have hz : ∀ j, raw39597 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39597step0 = (fun i j => raw39597 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39597step0 raw39597; decide +kernel
      have hl : raw39597step0Labels = raw39597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39597 raw39597Labels permutation434 hz
    mixedMoment B raw39597step0 raw39597step0Labels = mixedMoment B raw39597step1 raw39597step1Labels := by
      have hz : ∀ j, raw39597step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39597step1 = (fun i j => raw39597step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39597step1 raw39597step0; decide +kernel
      have hl : raw39597step1Labels = raw39597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39597step0 raw39597step0Labels permutation80 hz
    mixedMoment B raw39597step1 raw39597step1Labels = mixedMoment B raw39597step2 raw39597step2Labels := by
      have ha : raw39597step2 = (fun i j => raw39597step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39597step2 raw39597step1; decide +kernel
      have hl : raw39597step2Labels = raw39597step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39597step1 raw39597step1Labels permutation11 permutation7
    mixedMoment B raw39597step2 raw39597step2Labels = mixedMoment B raw39597step3 raw39597step3Labels := by
      have ha : raw39597step3 = -raw39597step2 := by apply Matrix.ext; change ∀ i j, raw39597step3 i j = -(raw39597step2 i j); unfold raw39597step3 raw39597step2; decide +kernel
      have hl : raw39597step3Labels = raw39597step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node76 node76Labels := by rfl

theorem canonical39598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39598 raw39598Labels = mixedMoment B node60 node60Labels := by
  calc
    mixedMoment B raw39598 raw39598Labels = mixedMoment B raw39598step0 raw39598step0Labels := by
      have hz : ∀ j, raw39598 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39598step0 = (fun i j => raw39598 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39598step0 raw39598; decide +kernel
      have hl : raw39598step0Labels = raw39598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39598 raw39598Labels permutation346 hz
    mixedMoment B raw39598step0 raw39598step0Labels = mixedMoment B raw39598step1 raw39598step1Labels := by
      have ha : raw39598step1 = (fun i j => raw39598step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39598step1 raw39598step0; decide +kernel
      have hl : raw39598step1Labels = raw39598step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39598step0 raw39598step0Labels permutation41 permutation7
    mixedMoment B raw39598step1 raw39598step1Labels = mixedMoment B raw39598step2 raw39598step2Labels := by
      have ha : raw39598step2 = -raw39598step1 := by apply Matrix.ext; change ∀ i j, raw39598step2 i j = -(raw39598step1 i j); unfold raw39598step2 raw39598step1; decide +kernel
      have hl : raw39598step2Labels = raw39598step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node60 node60Labels := by rfl

theorem canonical39599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39599 raw39599Labels = mixedMoment B node87 node87Labels := by
  calc
    mixedMoment B raw39599 raw39599Labels = mixedMoment B raw39599step0 raw39599step0Labels := by
      have hz : ∀ j, raw39599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39599step0 = (fun i j => raw39599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39599step0 raw39599; decide +kernel
      have hl : raw39599step0Labels = raw39599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39599 raw39599Labels permutation346 hz
    mixedMoment B raw39599step0 raw39599step0Labels = mixedMoment B raw39599step1 raw39599step1Labels := by
      have ha : raw39599step1 = (fun i j => raw39599step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39599step1 raw39599step0; decide +kernel
      have hl : raw39599step1Labels = raw39599step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39599step0 raw39599step0Labels permutation49 permutation7
    mixedMoment B raw39599step1 raw39599step1Labels = mixedMoment B raw39599step2 raw39599step2Labels := by
      have ha : raw39599step2 = -raw39599step1 := by apply Matrix.ext; change ∀ i j, raw39599step2 i j = -(raw39599step1 i j); unfold raw39599step2 raw39599step1; decide +kernel
      have hl : raw39599step2Labels = raw39599step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node87 node87Labels := by rfl

theorem canonical39600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39600 raw39600Labels = mixedMoment B node58 node58Labels := by
  calc
    mixedMoment B raw39600 raw39600Labels = mixedMoment B raw39600step0 raw39600step0Labels := by
      have ha : raw39600step0 = (fun i j => raw39600 (permutation197 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39600step0 raw39600; decide +kernel
      have hl : raw39600step0Labels = raw39600Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39600 raw39600Labels permutation197 permutation7
    mixedMoment B raw39600step0 raw39600step0Labels = mixedMoment B raw39600step1 raw39600step1Labels := by
      have ha : raw39600step1 = -raw39600step0 := by apply Matrix.ext; change ∀ i j, raw39600step1 i j = -(raw39600step0 i j); unfold raw39600step1 raw39600step0; decide +kernel
      have hl : raw39600step1Labels = raw39600step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node58 node58Labels := by rfl

theorem canonical39601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39601 raw39601Labels = mixedMoment B node101 node101Labels := by
  calc
    mixedMoment B raw39601 raw39601Labels = mixedMoment B raw39601step0 raw39601step0Labels := by
      have hz : ∀ j, raw39601 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39601step0 = (fun i j => raw39601 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39601step0 raw39601; decide +kernel
      have hl : raw39601step0Labels = raw39601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39601 raw39601Labels permutation434 hz
    mixedMoment B raw39601step0 raw39601step0Labels = mixedMoment B raw39601step1 raw39601step1Labels := by
      have ha : raw39601step1 = (fun i j => raw39601step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39601step1 raw39601step0; decide +kernel
      have hl : raw39601step1Labels = raw39601step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39601step0 raw39601step0Labels permutation53 permutation7
    mixedMoment B raw39601step1 raw39601step1Labels = mixedMoment B raw39601step2 raw39601step2Labels := by
      have ha : raw39601step2 = -raw39601step1 := by apply Matrix.ext; change ∀ i j, raw39601step2 i j = -(raw39601step1 i j); unfold raw39601step2 raw39601step1; decide +kernel
      have hl : raw39601step2Labels = raw39601step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node101 node101Labels := by rfl

theorem canonical39602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39602 raw39602Labels = mixedMoment B node74 node74Labels := by
  calc
    mixedMoment B raw39602 raw39602Labels = mixedMoment B raw39602step0 raw39602step0Labels := by
      have hz : ∀ j, raw39602 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39602step0 = (fun i j => raw39602 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39602step0 raw39602; decide +kernel
      have hl : raw39602step0Labels = raw39602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39602 raw39602Labels permutation434 hz
    mixedMoment B raw39602step0 raw39602step0Labels = mixedMoment B raw39602step1 raw39602step1Labels := by
      have ha : raw39602step1 = (fun i j => raw39602step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39602step1 raw39602step0; decide +kernel
      have hl : raw39602step1Labels = raw39602step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39602step0 raw39602step0Labels permutation46 permutation7
    mixedMoment B raw39602step1 raw39602step1Labels = mixedMoment B raw39602step2 raw39602step2Labels := by
      have ha : raw39602step2 = -raw39602step1 := by apply Matrix.ext; change ∀ i j, raw39602step2 i j = -(raw39602step1 i j); unfold raw39602step2 raw39602step1; decide +kernel
      have hl : raw39602step2Labels = raw39602step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node74 node74Labels := by rfl

theorem canonical39603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39603 raw39603Labels = mixedMoment B node103 node103Labels := by
  calc
    mixedMoment B raw39603 raw39603Labels = mixedMoment B raw39603step0 raw39603step0Labels := by
      have hz : ∀ j, raw39603 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39603step0 = (fun i j => raw39603 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39603step0 raw39603; decide +kernel
      have hl : raw39603step0Labels = raw39603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39603 raw39603Labels permutation434 hz
    mixedMoment B raw39603step0 raw39603step0Labels = mixedMoment B raw39603step1 raw39603step1Labels := by
      have hz : ∀ j, raw39603step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39603step1 = (fun i j => raw39603step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39603step1 raw39603step0; decide +kernel
      have hl : raw39603step1Labels = raw39603step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39603step0 raw39603step0Labels permutation80 hz
    mixedMoment B raw39603step1 raw39603step1Labels = mixedMoment B raw39603step2 raw39603step2Labels := by
      have ha : raw39603step2 = (fun i j => raw39603step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39603step2 raw39603step1; decide +kernel
      have hl : raw39603step2Labels = raw39603step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39603step1 raw39603step1Labels permutation12 permutation7
    mixedMoment B raw39603step2 raw39603step2Labels = mixedMoment B raw39603step3 raw39603step3Labels := by
      have ha : raw39603step3 = -raw39603step2 := by apply Matrix.ext; change ∀ i j, raw39603step3 i j = -(raw39603step2 i j); unfold raw39603step3 raw39603step2; decide +kernel
      have hl : raw39603step3Labels = raw39603step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node103 node103Labels := by rfl

theorem canonical39604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39604 raw39604Labels = mixedMoment B node98 node98Labels := by
  calc
    mixedMoment B raw39604 raw39604Labels = mixedMoment B raw39604step0 raw39604step0Labels := by
      have hz : ∀ j, raw39604 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39604step0 = (fun i j => raw39604 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39604step0 raw39604; decide +kernel
      have hl : raw39604step0Labels = raw39604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39604 raw39604Labels permutation434 hz
    mixedMoment B raw39604step0 raw39604step0Labels = mixedMoment B raw39604step1 raw39604step1Labels := by
      have hz : ∀ j, raw39604step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39604step1 = (fun i j => raw39604step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39604step1 raw39604step0; decide +kernel
      have hl : raw39604step1Labels = raw39604step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39604step0 raw39604step0Labels permutation80 hz
    mixedMoment B raw39604step1 raw39604step1Labels = mixedMoment B raw39604step2 raw39604step2Labels := by
      have ha : raw39604step2 = (fun i j => raw39604step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39604step2 raw39604step1; decide +kernel
      have hl : raw39604step2Labels = raw39604step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39604step1 raw39604step1Labels permutation10 permutation7
    mixedMoment B raw39604step2 raw39604step2Labels = mixedMoment B raw39604step3 raw39604step3Labels := by
      have ha : raw39604step3 = -raw39604step2 := by apply Matrix.ext; change ∀ i j, raw39604step3 i j = -(raw39604step2 i j); unfold raw39604step3 raw39604step2; decide +kernel
      have hl : raw39604step3Labels = raw39604step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node98 node98Labels := by rfl

theorem canonical39605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39605 raw39605Labels = mixedMoment B node75 node75Labels := by
  calc
    mixedMoment B raw39605 raw39605Labels = mixedMoment B raw39605step0 raw39605step0Labels := by
      have hz : ∀ j, raw39605 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39605step0 = (fun i j => raw39605 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39605step0 raw39605; decide +kernel
      have hl : raw39605step0Labels = raw39605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39605 raw39605Labels permutation434 hz
    mixedMoment B raw39605step0 raw39605step0Labels = mixedMoment B raw39605step1 raw39605step1Labels := by
      have hz : ∀ j, raw39605step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39605step1 = (fun i j => raw39605step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39605step1 raw39605step0; decide +kernel
      have hl : raw39605step1Labels = raw39605step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39605step0 raw39605step0Labels permutation80 hz
    mixedMoment B raw39605step1 raw39605step1Labels = mixedMoment B raw39605step2 raw39605step2Labels := by
      have ha : raw39605step2 = (fun i j => raw39605step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39605step2 raw39605step1; decide +kernel
      have hl : raw39605step2Labels = raw39605step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39605step1 raw39605step1Labels permutation10 permutation7
    mixedMoment B raw39605step2 raw39605step2Labels = mixedMoment B raw39605step3 raw39605step3Labels := by
      have ha : raw39605step3 = -raw39605step2 := by apply Matrix.ext; change ∀ i j, raw39605step3 i j = -(raw39605step2 i j); unfold raw39605step3 raw39605step2; decide +kernel
      have hl : raw39605step3Labels = raw39605step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node75 node75Labels := by rfl

theorem canonical39606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39606 raw39606Labels = mixedMoment B node91 node91Labels := by
  calc
    mixedMoment B raw39606 raw39606Labels = mixedMoment B raw39606step0 raw39606step0Labels := by
      have ha : raw39606step0 = (fun i j => raw39606 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39606step0 raw39606; decide +kernel
      have hl : raw39606step0Labels = raw39606Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39606 raw39606Labels permutation246 permutation7
    mixedMoment B raw39606step0 raw39606step0Labels = mixedMoment B raw39606step1 raw39606step1Labels := by
      have ha : raw39606step1 = -raw39606step0 := by apply Matrix.ext; change ∀ i j, raw39606step1 i j = -(raw39606step0 i j); unfold raw39606step1 raw39606step0; decide +kernel
      have hl : raw39606step1Labels = raw39606step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node91 node91Labels := by rfl

theorem canonical39607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39607 raw39607Labels = mixedMoment B node5504 node5504Labels := by
  calc
    mixedMoment B raw39607 raw39607Labels = mixedMoment B raw39607step0 raw39607step0Labels := by
      have hz : ∀ j, raw39607 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39607step0 = (fun i j => raw39607 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39607step0 raw39607; decide +kernel
      have hl : raw39607step0Labels = raw39607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39607 raw39607Labels permutation434 hz
    mixedMoment B raw39607step0 raw39607step0Labels = mixedMoment B raw39607step1 raw39607step1Labels := by
      have hz : ∀ j, raw39607step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39607step1 = (fun i j => raw39607step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39607step1 raw39607step0; decide +kernel
      have hl : raw39607step1Labels = raw39607step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39607step0 raw39607step0Labels permutation80 hz
    mixedMoment B raw39607step1 raw39607step1Labels = mixedMoment B raw39607step2 raw39607step2Labels := by
      have ha : raw39607step2 = (fun i j => raw39607step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39607step2 raw39607step1; decide +kernel
      have hl : raw39607step2Labels = raw39607step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39607step1 raw39607step1Labels permutation12 permutation7
    mixedMoment B raw39607step2 raw39607step2Labels = mixedMoment B raw39607step3 raw39607step3Labels := by
      have ha : raw39607step3 = -raw39607step2 := by apply Matrix.ext; change ∀ i j, raw39607step3 i j = -(raw39607step2 i j); unfold raw39607step3 raw39607step2; decide +kernel
      have hl : raw39607step3Labels = raw39607step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5504 node5504Labels := by rfl

theorem canonical39608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39608 raw39608Labels = mixedMoment B node94 node94Labels := by
  calc
    mixedMoment B raw39608 raw39608Labels = mixedMoment B raw39608step0 raw39608step0Labels := by
      have hz : ∀ j, raw39608 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39608step0 = (fun i j => raw39608 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39608step0 raw39608; decide +kernel
      have hl : raw39608step0Labels = raw39608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39608 raw39608Labels permutation434 hz
    mixedMoment B raw39608step0 raw39608step0Labels = mixedMoment B raw39608step1 raw39608step1Labels := by
      have hz : ∀ j, raw39608step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39608step1 = (fun i j => raw39608step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39608step1 raw39608step0; decide +kernel
      have hl : raw39608step1Labels = raw39608step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39608step0 raw39608step0Labels permutation80 hz
    mixedMoment B raw39608step1 raw39608step1Labels = mixedMoment B raw39608step2 raw39608step2Labels := by
      have ha : raw39608step2 = (fun i j => raw39608step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39608step2 raw39608step1; decide +kernel
      have hl : raw39608step2Labels = raw39608step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39608step1 raw39608step1Labels permutation10 permutation7
    mixedMoment B raw39608step2 raw39608step2Labels = mixedMoment B raw39608step3 raw39608step3Labels := by
      have ha : raw39608step3 = -raw39608step2 := by apply Matrix.ext; change ∀ i j, raw39608step3 i j = -(raw39608step2 i j); unfold raw39608step3 raw39608step2; decide +kernel
      have hl : raw39608step3Labels = raw39608step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node94 node94Labels := by rfl

theorem canonical39609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39609 raw39609Labels = mixedMoment B node93 node93Labels := by
  calc
    mixedMoment B raw39609 raw39609Labels = mixedMoment B raw39609step0 raw39609step0Labels := by
      have hz : ∀ j, raw39609 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39609step0 = (fun i j => raw39609 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39609step0 raw39609; decide +kernel
      have hl : raw39609step0Labels = raw39609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39609 raw39609Labels permutation346 hz
    mixedMoment B raw39609step0 raw39609step0Labels = mixedMoment B raw39609step1 raw39609step1Labels := by
      have ha : raw39609step1 = (fun i j => raw39609step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39609step1 raw39609step0; decide +kernel
      have hl : raw39609step1Labels = raw39609step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39609step0 raw39609step0Labels permutation51 permutation7
    mixedMoment B raw39609step1 raw39609step1Labels = mixedMoment B raw39609step2 raw39609step2Labels := by
      have ha : raw39609step2 = -raw39609step1 := by apply Matrix.ext; change ∀ i j, raw39609step2 i j = -(raw39609step1 i j); unfold raw39609step2 raw39609step1; decide +kernel
      have hl : raw39609step2Labels = raw39609step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node93 node93Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment128 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 128) =
      Integer.Sparse.eval keyMomentRow128 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 128).leftCharge (GramAssembly.key 128).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 154) := by
    have ha : gramCharges (GramAssembly.key 128).leftCharge (GramAssembly.key 128).rightCharge = raw39578 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39578Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39578 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 128).leftCharge (GramAssembly.key 128).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow128, Integer.Sparse.eval]

theorem keyMoment129 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 129) =
      Integer.Sparse.eval keyMomentRow129 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 129).leftCharge (GramAssembly.key 129).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 41) := by
    have ha : gramCharges (GramAssembly.key 129).leftCharge (GramAssembly.key 129).rightCharge = raw39579 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39579Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39579 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 129).leftCharge (GramAssembly.key 129).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow129, Integer.Sparse.eval]

theorem keyMoment130 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 130) =
      Integer.Sparse.eval keyMomentRow130 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 130).leftCharge (GramAssembly.key 130).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 102) := by
    have ha : gramCharges (GramAssembly.key 130).leftCharge (GramAssembly.key 130).rightCharge = raw39580 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39580Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39580 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 130).leftCharge (GramAssembly.key 130).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow130, Integer.Sparse.eval]

theorem keyMoment131 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 131) =
      Integer.Sparse.eval keyMomentRow131 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 131).leftCharge (GramAssembly.key 131).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 143) := by
    have ha : gramCharges (GramAssembly.key 131).leftCharge (GramAssembly.key 131).rightCharge = raw39581 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39581Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39581 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 131).leftCharge (GramAssembly.key 131).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow131, Integer.Sparse.eval]

theorem keyMoment132 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 132) =
      Integer.Sparse.eval keyMomentRow132 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 132).leftCharge (GramAssembly.key 132).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 32) := by
    have ha : gramCharges (GramAssembly.key 132).leftCharge (GramAssembly.key 132).rightCharge = raw39582 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39582Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39582 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 132).leftCharge (GramAssembly.key 132).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow132, Integer.Sparse.eval]

theorem keyMoment133 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 133) =
      Integer.Sparse.eval keyMomentRow133 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 133).leftCharge (GramAssembly.key 133).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 19) := by
    have ha : gramCharges (GramAssembly.key 133).leftCharge (GramAssembly.key 133).rightCharge = raw39583 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39583Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39583 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 133).leftCharge (GramAssembly.key 133).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow133, Integer.Sparse.eval]

theorem keyMoment134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 134) =
      Integer.Sparse.eval keyMomentRow134 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 134).leftCharge (GramAssembly.key 134).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 73) := by
    have ha : gramCharges (GramAssembly.key 134).leftCharge (GramAssembly.key 134).rightCharge = raw39584 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39584Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39584 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 134).leftCharge (GramAssembly.key 134).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow134, Integer.Sparse.eval]

theorem keyMoment135 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 135) =
      Integer.Sparse.eval keyMomentRow135 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 135).leftCharge (GramAssembly.key 135).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 97) := by
    have ha : gramCharges (GramAssembly.key 135).leftCharge (GramAssembly.key 135).rightCharge = raw39585 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39585Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39585 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 135).leftCharge (GramAssembly.key 135).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow135, Integer.Sparse.eval]

theorem keyMoment136 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 136) =
      Integer.Sparse.eval keyMomentRow136 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 136).leftCharge (GramAssembly.key 136).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 197) := by
    have ha : gramCharges (GramAssembly.key 136).leftCharge (GramAssembly.key 136).rightCharge = raw39586 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39586Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39586 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 136).leftCharge (GramAssembly.key 136).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow136, Integer.Sparse.eval]

theorem keyMoment137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 137) =
      Integer.Sparse.eval keyMomentRow137 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 137).leftCharge (GramAssembly.key 137).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 249) := by
    have ha : gramCharges (GramAssembly.key 137).leftCharge (GramAssembly.key 137).rightCharge = raw39587 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39587Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39587 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 137).leftCharge (GramAssembly.key 137).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow137, Integer.Sparse.eval]

theorem keyMoment138 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 138) =
      Integer.Sparse.eval keyMomentRow138 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 138).leftCharge (GramAssembly.key 138).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 14) := by
    have ha : gramCharges (GramAssembly.key 138).leftCharge (GramAssembly.key 138).rightCharge = raw39588 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39588Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39588 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 138).leftCharge (GramAssembly.key 138).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow138, Integer.Sparse.eval]

theorem keyMoment139 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 139) =
      Integer.Sparse.eval keyMomentRow139 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 139).leftCharge (GramAssembly.key 139).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 67) := by
    have ha : gramCharges (GramAssembly.key 139).leftCharge (GramAssembly.key 139).rightCharge = raw39589 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39589Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39589 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 139).leftCharge (GramAssembly.key 139).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow139, Integer.Sparse.eval]

theorem keyMoment140 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 140) =
      Integer.Sparse.eval keyMomentRow140 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 140).leftCharge (GramAssembly.key 140).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 87) := by
    have ha : gramCharges (GramAssembly.key 140).leftCharge (GramAssembly.key 140).rightCharge = raw39590 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39590Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39590 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 140).leftCharge (GramAssembly.key 140).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow140, Integer.Sparse.eval]

theorem keyMoment141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 141) =
      Integer.Sparse.eval keyMomentRow141 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 141).leftCharge (GramAssembly.key 141).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 227) := by
    have ha : gramCharges (GramAssembly.key 141).leftCharge (GramAssembly.key 141).rightCharge = raw39591 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39591Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39591 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 141).leftCharge (GramAssembly.key 141).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow141, Integer.Sparse.eval]

theorem keyMoment142 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 142) =
      Integer.Sparse.eval keyMomentRow142 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 142).leftCharge (GramAssembly.key 142).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 60) := by
    have ha : gramCharges (GramAssembly.key 142).leftCharge (GramAssembly.key 142).rightCharge = raw39592 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39592Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39592 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 142).leftCharge (GramAssembly.key 142).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow142, Integer.Sparse.eval]

theorem keyMoment143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 143) =
      Integer.Sparse.eval keyMomentRow143 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 143).leftCharge (GramAssembly.key 143).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 169) := by
    have ha : gramCharges (GramAssembly.key 143).leftCharge (GramAssembly.key 143).rightCharge = raw39593 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39593Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39593 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 143).leftCharge (GramAssembly.key 143).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow143, Integer.Sparse.eval]

theorem keyMoment144 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 144) =
      Integer.Sparse.eval keyMomentRow144 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 144).leftCharge (GramAssembly.key 144).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 58) := by
    have ha : gramCharges (GramAssembly.key 144).leftCharge (GramAssembly.key 144).rightCharge = raw39594 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39594Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39594 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 144).leftCharge (GramAssembly.key 144).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow144, Integer.Sparse.eval]

theorem keyMoment145 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 145) =
      Integer.Sparse.eval keyMomentRow145 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 145).leftCharge (GramAssembly.key 145).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 102) := by
    have ha : gramCharges (GramAssembly.key 145).leftCharge (GramAssembly.key 145).rightCharge = raw39595 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39595Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39595 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 145).leftCharge (GramAssembly.key 145).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow145, Integer.Sparse.eval]

theorem keyMoment146 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 146) =
      Integer.Sparse.eval keyMomentRow146 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 146).leftCharge (GramAssembly.key 146).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 97) := by
    have ha : gramCharges (GramAssembly.key 146).leftCharge (GramAssembly.key 146).rightCharge = raw39596 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39596Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39596 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 146).leftCharge (GramAssembly.key 146).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow146, Integer.Sparse.eval]

theorem keyMoment147 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 147) =
      Integer.Sparse.eval keyMomentRow147 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 147).leftCharge (GramAssembly.key 147).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 76) := by
    have ha : gramCharges (GramAssembly.key 147).leftCharge (GramAssembly.key 147).rightCharge = raw39597 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39597Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39597 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 147).leftCharge (GramAssembly.key 147).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow147, Integer.Sparse.eval]

theorem keyMoment148 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 148) =
      Integer.Sparse.eval keyMomentRow148 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 148).leftCharge (GramAssembly.key 148).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 60) := by
    have ha : gramCharges (GramAssembly.key 148).leftCharge (GramAssembly.key 148).rightCharge = raw39598 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39598Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39598 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 148).leftCharge (GramAssembly.key 148).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow148, Integer.Sparse.eval]

theorem keyMoment149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 149) =
      Integer.Sparse.eval keyMomentRow149 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 149).leftCharge (GramAssembly.key 149).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 87) := by
    have ha : gramCharges (GramAssembly.key 149).leftCharge (GramAssembly.key 149).rightCharge = raw39599 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39599Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39599 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 149).leftCharge (GramAssembly.key 149).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow149, Integer.Sparse.eval]

theorem keyMoment150 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 150) =
      Integer.Sparse.eval keyMomentRow150 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 150).leftCharge (GramAssembly.key 150).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 58) := by
    have ha : gramCharges (GramAssembly.key 150).leftCharge (GramAssembly.key 150).rightCharge = raw39600 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39600Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39600 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 150).leftCharge (GramAssembly.key 150).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow150, Integer.Sparse.eval]

theorem keyMoment151 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 151) =
      Integer.Sparse.eval keyMomentRow151 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 151).leftCharge (GramAssembly.key 151).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 101) := by
    have ha : gramCharges (GramAssembly.key 151).leftCharge (GramAssembly.key 151).rightCharge = raw39601 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39601Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39601 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 151).leftCharge (GramAssembly.key 151).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow151, Integer.Sparse.eval]

theorem keyMoment152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 152) =
      Integer.Sparse.eval keyMomentRow152 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 152).leftCharge (GramAssembly.key 152).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 74) := by
    have ha : gramCharges (GramAssembly.key 152).leftCharge (GramAssembly.key 152).rightCharge = raw39602 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39602Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39602 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 152).leftCharge (GramAssembly.key 152).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow152, Integer.Sparse.eval]

theorem keyMoment153 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 153) =
      Integer.Sparse.eval keyMomentRow153 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 153).leftCharge (GramAssembly.key 153).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 103) := by
    have ha : gramCharges (GramAssembly.key 153).leftCharge (GramAssembly.key 153).rightCharge = raw39603 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39603Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39603 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 153).leftCharge (GramAssembly.key 153).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow153, Integer.Sparse.eval]

theorem keyMoment154 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 154) =
      Integer.Sparse.eval keyMomentRow154 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 154).leftCharge (GramAssembly.key 154).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 98) := by
    have ha : gramCharges (GramAssembly.key 154).leftCharge (GramAssembly.key 154).rightCharge = raw39604 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39604Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39604 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 154).leftCharge (GramAssembly.key 154).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow154, Integer.Sparse.eval]

theorem keyMoment155 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 155) =
      Integer.Sparse.eval keyMomentRow155 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 155).leftCharge (GramAssembly.key 155).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 75) := by
    have ha : gramCharges (GramAssembly.key 155).leftCharge (GramAssembly.key 155).rightCharge = raw39605 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39605Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39605 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 155).leftCharge (GramAssembly.key 155).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow155, Integer.Sparse.eval]

theorem keyMoment156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 156) =
      Integer.Sparse.eval keyMomentRow156 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 156).leftCharge (GramAssembly.key 156).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 91) := by
    have ha : gramCharges (GramAssembly.key 156).leftCharge (GramAssembly.key 156).rightCharge = raw39606 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39606Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39606 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 156).leftCharge (GramAssembly.key 156).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow156, Integer.Sparse.eval]

theorem keyMoment157 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 157) =
      Integer.Sparse.eval keyMomentRow157 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 157).leftCharge (GramAssembly.key 157).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 2) := by
    have ha : gramCharges (GramAssembly.key 157).leftCharge (GramAssembly.key 157).rightCharge = raw39607 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39607Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39607 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 157).leftCharge (GramAssembly.key 157).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow157, Integer.Sparse.eval]

theorem keyMoment158 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 158) =
      Integer.Sparse.eval keyMomentRow158 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 158).leftCharge (GramAssembly.key 158).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 94) := by
    have ha : gramCharges (GramAssembly.key 158).leftCharge (GramAssembly.key 158).rightCharge = raw39608 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39608Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39608 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 158).leftCharge (GramAssembly.key 158).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow158, Integer.Sparse.eval]

theorem keyMoment159 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 159) =
      Integer.Sparse.eval keyMomentRow159 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 159).leftCharge (GramAssembly.key 159).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 93) := by
    have ha : gramCharges (GramAssembly.key 159).leftCharge (GramAssembly.key 159).rightCharge = raw39609 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39609Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39609 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 159).leftCharge (GramAssembly.key 159).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow159, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt128 : keyMomentRows (128 : Fin 2886) =
    keyMomentRow128 := by decide +kernel

theorem keyMomentRowsAt129 : keyMomentRows (129 : Fin 2886) =
    keyMomentRow129 := by decide +kernel

theorem keyMomentRowsAt130 : keyMomentRows (130 : Fin 2886) =
    keyMomentRow130 := by decide +kernel

theorem keyMomentRowsAt131 : keyMomentRows (131 : Fin 2886) =
    keyMomentRow131 := by decide +kernel

theorem keyMomentRowsAt132 : keyMomentRows (132 : Fin 2886) =
    keyMomentRow132 := by decide +kernel

theorem keyMomentRowsAt133 : keyMomentRows (133 : Fin 2886) =
    keyMomentRow133 := by decide +kernel

theorem keyMomentRowsAt134 : keyMomentRows (134 : Fin 2886) =
    keyMomentRow134 := by decide +kernel

theorem keyMomentRowsAt135 : keyMomentRows (135 : Fin 2886) =
    keyMomentRow135 := by decide +kernel

theorem keyMomentRowsAt136 : keyMomentRows (136 : Fin 2886) =
    keyMomentRow136 := by decide +kernel

theorem keyMomentRowsAt137 : keyMomentRows (137 : Fin 2886) =
    keyMomentRow137 := by decide +kernel

theorem keyMomentRowsAt138 : keyMomentRows (138 : Fin 2886) =
    keyMomentRow138 := by decide +kernel

theorem keyMomentRowsAt139 : keyMomentRows (139 : Fin 2886) =
    keyMomentRow139 := by decide +kernel

theorem keyMomentRowsAt140 : keyMomentRows (140 : Fin 2886) =
    keyMomentRow140 := by decide +kernel

theorem keyMomentRowsAt141 : keyMomentRows (141 : Fin 2886) =
    keyMomentRow141 := by decide +kernel

theorem keyMomentRowsAt142 : keyMomentRows (142 : Fin 2886) =
    keyMomentRow142 := by decide +kernel

theorem keyMomentRowsAt143 : keyMomentRows (143 : Fin 2886) =
    keyMomentRow143 := by decide +kernel

theorem keyMomentRowsAt144 : keyMomentRows (144 : Fin 2886) =
    keyMomentRow144 := by decide +kernel

theorem keyMomentRowsAt145 : keyMomentRows (145 : Fin 2886) =
    keyMomentRow145 := by decide +kernel

theorem keyMomentRowsAt146 : keyMomentRows (146 : Fin 2886) =
    keyMomentRow146 := by decide +kernel

theorem keyMomentRowsAt147 : keyMomentRows (147 : Fin 2886) =
    keyMomentRow147 := by decide +kernel

theorem keyMomentRowsAt148 : keyMomentRows (148 : Fin 2886) =
    keyMomentRow148 := by decide +kernel

theorem keyMomentRowsAt149 : keyMomentRows (149 : Fin 2886) =
    keyMomentRow149 := by decide +kernel

theorem keyMomentRowsAt150 : keyMomentRows (150 : Fin 2886) =
    keyMomentRow150 := by decide +kernel

theorem keyMomentRowsAt151 : keyMomentRows (151 : Fin 2886) =
    keyMomentRow151 := by decide +kernel

theorem keyMomentRowsAt152 : keyMomentRows (152 : Fin 2886) =
    keyMomentRow152 := by decide +kernel

theorem keyMomentRowsAt153 : keyMomentRows (153 : Fin 2886) =
    keyMomentRow153 := by decide +kernel

theorem keyMomentRowsAt154 : keyMomentRows (154 : Fin 2886) =
    keyMomentRow154 := by decide +kernel

theorem keyMomentRowsAt155 : keyMomentRows (155 : Fin 2886) =
    keyMomentRow155 := by decide +kernel

theorem keyMomentRowsAt156 : keyMomentRows (156 : Fin 2886) =
    keyMomentRow156 := by decide +kernel

theorem keyMomentRowsAt157 : keyMomentRows (157 : Fin 2886) =
    keyMomentRow157 := by decide +kernel

theorem keyMomentRowsAt158 : keyMomentRows (158 : Fin 2886) =
    keyMomentRow158 := by decide +kernel

theorem keyMomentRowsAt159 : keyMomentRows (159 : Fin 2886) =
    keyMomentRow159 := by decide +kernel

theorem keyMomentChunkSound4_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 4) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 128 ∨ k.val = 129 ∨ k.val = 130 ∨ k.val = 131 ∨ k.val = 132 ∨ k.val = 133 ∨ k.val = 134 ∨ k.val = 135 ∨ k.val = 136 ∨ k.val = 137 ∨ k.val = 138 ∨ k.val = 139 ∨ k.val = 140 ∨ k.val = 141 ∨ k.val = 142 ∨ k.val = 143 ∨ k.val = 144 ∨ k.val = 145 ∨ k.val = 146 ∨ k.val = 147 ∨ k.val = 148 ∨ k.val = 149 ∨ k.val = 150 ∨ k.val = 151 ∨ k.val = 152 ∨ k.val = 153 ∨ k.val = 154 ∨ k.val = 155 ∨ k.val = 156 ∨ k.val = 157 ∨ k.val = 158 ∨ k.val = 159 := by omega
  rcases heq with h128 | h129 | h130 | h131 | h132 | h133 | h134 | h135 | h136 | h137 | h138 | h139 | h140 | h141 | h142 | h143 | h144 | h145 | h146 | h147 | h148 | h149 | h150 | h151 | h152 | h153 | h154 | h155 | h156 | h157 | h158 | h159
  · have he : k = (128 : Fin 2886) := Fin.ext h128
    subst k
    rw [keyMomentRowsAt128]
    exact keyMoment128 B hB
  · have he : k = (129 : Fin 2886) := Fin.ext h129
    subst k
    rw [keyMomentRowsAt129]
    exact keyMoment129 B hB
  · have he : k = (130 : Fin 2886) := Fin.ext h130
    subst k
    rw [keyMomentRowsAt130]
    exact keyMoment130 B hB
  · have he : k = (131 : Fin 2886) := Fin.ext h131
    subst k
    rw [keyMomentRowsAt131]
    exact keyMoment131 B hB
  · have he : k = (132 : Fin 2886) := Fin.ext h132
    subst k
    rw [keyMomentRowsAt132]
    exact keyMoment132 B hB
  · have he : k = (133 : Fin 2886) := Fin.ext h133
    subst k
    rw [keyMomentRowsAt133]
    exact keyMoment133 B hB
  · have he : k = (134 : Fin 2886) := Fin.ext h134
    subst k
    rw [keyMomentRowsAt134]
    exact keyMoment134 B hB
  · have he : k = (135 : Fin 2886) := Fin.ext h135
    subst k
    rw [keyMomentRowsAt135]
    exact keyMoment135 B hB
  · have he : k = (136 : Fin 2886) := Fin.ext h136
    subst k
    rw [keyMomentRowsAt136]
    exact keyMoment136 B hB
  · have he : k = (137 : Fin 2886) := Fin.ext h137
    subst k
    rw [keyMomentRowsAt137]
    exact keyMoment137 B hB
  · have he : k = (138 : Fin 2886) := Fin.ext h138
    subst k
    rw [keyMomentRowsAt138]
    exact keyMoment138 B hB
  · have he : k = (139 : Fin 2886) := Fin.ext h139
    subst k
    rw [keyMomentRowsAt139]
    exact keyMoment139 B hB
  · have he : k = (140 : Fin 2886) := Fin.ext h140
    subst k
    rw [keyMomentRowsAt140]
    exact keyMoment140 B hB
  · have he : k = (141 : Fin 2886) := Fin.ext h141
    subst k
    rw [keyMomentRowsAt141]
    exact keyMoment141 B hB
  · have he : k = (142 : Fin 2886) := Fin.ext h142
    subst k
    rw [keyMomentRowsAt142]
    exact keyMoment142 B hB
  · have he : k = (143 : Fin 2886) := Fin.ext h143
    subst k
    rw [keyMomentRowsAt143]
    exact keyMoment143 B hB
  · have he : k = (144 : Fin 2886) := Fin.ext h144
    subst k
    rw [keyMomentRowsAt144]
    exact keyMoment144 B hB
  · have he : k = (145 : Fin 2886) := Fin.ext h145
    subst k
    rw [keyMomentRowsAt145]
    exact keyMoment145 B hB
  · have he : k = (146 : Fin 2886) := Fin.ext h146
    subst k
    rw [keyMomentRowsAt146]
    exact keyMoment146 B hB
  · have he : k = (147 : Fin 2886) := Fin.ext h147
    subst k
    rw [keyMomentRowsAt147]
    exact keyMoment147 B hB
  · have he : k = (148 : Fin 2886) := Fin.ext h148
    subst k
    rw [keyMomentRowsAt148]
    exact keyMoment148 B hB
  · have he : k = (149 : Fin 2886) := Fin.ext h149
    subst k
    rw [keyMomentRowsAt149]
    exact keyMoment149 B hB
  · have he : k = (150 : Fin 2886) := Fin.ext h150
    subst k
    rw [keyMomentRowsAt150]
    exact keyMoment150 B hB
  · have he : k = (151 : Fin 2886) := Fin.ext h151
    subst k
    rw [keyMomentRowsAt151]
    exact keyMoment151 B hB
  · have he : k = (152 : Fin 2886) := Fin.ext h152
    subst k
    rw [keyMomentRowsAt152]
    exact keyMoment152 B hB
  · have he : k = (153 : Fin 2886) := Fin.ext h153
    subst k
    rw [keyMomentRowsAt153]
    exact keyMoment153 B hB
  · have he : k = (154 : Fin 2886) := Fin.ext h154
    subst k
    rw [keyMomentRowsAt154]
    exact keyMoment154 B hB
  · have he : k = (155 : Fin 2886) := Fin.ext h155
    subst k
    rw [keyMomentRowsAt155]
    exact keyMoment155 B hB
  · have he : k = (156 : Fin 2886) := Fin.ext h156
    subst k
    rw [keyMomentRowsAt156]
    exact keyMoment156 B hB
  · have he : k = (157 : Fin 2886) := Fin.ext h157
    subst k
    rw [keyMomentRowsAt157]
    exact keyMoment157 B hB
  · have he : k = (158 : Fin 2886) := Fin.ext h158
    subst k
    rw [keyMomentRowsAt158]
    exact keyMoment158 B hB
  · have he : k = (159 : Fin 2886) := Fin.ext h159
    subst k
    rw [keyMomentRowsAt159]
    exact keyMoment159 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound4_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound4_e_oai
