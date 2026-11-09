-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound55_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:58:09.573207+00:00
-- url     : https://prove2.me/submissions/6e1a3a9a-51f7-410e-b768-5bd549903211

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

theorem canonical41173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41173 raw41173Labels = mixedMoment B node611 node611Labels := by
  calc
    mixedMoment B raw41173 raw41173Labels = mixedMoment B raw41173step0 raw41173step0Labels := by
      have hz : ∀ j, raw41173 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41173step0 = (fun i j => raw41173 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41173step0 raw41173; decide +kernel
      have hl : raw41173step0Labels = raw41173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41173 raw41173Labels permutation520 hz
    mixedMoment B raw41173step0 raw41173step0Labels = mixedMoment B raw41173step1 raw41173step1Labels := by
      have hz : ∀ j, raw41173step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41173step1 = (fun i j => raw41173step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41173step1 raw41173step0; decide +kernel
      have hl : raw41173step1Labels = raw41173step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41173step0 raw41173step0Labels permutation104 hz
    mixedMoment B raw41173step1 raw41173step1Labels = mixedMoment B raw41173step2 raw41173step2Labels := by
      have ha : raw41173step2 = (fun i j => raw41173step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41173step2 raw41173step1; decide +kernel
      have hl : raw41173step2Labels = raw41173step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41173step1 raw41173step1Labels permutation8 permutation6
    mixedMoment B raw41173step2 raw41173step2Labels = mixedMoment B raw41173step3 raw41173step3Labels := by
      have ha : raw41173step3 = -raw41173step2 := by apply Matrix.ext; change ∀ i j, raw41173step3 i j = -(raw41173step2 i j); unfold raw41173step3 raw41173step2; decide +kernel
      have hl : raw41173step3Labels = raw41173step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node611 node611Labels := by rfl

theorem canonical41174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41174 raw41174Labels = mixedMoment B node603 node603Labels := by
  calc
    mixedMoment B raw41174 raw41174Labels = mixedMoment B raw41174step0 raw41174step0Labels := by
      have hz : ∀ j, raw41174 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41174step0 = (fun i j => raw41174 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41174step0 raw41174; decide +kernel
      have hl : raw41174step0Labels = raw41174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41174 raw41174Labels permutation434 hz
    mixedMoment B raw41174step0 raw41174step0Labels = mixedMoment B raw41174step1 raw41174step1Labels := by
      have ha : raw41174step1 = (fun i j => raw41174step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41174step1 raw41174step0; decide +kernel
      have hl : raw41174step1Labels = raw41174step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41174step0 raw41174step0Labels permutation50 permutation6
    mixedMoment B raw41174step1 raw41174step1Labels = mixedMoment B raw41174step2 raw41174step2Labels := by
      have ha : raw41174step2 = -raw41174step1 := by apply Matrix.ext; change ∀ i j, raw41174step2 i j = -(raw41174step1 i j); unfold raw41174step2 raw41174step1; decide +kernel
      have hl : raw41174step2Labels = raw41174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node603 node603Labels := by rfl

theorem canonical41175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41175 raw41175Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw41175 raw41175Labels = mixedMoment B raw41175step0 raw41175step0Labels := by
      have hz : ∀ j, raw41175 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41175step0 = (fun i j => raw41175 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41175step0 raw41175; decide +kernel
      have hl : raw41175step0Labels = raw41175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41175 raw41175Labels permutation520 hz
    mixedMoment B raw41175step0 raw41175step0Labels = mixedMoment B raw41175step1 raw41175step1Labels := by
      have hz : ∀ j, raw41175step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41175step1 = (fun i j => raw41175step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41175step1 raw41175step0; decide +kernel
      have hl : raw41175step1Labels = raw41175step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41175step0 raw41175step0Labels permutation104 hz
    mixedMoment B raw41175step1 raw41175step1Labels = mixedMoment B raw41175step2 raw41175step2Labels := by
      have hz : ∀ j, raw41175step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41175step2 = (fun i j => raw41175step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41175step2 raw41175step1; decide +kernel
      have hl : raw41175step2Labels = raw41175step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41175step1 raw41175step1Labels permutation20 hz
    mixedMoment B raw41175step2 raw41175step2Labels = mixedMoment B raw41175step3 raw41175step3Labels := by
      have ha : raw41175step3 = (fun i j => raw41175step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41175step3 raw41175step2; decide +kernel
      have hl : raw41175step3Labels = raw41175step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41175step2 raw41175step2Labels permutation2 permutation6
    mixedMoment B raw41175step3 raw41175step3Labels = mixedMoment B raw41175step4 raw41175step4Labels := by
      have ha : raw41175step4 = -raw41175step3 := by apply Matrix.ext; change ∀ i j, raw41175step4 i j = -(raw41175step3 i j); unfold raw41175step4 raw41175step3; decide +kernel
      have hl : raw41175step4Labels = raw41175step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node615 node615Labels := by rfl

theorem canonical41176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41176 raw41176Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw41176 raw41176Labels = mixedMoment B raw41176step0 raw41176step0Labels := by
      have hz : ∀ j, raw41176 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41176step0 = (fun i j => raw41176 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41176step0 raw41176; decide +kernel
      have hl : raw41176step0Labels = raw41176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41176 raw41176Labels permutation434 hz
    mixedMoment B raw41176step0 raw41176step0Labels = mixedMoment B raw41176step1 raw41176step1Labels := by
      have hz : ∀ j, raw41176step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41176step1 = (fun i j => raw41176step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41176step1 raw41176step0; decide +kernel
      have hl : raw41176step1Labels = raw41176step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41176step0 raw41176step0Labels permutation80 hz
    mixedMoment B raw41176step1 raw41176step1Labels = mixedMoment B raw41176step2 raw41176step2Labels := by
      have ha : raw41176step2 = (fun i j => raw41176step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41176step2 raw41176step1; decide +kernel
      have hl : raw41176step2Labels = raw41176step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41176step1 raw41176step1Labels permutation12 permutation6
    mixedMoment B raw41176step2 raw41176step2Labels = mixedMoment B raw41176step3 raw41176step3Labels := by
      have ha : raw41176step3 = -raw41176step2 := by apply Matrix.ext; change ∀ i j, raw41176step3 i j = -(raw41176step2 i j); unfold raw41176step3 raw41176step2; decide +kernel
      have hl : raw41176step3Labels = raw41176step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node605 node605Labels := by rfl

theorem canonical41177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41177 raw41177Labels = mixedMoment B node614 node614Labels := by
  calc
    mixedMoment B raw41177 raw41177Labels = mixedMoment B raw41177step0 raw41177step0Labels := by
      have hz : ∀ j, raw41177 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41177step0 = (fun i j => raw41177 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41177step0 raw41177; decide +kernel
      have hl : raw41177step0Labels = raw41177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41177 raw41177Labels permutation434 hz
    mixedMoment B raw41177step0 raw41177step0Labels = mixedMoment B raw41177step1 raw41177step1Labels := by
      have hz : ∀ j, raw41177step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41177step1 = (fun i j => raw41177step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41177step1 raw41177step0; decide +kernel
      have hl : raw41177step1Labels = raw41177step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41177step0 raw41177step0Labels permutation80 hz
    mixedMoment B raw41177step1 raw41177step1Labels = mixedMoment B raw41177step2 raw41177step2Labels := by
      have ha : raw41177step2 = (fun i j => raw41177step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41177step2 raw41177step1; decide +kernel
      have hl : raw41177step2Labels = raw41177step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41177step1 raw41177step1Labels permutation8 permutation6
    mixedMoment B raw41177step2 raw41177step2Labels = mixedMoment B raw41177step3 raw41177step3Labels := by
      have ha : raw41177step3 = -raw41177step2 := by apply Matrix.ext; change ∀ i j, raw41177step3 i j = -(raw41177step2 i j); unfold raw41177step3 raw41177step2; decide +kernel
      have hl : raw41177step3Labels = raw41177step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node614 node614Labels := by rfl

theorem canonical41178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41178 raw41178Labels = mixedMoment B node622 node622Labels := by
  calc
    mixedMoment B raw41178 raw41178Labels = mixedMoment B raw41178step0 raw41178step0Labels := by
      have hz : ∀ j, raw41178 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41178step0 = (fun i j => raw41178 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41178step0 raw41178; decide +kernel
      have hl : raw41178step0Labels = raw41178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41178 raw41178Labels permutation520 hz
    mixedMoment B raw41178step0 raw41178step0Labels = mixedMoment B raw41178step1 raw41178step1Labels := by
      have hz : ∀ j, raw41178step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41178step1 = (fun i j => raw41178step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41178step1 raw41178step0; decide +kernel
      have hl : raw41178step1Labels = raw41178step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41178step0 raw41178step0Labels permutation104 hz
    mixedMoment B raw41178step1 raw41178step1Labels = mixedMoment B raw41178step2 raw41178step2Labels := by
      have hz : ∀ j, raw41178step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41178step2 = (fun i j => raw41178step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41178step2 raw41178step1; decide +kernel
      have hl : raw41178step2Labels = raw41178step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41178step1 raw41178step1Labels permutation20 hz
    mixedMoment B raw41178step2 raw41178step2Labels = mixedMoment B raw41178step3 raw41178step3Labels := by
      have hz : ∀ j, raw41178step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw41178step3 = (fun i j => raw41178step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw41178step3 raw41178step2; decide +kernel
      have hl : raw41178step3Labels = raw41178step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41178step2 raw41178step2Labels permutation4 hz
    mixedMoment B raw41178step3 raw41178step3Labels = mixedMoment B raw41178step4 raw41178step4Labels := by
      have ha : raw41178step4 = (fun i j => raw41178step3 (permutation1 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41178step4 raw41178step3; decide +kernel
      have hl : raw41178step4Labels = raw41178step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41178step3 raw41178step3Labels permutation1 permutation6
    _ = mixedMoment B node622 node622Labels := by rfl

theorem canonical41179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41179 raw41179Labels = mixedMoment B node619 node619Labels := by
  calc
    mixedMoment B raw41179 raw41179Labels = mixedMoment B raw41179step0 raw41179step0Labels := by
      have hz : ∀ j, raw41179 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41179step0 = (fun i j => raw41179 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41179step0 raw41179; decide +kernel
      have hl : raw41179step0Labels = raw41179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41179 raw41179Labels permutation434 hz
    mixedMoment B raw41179step0 raw41179step0Labels = mixedMoment B raw41179step1 raw41179step1Labels := by
      have hz : ∀ j, raw41179step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41179step1 = (fun i j => raw41179step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41179step1 raw41179step0; decide +kernel
      have hl : raw41179step1Labels = raw41179step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41179step0 raw41179step0Labels permutation80 hz
    mixedMoment B raw41179step1 raw41179step1Labels = mixedMoment B raw41179step2 raw41179step2Labels := by
      have hz : ∀ j, raw41179step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41179step2 = (fun i j => raw41179step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41179step2 raw41179step1; decide +kernel
      have hl : raw41179step2Labels = raw41179step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41179step1 raw41179step1Labels permutation14 hz
    mixedMoment B raw41179step2 raw41179step2Labels = mixedMoment B raw41179step3 raw41179step3Labels := by
      have ha : raw41179step3 = (fun i j => raw41179step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41179step3 raw41179step2; decide +kernel
      have hl : raw41179step3Labels = raw41179step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41179step2 raw41179step2Labels permutation3 permutation6
    mixedMoment B raw41179step3 raw41179step3Labels = mixedMoment B raw41179step4 raw41179step4Labels := by
      have ha : raw41179step4 = -raw41179step3 := by apply Matrix.ext; change ∀ i j, raw41179step4 i j = -(raw41179step3 i j); unfold raw41179step4 raw41179step3; decide +kernel
      have hl : raw41179step4Labels = raw41179step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node619 node619Labels := by rfl

theorem canonical41180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41180 raw41180Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw41180 raw41180Labels = mixedMoment B raw41180step0 raw41180step0Labels := by
      have hz : ∀ j, raw41180 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41180step0 = (fun i j => raw41180 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41180step0 raw41180; decide +kernel
      have hl : raw41180step0Labels = raw41180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41180 raw41180Labels permutation434 hz
    mixedMoment B raw41180step0 raw41180step0Labels = mixedMoment B raw41180step1 raw41180step1Labels := by
      have ha : raw41180step1 = (fun i j => raw41180step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41180step1 raw41180step0; decide +kernel
      have hl : raw41180step1Labels = raw41180step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41180step0 raw41180step0Labels permutation149 permutation3
    mixedMoment B raw41180step1 raw41180step1Labels = mixedMoment B raw41180step2 raw41180step2Labels := by
      have ha : raw41180step2 = -raw41180step1 := by apply Matrix.ext; change ∀ i j, raw41180step2 i j = -(raw41180step1 i j); unfold raw41180step2 raw41180step1; decide +kernel
      have hl : raw41180step2Labels = raw41180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2738 node2738Labels := by rfl

theorem canonical41181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41181 raw41181Labels = mixedMoment B node3050 node3050Labels := by
  calc
    mixedMoment B raw41181 raw41181Labels = mixedMoment B raw41181step0 raw41181step0Labels := by
      have hz : ∀ j, raw41181 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41181step0 = (fun i j => raw41181 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41181step0 raw41181; decide +kernel
      have hl : raw41181step0Labels = raw41181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41181 raw41181Labels permutation434 hz
    mixedMoment B raw41181step0 raw41181step0Labels = mixedMoment B raw41181step1 raw41181step1Labels := by
      have ha : raw41181step1 = (fun i j => raw41181step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41181step1 raw41181step0; decide +kernel
      have hl : raw41181step1Labels = raw41181step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41181step0 raw41181step0Labels permutation149 permutation3
    mixedMoment B raw41181step1 raw41181step1Labels = mixedMoment B raw41181step2 raw41181step2Labels := by
      have ha : raw41181step2 = -raw41181step1 := by apply Matrix.ext; change ∀ i j, raw41181step2 i j = -(raw41181step1 i j); unfold raw41181step2 raw41181step1; decide +kernel
      have hl : raw41181step2Labels = raw41181step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3050 node3050Labels := by rfl

theorem canonical41182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41182 raw41182Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw41182 raw41182Labels = mixedMoment B raw41182step0 raw41182step0Labels := by
      have hz : ∀ j, raw41182 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41182step0 = (fun i j => raw41182 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41182step0 raw41182; decide +kernel
      have hl : raw41182step0Labels = raw41182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41182 raw41182Labels permutation434 hz
    mixedMoment B raw41182step0 raw41182step0Labels = mixedMoment B raw41182step1 raw41182step1Labels := by
      have ha : raw41182step1 = (fun i j => raw41182step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41182step1 raw41182step0; decide +kernel
      have hl : raw41182step1Labels = raw41182step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41182step0 raw41182step0Labels permutation48 permutation6
    _ = mixedMoment B node3625 node3625Labels := by rfl

theorem canonical41183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41183 raw41183Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw41183 raw41183Labels = mixedMoment B raw41183step0 raw41183step0Labels := by
      have hz : ∀ j, raw41183 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41183step0 = (fun i j => raw41183 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41183step0 raw41183; decide +kernel
      have hl : raw41183step0Labels = raw41183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41183 raw41183Labels permutation434 hz
    mixedMoment B raw41183step0 raw41183step0Labels = mixedMoment B raw41183step1 raw41183step1Labels := by
      have ha : raw41183step1 = (fun i j => raw41183step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41183step1 raw41183step0; decide +kernel
      have hl : raw41183step1Labels = raw41183step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41183step0 raw41183step0Labels permutation50 permutation6
    _ = mixedMoment B node3580 node3580Labels := by rfl

theorem canonical41184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41184 raw41184Labels = mixedMoment B node3073 node3073Labels := by
  calc
    mixedMoment B raw41184 raw41184Labels = mixedMoment B raw41184step0 raw41184step0Labels := by
      have ha : raw41184step0 = (fun i j => raw41184 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41184step0 raw41184; decide +kernel
      have hl : raw41184step0Labels = raw41184Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41184 raw41184Labels permutation662 permutation3
    mixedMoment B raw41184step0 raw41184step0Labels = mixedMoment B raw41184step1 raw41184step1Labels := by
      have ha : raw41184step1 = -raw41184step0 := by apply Matrix.ext; change ∀ i j, raw41184step1 i j = -(raw41184step0 i j); unfold raw41184step1 raw41184step0; decide +kernel
      have hl : raw41184step1Labels = raw41184step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3073 node3073Labels := by rfl

theorem canonical41185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41185 raw41185Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw41185 raw41185Labels = mixedMoment B raw41185step0 raw41185step0Labels := by
      have ha : raw41185step0 = (fun i j => raw41185 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41185step0 raw41185; decide +kernel
      have hl : raw41185step0Labels = raw41185Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41185 raw41185Labels permutation260 permutation6
    _ = mixedMoment B node3571 node3571Labels := by rfl

theorem canonical41186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41186 raw41186Labels = mixedMoment B node3388 node3388Labels := by
  calc
    mixedMoment B raw41186 raw41186Labels = mixedMoment B raw41186step0 raw41186step0Labels := by
      have ha : raw41186step0 = (fun i j => raw41186 (permutation246 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41186step0 raw41186; decide +kernel
      have hl : raw41186step0Labels = raw41186Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41186 raw41186Labels permutation246 permutation6
    _ = mixedMoment B node3388 node3388Labels := by rfl

theorem canonical41187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41187 raw41187Labels = mixedMoment B node3375 node3375Labels := by
  calc
    mixedMoment B raw41187 raw41187Labels = mixedMoment B raw41187step0 raw41187step0Labels := by
      have ha : raw41187step0 = (fun i j => raw41187 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41187step0 raw41187; decide +kernel
      have hl : raw41187step0Labels = raw41187Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41187 raw41187Labels permutation260 permutation6
    _ = mixedMoment B node3375 node3375Labels := by rfl

theorem canonical41188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41188 raw41188Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw41188 raw41188Labels = mixedMoment B raw41188step0 raw41188step0Labels := by
      have hz : ∀ j, raw41188 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41188step0 = (fun i j => raw41188 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41188step0 raw41188; decide +kernel
      have hl : raw41188step0Labels = raw41188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41188 raw41188Labels permutation520 hz
    mixedMoment B raw41188step0 raw41188step0Labels = mixedMoment B raw41188step1 raw41188step1Labels := by
      have hz : ∀ j, raw41188step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41188step1 = (fun i j => raw41188step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41188step1 raw41188step0; decide +kernel
      have hl : raw41188step1Labels = raw41188step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41188step0 raw41188step0Labels permutation104 hz
    mixedMoment B raw41188step1 raw41188step1Labels = mixedMoment B raw41188step2 raw41188step2Labels := by
      have ha : raw41188step2 = (fun i j => raw41188step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41188step2 raw41188step1; decide +kernel
      have hl : raw41188step2Labels = raw41188step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41188step1 raw41188step1Labels permutation31 permutation3
    mixedMoment B raw41188step2 raw41188step2Labels = mixedMoment B raw41188step3 raw41188step3Labels := by
      have ha : raw41188step3 = -raw41188step2 := by apply Matrix.ext; change ∀ i j, raw41188step3 i j = -(raw41188step2 i j); unfold raw41188step3 raw41188step2; decide +kernel
      have hl : raw41188step3Labels = raw41188step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2781 node2781Labels := by rfl

theorem canonical41189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41189 raw41189Labels = mixedMoment B node3096 node3096Labels := by
  calc
    mixedMoment B raw41189 raw41189Labels = mixedMoment B raw41189step0 raw41189step0Labels := by
      have hz : ∀ j, raw41189 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41189step0 = (fun i j => raw41189 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41189step0 raw41189; decide +kernel
      have hl : raw41189step0Labels = raw41189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41189 raw41189Labels permutation434 hz
    mixedMoment B raw41189step0 raw41189step0Labels = mixedMoment B raw41189step1 raw41189step1Labels := by
      have ha : raw41189step1 = (fun i j => raw41189step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41189step1 raw41189step0; decide +kernel
      have hl : raw41189step1Labels = raw41189step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41189step0 raw41189step0Labels permutation151 permutation3
    mixedMoment B raw41189step1 raw41189step1Labels = mixedMoment B raw41189step2 raw41189step2Labels := by
      have ha : raw41189step2 = -raw41189step1 := by apply Matrix.ext; change ∀ i j, raw41189step2 i j = -(raw41189step1 i j); unfold raw41189step2 raw41189step1; decide +kernel
      have hl : raw41189step2Labels = raw41189step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3096 node3096Labels := by rfl

theorem canonical41190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41190 raw41190Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw41190 raw41190Labels = mixedMoment B raw41190step0 raw41190step0Labels := by
      have hz : ∀ j, raw41190 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41190step0 = (fun i j => raw41190 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41190step0 raw41190; decide +kernel
      have hl : raw41190step0Labels = raw41190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41190 raw41190Labels permutation434 hz
    mixedMoment B raw41190step0 raw41190step0Labels = mixedMoment B raw41190step1 raw41190step1Labels := by
      have ha : raw41190step1 = (fun i j => raw41190step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41190step1 raw41190step0; decide +kernel
      have hl : raw41190step1Labels = raw41190step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41190step0 raw41190step0Labels permutation54 permutation6
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical41191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41191 raw41191Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw41191 raw41191Labels = mixedMoment B raw41191step0 raw41191step0Labels := by
      have hz : ∀ j, raw41191 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41191step0 = (fun i j => raw41191 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41191step0 raw41191; decide +kernel
      have hl : raw41191step0Labels = raw41191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41191 raw41191Labels permutation434 hz
    mixedMoment B raw41191step0 raw41191step0Labels = mixedMoment B raw41191step1 raw41191step1Labels := by
      have ha : raw41191step1 = (fun i j => raw41191step0 (permutation51 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41191step1 raw41191step0; decide +kernel
      have hl : raw41191step1Labels = raw41191step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41191step0 raw41191step0Labels permutation51 permutation6
    _ = mixedMoment B node3392 node3392Labels := by rfl

theorem canonical41192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41192 raw41192Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw41192 raw41192Labels = mixedMoment B raw41192step0 raw41192step0Labels := by
      have ha : raw41192step0 = (fun i j => raw41192 (permutation261 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41192step0 raw41192; decide +kernel
      have hl : raw41192step0Labels = raw41192Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41192 raw41192Labels permutation261 permutation6
    _ = mixedMoment B node3376 node3376Labels := by rfl

theorem canonical41193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41193 raw41193Labels = mixedMoment B node2603 node2603Labels := by
  calc
    mixedMoment B raw41193 raw41193Labels = mixedMoment B raw41193step0 raw41193step0Labels := by
      have hz : ∀ j, raw41193 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41193step0 = (fun i j => raw41193 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41193step0 raw41193; decide +kernel
      have hl : raw41193step0Labels = raw41193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41193 raw41193Labels permutation520 hz
    mixedMoment B raw41193step0 raw41193step0Labels = mixedMoment B raw41193step1 raw41193step1Labels := by
      have hz : ∀ j, raw41193step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41193step1 = (fun i j => raw41193step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41193step1 raw41193step0; decide +kernel
      have hl : raw41193step1Labels = raw41193step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41193step0 raw41193step0Labels permutation104 hz
    mixedMoment B raw41193step1 raw41193step1Labels = mixedMoment B raw41193step2 raw41193step2Labels := by
      have ha : raw41193step2 = (fun i j => raw41193step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41193step2 raw41193step1; decide +kernel
      have hl : raw41193step2Labels = raw41193step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41193step1 raw41193step1Labels permutation23 permutation6
    mixedMoment B raw41193step2 raw41193step2Labels = mixedMoment B raw41193step3 raw41193step3Labels := by
      have ha : raw41193step3 = -raw41193step2 := by apply Matrix.ext; change ∀ i j, raw41193step3 i j = -(raw41193step2 i j); unfold raw41193step3 raw41193step2; decide +kernel
      have hl : raw41193step3Labels = raw41193step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2603 node2603Labels := by rfl

theorem canonical41194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41194 raw41194Labels = mixedMoment B node2560 node2560Labels := by
  calc
    mixedMoment B raw41194 raw41194Labels = mixedMoment B raw41194step0 raw41194step0Labels := by
      have hz : ∀ j, raw41194 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41194step0 = (fun i j => raw41194 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41194step0 raw41194; decide +kernel
      have hl : raw41194step0Labels = raw41194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41194 raw41194Labels permutation434 hz
    mixedMoment B raw41194step0 raw41194step0Labels = mixedMoment B raw41194step1 raw41194step1Labels := by
      have ha : raw41194step1 = (fun i j => raw41194step0 (permutation89 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41194step1 raw41194step0; decide +kernel
      have hl : raw41194step1Labels = raw41194step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41194step0 raw41194step0Labels permutation89 permutation6
    mixedMoment B raw41194step1 raw41194step1Labels = mixedMoment B raw41194step2 raw41194step2Labels := by
      have ha : raw41194step2 = -raw41194step1 := by apply Matrix.ext; change ∀ i j, raw41194step2 i j = -(raw41194step1 i j); unfold raw41194step2 raw41194step1; decide +kernel
      have hl : raw41194step2Labels = raw41194step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2560 node2560Labels := by rfl

theorem canonical41195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41195 raw41195Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw41195 raw41195Labels = mixedMoment B raw41195step0 raw41195step0Labels := by
      have hz : ∀ j, raw41195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41195step0 = (fun i j => raw41195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41195step0 raw41195; decide +kernel
      have hl : raw41195step0Labels = raw41195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41195 raw41195Labels permutation346 hz
    mixedMoment B raw41195step0 raw41195step0Labels = mixedMoment B raw41195step1 raw41195step1Labels := by
      have ha : raw41195step1 = (fun i j => raw41195step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41195step1 raw41195step0; decide +kernel
      have hl : raw41195step1Labels = raw41195step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41195step0 raw41195step0Labels permutation50 permutation6
    _ = mixedMoment B node3581 node3581Labels := by rfl

theorem canonical41196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41196 raw41196Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw41196 raw41196Labels = mixedMoment B raw41196step0 raw41196step0Labels := by
      have hz : ∀ j, raw41196 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41196step0 = (fun i j => raw41196 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41196step0 raw41196; decide +kernel
      have hl : raw41196step0Labels = raw41196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41196 raw41196Labels permutation346 hz
    mixedMoment B raw41196step0 raw41196step0Labels = mixedMoment B raw41196step1 raw41196step1Labels := by
      have ha : raw41196step1 = (fun i j => raw41196step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41196step1 raw41196step0; decide +kernel
      have hl : raw41196step1Labels = raw41196step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41196step0 raw41196step0Labels permutation50 permutation6
    _ = mixedMoment B node3391 node3391Labels := by rfl

theorem canonical41197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41197 raw41197Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw41197 raw41197Labels = mixedMoment B raw41197step0 raw41197step0Labels := by
      have hz : ∀ j, raw41197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41197step0 = (fun i j => raw41197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41197step0 raw41197; decide +kernel
      have hl : raw41197step0Labels = raw41197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41197 raw41197Labels permutation346 hz
    mixedMoment B raw41197step0 raw41197step0Labels = mixedMoment B raw41197step1 raw41197step1Labels := by
      have ha : raw41197step1 = (fun i j => raw41197step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41197step1 raw41197step0; decide +kernel
      have hl : raw41197step1Labels = raw41197step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41197step0 raw41197step0Labels permutation44 permutation6
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical41198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41198 raw41198Labels = mixedMoment B node3622 node3622Labels := by
  calc
    mixedMoment B raw41198 raw41198Labels = mixedMoment B raw41198step0 raw41198step0Labels := by
      have hz : ∀ j, raw41198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41198step0 = (fun i j => raw41198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41198step0 raw41198; decide +kernel
      have hl : raw41198step0Labels = raw41198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41198 raw41198Labels permutation346 hz
    mixedMoment B raw41198step0 raw41198step0Labels = mixedMoment B raw41198step1 raw41198step1Labels := by
      have ha : raw41198step1 = (fun i j => raw41198step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41198step1 raw41198step0; decide +kernel
      have hl : raw41198step1Labels = raw41198step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41198step0 raw41198step0Labels permutation48 permutation6
    _ = mixedMoment B node3622 node3622Labels := by rfl

theorem canonical41199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41199 raw41199Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw41199 raw41199Labels = mixedMoment B raw41199step0 raw41199step0Labels := by
      have hz : ∀ j, raw41199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41199step0 = (fun i j => raw41199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41199step0 raw41199; decide +kernel
      have hl : raw41199step0Labels = raw41199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41199 raw41199Labels permutation346 hz
    mixedMoment B raw41199step0 raw41199step0Labels = mixedMoment B raw41199step1 raw41199step1Labels := by
      have ha : raw41199step1 = (fun i j => raw41199step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41199step1 raw41199step0; decide +kernel
      have hl : raw41199step1Labels = raw41199step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41199step0 raw41199step0Labels permutation48 permutation6
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical41200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41200 raw41200Labels = mixedMoment B node3390 node3390Labels := by
  calc
    mixedMoment B raw41200 raw41200Labels = mixedMoment B raw41200step0 raw41200step0Labels := by
      have ha : raw41200step0 = (fun i j => raw41200 (permutation246 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41200step0 raw41200; decide +kernel
      have hl : raw41200step0Labels = raw41200Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41200 raw41200Labels permutation246 permutation6
    _ = mixedMoment B node3390 node3390Labels := by rfl

theorem canonical41201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41201 raw41201Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw41201 raw41201Labels = mixedMoment B raw41201step0 raw41201step0Labels := by
      have ha : raw41201step0 = (fun i j => raw41201 (permutation240 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41201step0 raw41201; decide +kernel
      have hl : raw41201step0Labels = raw41201Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41201 raw41201Labels permutation240 permutation6
    _ = mixedMoment B node3532 node3532Labels := by rfl

theorem canonical41202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41202 raw41202Labels = mixedMoment B node3118 node3118Labels := by
  calc
    mixedMoment B raw41202 raw41202Labels = mixedMoment B raw41202step0 raw41202step0Labels := by
      have hz : ∀ j, raw41202 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41202step0 = (fun i j => raw41202 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41202step0 raw41202; decide +kernel
      have hl : raw41202step0Labels = raw41202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41202 raw41202Labels permutation520 hz
    mixedMoment B raw41202step0 raw41202step0Labels = mixedMoment B raw41202step1 raw41202step1Labels := by
      have hz : ∀ j, raw41202step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41202step1 = (fun i j => raw41202step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41202step1 raw41202step0; decide +kernel
      have hl : raw41202step1Labels = raw41202step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41202step0 raw41202step0Labels permutation104 hz
    mixedMoment B raw41202step1 raw41202step1Labels = mixedMoment B raw41202step2 raw41202step2Labels := by
      have ha : raw41202step2 = (fun i j => raw41202step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41202step2 raw41202step1; decide +kernel
      have hl : raw41202step2Labels = raw41202step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41202step1 raw41202step1Labels permutation29 permutation3
    mixedMoment B raw41202step2 raw41202step2Labels = mixedMoment B raw41202step3 raw41202step3Labels := by
      have ha : raw41202step3 = -raw41202step2 := by apply Matrix.ext; change ∀ i j, raw41202step3 i j = -(raw41202step2 i j); unfold raw41202step3 raw41202step2; decide +kernel
      have hl : raw41202step3Labels = raw41202step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3118 node3118Labels := by rfl

theorem canonical41203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41203 raw41203Labels = mixedMoment B node3380 node3380Labels := by
  calc
    mixedMoment B raw41203 raw41203Labels = mixedMoment B raw41203step0 raw41203step0Labels := by
      have hz : ∀ j, raw41203 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41203step0 = (fun i j => raw41203 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41203step0 raw41203; decide +kernel
      have hl : raw41203step0Labels = raw41203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41203 raw41203Labels permutation434 hz
    mixedMoment B raw41203step0 raw41203step0Labels = mixedMoment B raw41203step1 raw41203step1Labels := by
      have ha : raw41203step1 = (fun i j => raw41203step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41203step1 raw41203step0; decide +kernel
      have hl : raw41203step1Labels = raw41203step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41203step0 raw41203step0Labels permutation54 permutation6
    _ = mixedMoment B node3380 node3380Labels := by rfl

theorem canonical41204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41204 raw41204Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw41204 raw41204Labels = mixedMoment B raw41204step0 raw41204step0Labels := by
      have hz : ∀ j, raw41204 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41204step0 = (fun i j => raw41204 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41204step0 raw41204; decide +kernel
      have hl : raw41204step0Labels = raw41204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41204 raw41204Labels permutation520 hz
    mixedMoment B raw41204step0 raw41204step0Labels = mixedMoment B raw41204step1 raw41204step1Labels := by
      have hz : ∀ j, raw41204step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41204step1 = (fun i j => raw41204step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41204step1 raw41204step0; decide +kernel
      have hl : raw41204step1Labels = raw41204step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41204step0 raw41204step0Labels permutation104 hz
    mixedMoment B raw41204step1 raw41204step1Labels = mixedMoment B raw41204step2 raw41204step2Labels := by
      have hz : ∀ j, raw41204step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41204step2 = (fun i j => raw41204step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41204step2 raw41204step1; decide +kernel
      have hl : raw41204step2Labels = raw41204step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41204step1 raw41204step1Labels permutation20 hz
    mixedMoment B raw41204step2 raw41204step2Labels = mixedMoment B raw41204step3 raw41204step3Labels := by
      have ha : raw41204step3 = (fun i j => raw41204step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41204step3 raw41204step2; decide +kernel
      have hl : raw41204step3Labels = raw41204step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41204step2 raw41204step2Labels permutation3 permutation6
    _ = mixedMoment B node3633 node3633Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1760 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1760) =
      Integer.Sparse.eval keyMomentRow1760 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1760).leftCharge (GramAssembly.key 1760).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 611) := by
    have ha : gramCharges (GramAssembly.key 1760).leftCharge (GramAssembly.key 1760).rightCharge = raw41173 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41173Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41173 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1760).leftCharge (GramAssembly.key 1760).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1760, Integer.Sparse.eval]

theorem keyMoment1761 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1761) =
      Integer.Sparse.eval keyMomentRow1761 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1761).leftCharge (GramAssembly.key 1761).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 603) := by
    have ha : gramCharges (GramAssembly.key 1761).leftCharge (GramAssembly.key 1761).rightCharge = raw41174 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41174Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41174 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1761).leftCharge (GramAssembly.key 1761).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1761, Integer.Sparse.eval]

theorem keyMoment1762 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1762) =
      Integer.Sparse.eval keyMomentRow1762 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1762).leftCharge (GramAssembly.key 1762).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 615) := by
    have ha : gramCharges (GramAssembly.key 1762).leftCharge (GramAssembly.key 1762).rightCharge = raw41175 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41175Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41175 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1762).leftCharge (GramAssembly.key 1762).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1762, Integer.Sparse.eval]

theorem keyMoment1763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1763) =
      Integer.Sparse.eval keyMomentRow1763 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1763).leftCharge (GramAssembly.key 1763).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 605) := by
    have ha : gramCharges (GramAssembly.key 1763).leftCharge (GramAssembly.key 1763).rightCharge = raw41176 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41176Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41176 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1763).leftCharge (GramAssembly.key 1763).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1763, Integer.Sparse.eval]

theorem keyMoment1764 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1764) =
      Integer.Sparse.eval keyMomentRow1764 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1764).leftCharge (GramAssembly.key 1764).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 614) := by
    have ha : gramCharges (GramAssembly.key 1764).leftCharge (GramAssembly.key 1764).rightCharge = raw41177 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41177Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41177 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1764).leftCharge (GramAssembly.key 1764).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1764, Integer.Sparse.eval]

theorem keyMoment1765 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1765) =
      Integer.Sparse.eval keyMomentRow1765 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1765).leftCharge (GramAssembly.key 1765).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 622) := by
    have ha : gramCharges (GramAssembly.key 1765).leftCharge (GramAssembly.key 1765).rightCharge = raw41178 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41178Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41178 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1765).leftCharge (GramAssembly.key 1765).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1765, Integer.Sparse.eval]

theorem keyMoment1766 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1766) =
      Integer.Sparse.eval keyMomentRow1766 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1766).leftCharge (GramAssembly.key 1766).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 619) := by
    have ha : gramCharges (GramAssembly.key 1766).leftCharge (GramAssembly.key 1766).rightCharge = raw41179 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41179Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41179 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1766).leftCharge (GramAssembly.key 1766).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1766, Integer.Sparse.eval]

theorem keyMoment1767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1767) =
      Integer.Sparse.eval keyMomentRow1767 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1767).leftCharge (GramAssembly.key 1767).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2738) := by
    have ha : gramCharges (GramAssembly.key 1767).leftCharge (GramAssembly.key 1767).rightCharge = raw41180 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41180Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41180 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1767).leftCharge (GramAssembly.key 1767).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1767, Integer.Sparse.eval]

theorem keyMoment1768 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1768) =
      Integer.Sparse.eval keyMomentRow1768 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1768).leftCharge (GramAssembly.key 1768).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3050) := by
    have ha : gramCharges (GramAssembly.key 1768).leftCharge (GramAssembly.key 1768).rightCharge = raw41181 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41181Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41181 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1768).leftCharge (GramAssembly.key 1768).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1768, Integer.Sparse.eval]

theorem keyMoment1769 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1769) =
      Integer.Sparse.eval keyMomentRow1769 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1769).leftCharge (GramAssembly.key 1769).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3625) := by
    have ha : gramCharges (GramAssembly.key 1769).leftCharge (GramAssembly.key 1769).rightCharge = raw41182 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41182Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41182 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1769).leftCharge (GramAssembly.key 1769).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1769, Integer.Sparse.eval]

theorem keyMoment1770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1770) =
      Integer.Sparse.eval keyMomentRow1770 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1770).leftCharge (GramAssembly.key 1770).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3580) := by
    have ha : gramCharges (GramAssembly.key 1770).leftCharge (GramAssembly.key 1770).rightCharge = raw41183 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41183Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41183 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1770).leftCharge (GramAssembly.key 1770).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1770, Integer.Sparse.eval]

theorem keyMoment1771 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1771) =
      Integer.Sparse.eval keyMomentRow1771 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1771).leftCharge (GramAssembly.key 1771).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3073) := by
    have ha : gramCharges (GramAssembly.key 1771).leftCharge (GramAssembly.key 1771).rightCharge = raw41184 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41184Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41184 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1771).leftCharge (GramAssembly.key 1771).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1771, Integer.Sparse.eval]

theorem keyMoment1772 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1772) =
      Integer.Sparse.eval keyMomentRow1772 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1772).leftCharge (GramAssembly.key 1772).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3571) := by
    have ha : gramCharges (GramAssembly.key 1772).leftCharge (GramAssembly.key 1772).rightCharge = raw41185 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41185Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41185 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1772).leftCharge (GramAssembly.key 1772).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1772, Integer.Sparse.eval]

theorem keyMoment1773 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1773) =
      Integer.Sparse.eval keyMomentRow1773 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1773).leftCharge (GramAssembly.key 1773).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3388) := by
    have ha : gramCharges (GramAssembly.key 1773).leftCharge (GramAssembly.key 1773).rightCharge = raw41186 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41186Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41186 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1773).leftCharge (GramAssembly.key 1773).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1773, Integer.Sparse.eval]

theorem keyMoment1774 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1774) =
      Integer.Sparse.eval keyMomentRow1774 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1774).leftCharge (GramAssembly.key 1774).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3375) := by
    have ha : gramCharges (GramAssembly.key 1774).leftCharge (GramAssembly.key 1774).rightCharge = raw41187 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41187Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41187 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1774).leftCharge (GramAssembly.key 1774).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1774, Integer.Sparse.eval]

theorem keyMoment1775 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1775) =
      Integer.Sparse.eval keyMomentRow1775 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1775).leftCharge (GramAssembly.key 1775).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2781) := by
    have ha : gramCharges (GramAssembly.key 1775).leftCharge (GramAssembly.key 1775).rightCharge = raw41188 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41188Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41188 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1775).leftCharge (GramAssembly.key 1775).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1775, Integer.Sparse.eval]

theorem keyMoment1776 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1776) =
      Integer.Sparse.eval keyMomentRow1776 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1776).leftCharge (GramAssembly.key 1776).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3096) := by
    have ha : gramCharges (GramAssembly.key 1776).leftCharge (GramAssembly.key 1776).rightCharge = raw41189 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41189Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41189 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1776).leftCharge (GramAssembly.key 1776).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1776, Integer.Sparse.eval]

theorem keyMoment1777 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1777) =
      Integer.Sparse.eval keyMomentRow1777 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1777).leftCharge (GramAssembly.key 1777).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3572) := by
    have ha : gramCharges (GramAssembly.key 1777).leftCharge (GramAssembly.key 1777).rightCharge = raw41190 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41190Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41190 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1777).leftCharge (GramAssembly.key 1777).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1777, Integer.Sparse.eval]

theorem keyMoment1778 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1778) =
      Integer.Sparse.eval keyMomentRow1778 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1778).leftCharge (GramAssembly.key 1778).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3392) := by
    have ha : gramCharges (GramAssembly.key 1778).leftCharge (GramAssembly.key 1778).rightCharge = raw41191 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41191Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41191 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1778).leftCharge (GramAssembly.key 1778).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1778, Integer.Sparse.eval]

theorem keyMoment1779 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1779) =
      Integer.Sparse.eval keyMomentRow1779 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1779).leftCharge (GramAssembly.key 1779).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3376) := by
    have ha : gramCharges (GramAssembly.key 1779).leftCharge (GramAssembly.key 1779).rightCharge = raw41192 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41192Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41192 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1779).leftCharge (GramAssembly.key 1779).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1779, Integer.Sparse.eval]

theorem keyMoment1780 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1780) =
      Integer.Sparse.eval keyMomentRow1780 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1780).leftCharge (GramAssembly.key 1780).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2603) := by
    have ha : gramCharges (GramAssembly.key 1780).leftCharge (GramAssembly.key 1780).rightCharge = raw41193 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41193Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41193 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1780).leftCharge (GramAssembly.key 1780).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1780, Integer.Sparse.eval]

theorem keyMoment1781 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1781) =
      Integer.Sparse.eval keyMomentRow1781 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1781).leftCharge (GramAssembly.key 1781).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2560) := by
    have ha : gramCharges (GramAssembly.key 1781).leftCharge (GramAssembly.key 1781).rightCharge = raw41194 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41194Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41194 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1781).leftCharge (GramAssembly.key 1781).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1781, Integer.Sparse.eval]

theorem keyMoment1782 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1782) =
      Integer.Sparse.eval keyMomentRow1782 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1782).leftCharge (GramAssembly.key 1782).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3581) := by
    have ha : gramCharges (GramAssembly.key 1782).leftCharge (GramAssembly.key 1782).rightCharge = raw41195 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41195Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41195 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1782).leftCharge (GramAssembly.key 1782).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1782, Integer.Sparse.eval]

theorem keyMoment1783 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1783) =
      Integer.Sparse.eval keyMomentRow1783 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1783).leftCharge (GramAssembly.key 1783).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3391) := by
    have ha : gramCharges (GramAssembly.key 1783).leftCharge (GramAssembly.key 1783).rightCharge = raw41196 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41196Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41196 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1783).leftCharge (GramAssembly.key 1783).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1783, Integer.Sparse.eval]

theorem keyMoment1784 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1784) =
      Integer.Sparse.eval keyMomentRow1784 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1784).leftCharge (GramAssembly.key 1784).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3544) := by
    have ha : gramCharges (GramAssembly.key 1784).leftCharge (GramAssembly.key 1784).rightCharge = raw41197 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41197Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41197 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1784).leftCharge (GramAssembly.key 1784).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1784, Integer.Sparse.eval]

theorem keyMoment1785 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1785) =
      Integer.Sparse.eval keyMomentRow1785 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1785).leftCharge (GramAssembly.key 1785).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3622) := by
    have ha : gramCharges (GramAssembly.key 1785).leftCharge (GramAssembly.key 1785).rightCharge = raw41198 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41198Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41198 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1785).leftCharge (GramAssembly.key 1785).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1785, Integer.Sparse.eval]

theorem keyMoment1786 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1786) =
      Integer.Sparse.eval keyMomentRow1786 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1786).leftCharge (GramAssembly.key 1786).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3533) := by
    have ha : gramCharges (GramAssembly.key 1786).leftCharge (GramAssembly.key 1786).rightCharge = raw41199 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41199Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41199 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1786).leftCharge (GramAssembly.key 1786).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1786, Integer.Sparse.eval]

theorem keyMoment1787 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1787) =
      Integer.Sparse.eval keyMomentRow1787 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1787).leftCharge (GramAssembly.key 1787).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3390) := by
    have ha : gramCharges (GramAssembly.key 1787).leftCharge (GramAssembly.key 1787).rightCharge = raw41200 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41200Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41200 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1787).leftCharge (GramAssembly.key 1787).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1787, Integer.Sparse.eval]

theorem keyMoment1788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1788) =
      Integer.Sparse.eval keyMomentRow1788 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1788).leftCharge (GramAssembly.key 1788).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3532) := by
    have ha : gramCharges (GramAssembly.key 1788).leftCharge (GramAssembly.key 1788).rightCharge = raw41201 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41201Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41201 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1788).leftCharge (GramAssembly.key 1788).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1788, Integer.Sparse.eval]

theorem keyMoment1789 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1789) =
      Integer.Sparse.eval keyMomentRow1789 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1789).leftCharge (GramAssembly.key 1789).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3118) := by
    have ha : gramCharges (GramAssembly.key 1789).leftCharge (GramAssembly.key 1789).rightCharge = raw41202 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41202Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41202 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1789).leftCharge (GramAssembly.key 1789).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1789, Integer.Sparse.eval]

theorem keyMoment1790 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1790) =
      Integer.Sparse.eval keyMomentRow1790 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1790).leftCharge (GramAssembly.key 1790).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3380) := by
    have ha : gramCharges (GramAssembly.key 1790).leftCharge (GramAssembly.key 1790).rightCharge = raw41203 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41203Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41203 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1790).leftCharge (GramAssembly.key 1790).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1790, Integer.Sparse.eval]

theorem keyMoment1791 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1791) =
      Integer.Sparse.eval keyMomentRow1791 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1791).leftCharge (GramAssembly.key 1791).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3633) := by
    have ha : gramCharges (GramAssembly.key 1791).leftCharge (GramAssembly.key 1791).rightCharge = raw41204 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41204Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41204 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1791).leftCharge (GramAssembly.key 1791).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1791, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1760 : keyMomentRows (1760 : Fin 2886) =
    keyMomentRow1760 := by decide +kernel

theorem keyMomentRowsAt1761 : keyMomentRows (1761 : Fin 2886) =
    keyMomentRow1761 := by decide +kernel

theorem keyMomentRowsAt1762 : keyMomentRows (1762 : Fin 2886) =
    keyMomentRow1762 := by decide +kernel

theorem keyMomentRowsAt1763 : keyMomentRows (1763 : Fin 2886) =
    keyMomentRow1763 := by decide +kernel

theorem keyMomentRowsAt1764 : keyMomentRows (1764 : Fin 2886) =
    keyMomentRow1764 := by decide +kernel

theorem keyMomentRowsAt1765 : keyMomentRows (1765 : Fin 2886) =
    keyMomentRow1765 := by decide +kernel

theorem keyMomentRowsAt1766 : keyMomentRows (1766 : Fin 2886) =
    keyMomentRow1766 := by decide +kernel

theorem keyMomentRowsAt1767 : keyMomentRows (1767 : Fin 2886) =
    keyMomentRow1767 := by decide +kernel

theorem keyMomentRowsAt1768 : keyMomentRows (1768 : Fin 2886) =
    keyMomentRow1768 := by decide +kernel

theorem keyMomentRowsAt1769 : keyMomentRows (1769 : Fin 2886) =
    keyMomentRow1769 := by decide +kernel

theorem keyMomentRowsAt1770 : keyMomentRows (1770 : Fin 2886) =
    keyMomentRow1770 := by decide +kernel

theorem keyMomentRowsAt1771 : keyMomentRows (1771 : Fin 2886) =
    keyMomentRow1771 := by decide +kernel

theorem keyMomentRowsAt1772 : keyMomentRows (1772 : Fin 2886) =
    keyMomentRow1772 := by decide +kernel

theorem keyMomentRowsAt1773 : keyMomentRows (1773 : Fin 2886) =
    keyMomentRow1773 := by decide +kernel

theorem keyMomentRowsAt1774 : keyMomentRows (1774 : Fin 2886) =
    keyMomentRow1774 := by decide +kernel

theorem keyMomentRowsAt1775 : keyMomentRows (1775 : Fin 2886) =
    keyMomentRow1775 := by decide +kernel

theorem keyMomentRowsAt1776 : keyMomentRows (1776 : Fin 2886) =
    keyMomentRow1776 := by decide +kernel

theorem keyMomentRowsAt1777 : keyMomentRows (1777 : Fin 2886) =
    keyMomentRow1777 := by decide +kernel

theorem keyMomentRowsAt1778 : keyMomentRows (1778 : Fin 2886) =
    keyMomentRow1778 := by decide +kernel

theorem keyMomentRowsAt1779 : keyMomentRows (1779 : Fin 2886) =
    keyMomentRow1779 := by decide +kernel

theorem keyMomentRowsAt1780 : keyMomentRows (1780 : Fin 2886) =
    keyMomentRow1780 := by decide +kernel

theorem keyMomentRowsAt1781 : keyMomentRows (1781 : Fin 2886) =
    keyMomentRow1781 := by decide +kernel

theorem keyMomentRowsAt1782 : keyMomentRows (1782 : Fin 2886) =
    keyMomentRow1782 := by decide +kernel

theorem keyMomentRowsAt1783 : keyMomentRows (1783 : Fin 2886) =
    keyMomentRow1783 := by decide +kernel

theorem keyMomentRowsAt1784 : keyMomentRows (1784 : Fin 2886) =
    keyMomentRow1784 := by decide +kernel

theorem keyMomentRowsAt1785 : keyMomentRows (1785 : Fin 2886) =
    keyMomentRow1785 := by decide +kernel

theorem keyMomentRowsAt1786 : keyMomentRows (1786 : Fin 2886) =
    keyMomentRow1786 := by decide +kernel

theorem keyMomentRowsAt1787 : keyMomentRows (1787 : Fin 2886) =
    keyMomentRow1787 := by decide +kernel

theorem keyMomentRowsAt1788 : keyMomentRows (1788 : Fin 2886) =
    keyMomentRow1788 := by decide +kernel

theorem keyMomentRowsAt1789 : keyMomentRows (1789 : Fin 2886) =
    keyMomentRow1789 := by decide +kernel

theorem keyMomentRowsAt1790 : keyMomentRows (1790 : Fin 2886) =
    keyMomentRow1790 := by decide +kernel

theorem keyMomentRowsAt1791 : keyMomentRows (1791 : Fin 2886) =
    keyMomentRow1791 := by decide +kernel

theorem keyMomentChunkSound55_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 55) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1760 ∨ k.val = 1761 ∨ k.val = 1762 ∨ k.val = 1763 ∨ k.val = 1764 ∨ k.val = 1765 ∨ k.val = 1766 ∨ k.val = 1767 ∨ k.val = 1768 ∨ k.val = 1769 ∨ k.val = 1770 ∨ k.val = 1771 ∨ k.val = 1772 ∨ k.val = 1773 ∨ k.val = 1774 ∨ k.val = 1775 ∨ k.val = 1776 ∨ k.val = 1777 ∨ k.val = 1778 ∨ k.val = 1779 ∨ k.val = 1780 ∨ k.val = 1781 ∨ k.val = 1782 ∨ k.val = 1783 ∨ k.val = 1784 ∨ k.val = 1785 ∨ k.val = 1786 ∨ k.val = 1787 ∨ k.val = 1788 ∨ k.val = 1789 ∨ k.val = 1790 ∨ k.val = 1791 := by omega
  rcases heq with h1760 | h1761 | h1762 | h1763 | h1764 | h1765 | h1766 | h1767 | h1768 | h1769 | h1770 | h1771 | h1772 | h1773 | h1774 | h1775 | h1776 | h1777 | h1778 | h1779 | h1780 | h1781 | h1782 | h1783 | h1784 | h1785 | h1786 | h1787 | h1788 | h1789 | h1790 | h1791
  · have he : k = (1760 : Fin 2886) := Fin.ext h1760
    subst k
    rw [keyMomentRowsAt1760]
    exact keyMoment1760 B hB
  · have he : k = (1761 : Fin 2886) := Fin.ext h1761
    subst k
    rw [keyMomentRowsAt1761]
    exact keyMoment1761 B hB
  · have he : k = (1762 : Fin 2886) := Fin.ext h1762
    subst k
    rw [keyMomentRowsAt1762]
    exact keyMoment1762 B hB
  · have he : k = (1763 : Fin 2886) := Fin.ext h1763
    subst k
    rw [keyMomentRowsAt1763]
    exact keyMoment1763 B hB
  · have he : k = (1764 : Fin 2886) := Fin.ext h1764
    subst k
    rw [keyMomentRowsAt1764]
    exact keyMoment1764 B hB
  · have he : k = (1765 : Fin 2886) := Fin.ext h1765
    subst k
    rw [keyMomentRowsAt1765]
    exact keyMoment1765 B hB
  · have he : k = (1766 : Fin 2886) := Fin.ext h1766
    subst k
    rw [keyMomentRowsAt1766]
    exact keyMoment1766 B hB
  · have he : k = (1767 : Fin 2886) := Fin.ext h1767
    subst k
    rw [keyMomentRowsAt1767]
    exact keyMoment1767 B hB
  · have he : k = (1768 : Fin 2886) := Fin.ext h1768
    subst k
    rw [keyMomentRowsAt1768]
    exact keyMoment1768 B hB
  · have he : k = (1769 : Fin 2886) := Fin.ext h1769
    subst k
    rw [keyMomentRowsAt1769]
    exact keyMoment1769 B hB
  · have he : k = (1770 : Fin 2886) := Fin.ext h1770
    subst k
    rw [keyMomentRowsAt1770]
    exact keyMoment1770 B hB
  · have he : k = (1771 : Fin 2886) := Fin.ext h1771
    subst k
    rw [keyMomentRowsAt1771]
    exact keyMoment1771 B hB
  · have he : k = (1772 : Fin 2886) := Fin.ext h1772
    subst k
    rw [keyMomentRowsAt1772]
    exact keyMoment1772 B hB
  · have he : k = (1773 : Fin 2886) := Fin.ext h1773
    subst k
    rw [keyMomentRowsAt1773]
    exact keyMoment1773 B hB
  · have he : k = (1774 : Fin 2886) := Fin.ext h1774
    subst k
    rw [keyMomentRowsAt1774]
    exact keyMoment1774 B hB
  · have he : k = (1775 : Fin 2886) := Fin.ext h1775
    subst k
    rw [keyMomentRowsAt1775]
    exact keyMoment1775 B hB
  · have he : k = (1776 : Fin 2886) := Fin.ext h1776
    subst k
    rw [keyMomentRowsAt1776]
    exact keyMoment1776 B hB
  · have he : k = (1777 : Fin 2886) := Fin.ext h1777
    subst k
    rw [keyMomentRowsAt1777]
    exact keyMoment1777 B hB
  · have he : k = (1778 : Fin 2886) := Fin.ext h1778
    subst k
    rw [keyMomentRowsAt1778]
    exact keyMoment1778 B hB
  · have he : k = (1779 : Fin 2886) := Fin.ext h1779
    subst k
    rw [keyMomentRowsAt1779]
    exact keyMoment1779 B hB
  · have he : k = (1780 : Fin 2886) := Fin.ext h1780
    subst k
    rw [keyMomentRowsAt1780]
    exact keyMoment1780 B hB
  · have he : k = (1781 : Fin 2886) := Fin.ext h1781
    subst k
    rw [keyMomentRowsAt1781]
    exact keyMoment1781 B hB
  · have he : k = (1782 : Fin 2886) := Fin.ext h1782
    subst k
    rw [keyMomentRowsAt1782]
    exact keyMoment1782 B hB
  · have he : k = (1783 : Fin 2886) := Fin.ext h1783
    subst k
    rw [keyMomentRowsAt1783]
    exact keyMoment1783 B hB
  · have he : k = (1784 : Fin 2886) := Fin.ext h1784
    subst k
    rw [keyMomentRowsAt1784]
    exact keyMoment1784 B hB
  · have he : k = (1785 : Fin 2886) := Fin.ext h1785
    subst k
    rw [keyMomentRowsAt1785]
    exact keyMoment1785 B hB
  · have he : k = (1786 : Fin 2886) := Fin.ext h1786
    subst k
    rw [keyMomentRowsAt1786]
    exact keyMoment1786 B hB
  · have he : k = (1787 : Fin 2886) := Fin.ext h1787
    subst k
    rw [keyMomentRowsAt1787]
    exact keyMoment1787 B hB
  · have he : k = (1788 : Fin 2886) := Fin.ext h1788
    subst k
    rw [keyMomentRowsAt1788]
    exact keyMoment1788 B hB
  · have he : k = (1789 : Fin 2886) := Fin.ext h1789
    subst k
    rw [keyMomentRowsAt1789]
    exact keyMoment1789 B hB
  · have he : k = (1790 : Fin 2886) := Fin.ext h1790
    subst k
    rw [keyMomentRowsAt1790]
    exact keyMoment1790 B hB
  · have he : k = (1791 : Fin 2886) := Fin.ext h1791
    subst k
    rw [keyMomentRowsAt1791]
    exact keyMoment1791 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound55_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound55_e_oai
