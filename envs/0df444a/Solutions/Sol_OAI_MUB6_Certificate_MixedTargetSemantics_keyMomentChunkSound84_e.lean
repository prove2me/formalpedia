-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound84_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:05:57.981218+00:00
-- url     : https://prove2.me/submissions/eb50a37f-d721-4c76-8dd5-92a3435f7816

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E114
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

theorem rename_labels {p n l k : ℕ} (hk : k ≤ 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (small : Fin n → Fin l) (e : Fin l ↪ Fin k) (h : label = e ∘ small) :
    mixedMoment B A label = mixedMoment B A small := by
  rw [h]
  exact mixedMoment_label_embedding hk B A e small

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical333
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical42688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42688 raw42688Labels = mixedMoment B node3579 node3579Labels := by
  calc
    mixedMoment B raw42688 raw42688Labels = mixedMoment B raw42688step0 raw42688step0Labels := by
      have hz : ∀ j, raw42688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42688step0 = (fun i j => raw42688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42688step0 raw42688; decide +kernel
      have hl : raw42688step0Labels = raw42688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42688 raw42688Labels permutation434 hz
    mixedMoment B raw42688step0 raw42688step0Labels = mixedMoment B raw42688step1 raw42688step1Labels := by
      have hz : ∀ j, raw42688step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42688step1 = (fun i j => raw42688step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42688step1 raw42688step0; decide +kernel
      have hl : raw42688step1Labels = raw42688step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42688step0 raw42688step0Labels permutation80 hz
    mixedMoment B raw42688step1 raw42688step1Labels = mixedMoment B raw42688step2 raw42688step2Labels := by
      have ha : raw42688step2 = raw42688step1 := by apply Matrix.ext; unfold raw42688step2 raw42688step1; decide +kernel
      have hl : raw42688step1Labels = labelEmbedding1 ∘ raw42688step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42688step1 raw42688step1Labels raw42688step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3579 node3579Labels := by rfl

theorem canonical42689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42689 raw42689Labels = mixedMoment B node5201 node5201Labels := by
  calc
    mixedMoment B raw42689 raw42689Labels = mixedMoment B raw42689step0 raw42689step0Labels := by
      have hz : ∀ j, raw42689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42689step0 = (fun i j => raw42689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42689step0 raw42689; decide +kernel
      have hl : raw42689step0Labels = raw42689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42689 raw42689Labels permutation434 hz
    mixedMoment B raw42689step0 raw42689step0Labels = mixedMoment B raw42689step1 raw42689step1Labels := by
      have hz : ∀ j, raw42689step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42689step1 = (fun i j => raw42689step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42689step1 raw42689step0; decide +kernel
      have hl : raw42689step1Labels = raw42689step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42689step0 raw42689step0Labels permutation80 hz
    mixedMoment B raw42689step1 raw42689step1Labels = mixedMoment B raw42689step2 raw42689step2Labels := by
      have ha : raw42689step2 = (fun i j => raw42689step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42689step2 raw42689step1; decide +kernel
      have hl : raw42689step2Labels = raw42689step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42689step1 raw42689step1Labels permutation29 permutation7
    mixedMoment B raw42689step2 raw42689step2Labels = mixedMoment B raw42689step3 raw42689step3Labels := by
      have ha : raw42689step3 = raw42689step2 := by apply Matrix.ext; unfold raw42689step3 raw42689step2; decide +kernel
      have hl : raw42689step2Labels = labelEmbedding6 ∘ raw42689step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42689step2 raw42689step2Labels raw42689step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5201 node5201Labels := by rfl

theorem canonical42690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42690 raw42690Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw42690 raw42690Labels = mixedMoment B raw42690step0 raw42690step0Labels := by
      have hz : ∀ j, raw42690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42690step0 = (fun i j => raw42690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42690step0 raw42690; decide +kernel
      have hl : raw42690step0Labels = raw42690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42690 raw42690Labels permutation346 hz
    mixedMoment B raw42690step0 raw42690step0Labels = mixedMoment B raw42690step1 raw42690step1Labels := by
      have ha : raw42690step1 = (fun i j => raw42690step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42690step1 raw42690step0; decide +kernel
      have hl : raw42690step1Labels = raw42690step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42690step0 raw42690step0Labels permutation151 permutation2
    mixedMoment B raw42690step1 raw42690step1Labels = mixedMoment B raw42690step2 raw42690step2Labels := by
      have ha : raw42690step2 = -raw42690step1 := by apply Matrix.ext; change ∀ i j, raw42690step2 i j = -(raw42690step1 i j); unfold raw42690step2 raw42690step1; decide +kernel
      have hl : raw42690step2Labels = raw42690step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42690step2 raw42690step2Labels = mixedMoment B raw42690step3 raw42690step3Labels := by
      have ha : raw42690step3 = raw42690step2 := by apply Matrix.ext; unfold raw42690step3 raw42690step2; decide +kernel
      have hl : raw42690step2Labels = labelEmbedding1 ∘ raw42690step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42690step2 raw42690step2Labels raw42690step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

theorem canonical42691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42691 raw42691Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw42691 raw42691Labels = mixedMoment B raw42691step0 raw42691step0Labels := by
      have hz : ∀ j, raw42691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42691step0 = (fun i j => raw42691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42691step0 raw42691; decide +kernel
      have hl : raw42691step0Labels = raw42691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42691 raw42691Labels permutation346 hz
    mixedMoment B raw42691step0 raw42691step0Labels = mixedMoment B raw42691step1 raw42691step1Labels := by
      have ha : raw42691step1 = (fun i j => raw42691step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42691step1 raw42691step0; decide +kernel
      have hl : raw42691step1Labels = raw42691step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42691step0 raw42691step0Labels permutation40 permutation7
    mixedMoment B raw42691step1 raw42691step1Labels = mixedMoment B raw42691step2 raw42691step2Labels := by
      have ha : raw42691step2 = -raw42691step1 := by apply Matrix.ext; change ∀ i j, raw42691step2 i j = -(raw42691step1 i j); unfold raw42691step2 raw42691step1; decide +kernel
      have hl : raw42691step2Labels = raw42691step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42691step2 raw42691step2Labels = mixedMoment B raw42691step3 raw42691step3Labels := by
      have ha : raw42691step3 = raw42691step2 := by apply Matrix.ext; unfold raw42691step3 raw42691step2; decide +kernel
      have hl : raw42691step2Labels = labelEmbedding6 ∘ raw42691step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42691step2 raw42691step2Labels raw42691step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

theorem canonical42692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42692 raw42692Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw42692 raw42692Labels = mixedMoment B raw42692step0 raw42692step0Labels := by
      have hz : ∀ j, raw42692 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42692step0 = (fun i j => raw42692 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42692step0 raw42692; decide +kernel
      have hl : raw42692step0Labels = raw42692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42692 raw42692Labels permutation346 hz
    mixedMoment B raw42692step0 raw42692step0Labels = mixedMoment B raw42692step1 raw42692step1Labels := by
      have ha : raw42692step1 = (fun i j => raw42692step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42692step1 raw42692step0; decide +kernel
      have hl : raw42692step1Labels = raw42692step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42692step0 raw42692step0Labels permutation37 permutation2
    mixedMoment B raw42692step1 raw42692step1Labels = mixedMoment B raw42692step2 raw42692step2Labels := by
      have ha : raw42692step2 = raw42692step1 := by apply Matrix.ext; unfold raw42692step2 raw42692step1; decide +kernel
      have hl : raw42692step1Labels = labelEmbedding1 ∘ raw42692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42692step1 raw42692step1Labels raw42692step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

theorem canonical42693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42693 raw42693Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw42693 raw42693Labels = mixedMoment B raw42693step0 raw42693step0Labels := by
      have hz : ∀ j, raw42693 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42693step0 = (fun i j => raw42693 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42693step0 raw42693; decide +kernel
      have hl : raw42693step0Labels = raw42693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42693 raw42693Labels permutation346 hz
    mixedMoment B raw42693step0 raw42693step0Labels = mixedMoment B raw42693step1 raw42693step1Labels := by
      have ha : raw42693step1 = (fun i j => raw42693step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42693step1 raw42693step0; decide +kernel
      have hl : raw42693step1Labels = raw42693step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42693step0 raw42693step0Labels permutation51 permutation7
    mixedMoment B raw42693step1 raw42693step1Labels = mixedMoment B raw42693step2 raw42693step2Labels := by
      have ha : raw42693step2 = -raw42693step1 := by apply Matrix.ext; change ∀ i j, raw42693step2 i j = -(raw42693step1 i j); unfold raw42693step2 raw42693step1; decide +kernel
      have hl : raw42693step2Labels = raw42693step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42693step2 raw42693step2Labels = mixedMoment B raw42693step3 raw42693step3Labels := by
      have ha : raw42693step3 = raw42693step2 := by apply Matrix.ext; unfold raw42693step3 raw42693step2; decide +kernel
      have hl : raw42693step2Labels = labelEmbedding6 ∘ raw42693step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42693step2 raw42693step2Labels raw42693step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

theorem canonical42694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42694 raw42694Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw42694 raw42694Labels = mixedMoment B raw42694step0 raw42694step0Labels := by
      have hz : ∀ j, raw42694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42694step0 = (fun i j => raw42694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42694step0 raw42694; decide +kernel
      have hl : raw42694step0Labels = raw42694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42694 raw42694Labels permutation346 hz
    mixedMoment B raw42694step0 raw42694step0Labels = mixedMoment B raw42694step1 raw42694step1Labels := by
      have ha : raw42694step1 = (fun i j => raw42694step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42694step1 raw42694step0; decide +kernel
      have hl : raw42694step1Labels = raw42694step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42694step0 raw42694step0Labels permutation35 permutation2
    mixedMoment B raw42694step1 raw42694step1Labels = mixedMoment B raw42694step2 raw42694step2Labels := by
      have ha : raw42694step2 = raw42694step1 := by apply Matrix.ext; unfold raw42694step2 raw42694step1; decide +kernel
      have hl : raw42694step1Labels = labelEmbedding1 ∘ raw42694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42694step1 raw42694step1Labels raw42694step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

theorem canonical42695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42695 raw42695Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw42695 raw42695Labels = mixedMoment B raw42695step0 raw42695step0Labels := by
      have hz : ∀ j, raw42695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42695step0 = (fun i j => raw42695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42695step0 raw42695; decide +kernel
      have hl : raw42695step0Labels = raw42695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42695 raw42695Labels permutation346 hz
    mixedMoment B raw42695step0 raw42695step0Labels = mixedMoment B raw42695step1 raw42695step1Labels := by
      have ha : raw42695step1 = (fun i j => raw42695step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42695step1 raw42695step0; decide +kernel
      have hl : raw42695step1Labels = raw42695step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42695step0 raw42695step0Labels permutation48 permutation7
    mixedMoment B raw42695step1 raw42695step1Labels = mixedMoment B raw42695step2 raw42695step2Labels := by
      have ha : raw42695step2 = -raw42695step1 := by apply Matrix.ext; change ∀ i j, raw42695step2 i j = -(raw42695step1 i j); unfold raw42695step2 raw42695step1; decide +kernel
      have hl : raw42695step2Labels = raw42695step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42695step2 raw42695step2Labels = mixedMoment B raw42695step3 raw42695step3Labels := by
      have ha : raw42695step3 = raw42695step2 := by apply Matrix.ext; unfold raw42695step3 raw42695step2; decide +kernel
      have hl : raw42695step2Labels = labelEmbedding6 ∘ raw42695step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42695step2 raw42695step2Labels raw42695step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

theorem canonical42696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42696 raw42696Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw42696 raw42696Labels = mixedMoment B raw42696step0 raw42696step0Labels := by
      have ha : raw42696step0 = (fun i j => raw42696 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42696step0 raw42696; decide +kernel
      have hl : raw42696step0Labels = raw42696Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42696 raw42696Labels permutation157 permutation2
    mixedMoment B raw42696step0 raw42696step0Labels = mixedMoment B raw42696step1 raw42696step1Labels := by
      have ha : raw42696step1 = raw42696step0 := by apply Matrix.ext; unfold raw42696step1 raw42696step0; decide +kernel
      have hl : raw42696step0Labels = labelEmbedding1 ∘ raw42696step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42696step0 raw42696step0Labels raw42696step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

theorem canonical42697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42697 raw42697Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw42697 raw42697Labels = mixedMoment B raw42697step0 raw42697step0Labels := by
      have ha : raw42697step0 = (fun i j => raw42697 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42697step0 raw42697; decide +kernel
      have hl : raw42697step0Labels = raw42697Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42697 raw42697Labels permutation195 permutation7
    mixedMoment B raw42697step0 raw42697step0Labels = mixedMoment B raw42697step1 raw42697step1Labels := by
      have ha : raw42697step1 = -raw42697step0 := by apply Matrix.ext; change ∀ i j, raw42697step1 i j = -(raw42697step0 i j); unfold raw42697step1 raw42697step0; decide +kernel
      have hl : raw42697step1Labels = raw42697step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42697step1 raw42697step1Labels = mixedMoment B raw42697step2 raw42697step2Labels := by
      have ha : raw42697step2 = raw42697step1 := by apply Matrix.ext; unfold raw42697step2 raw42697step1; decide +kernel
      have hl : raw42697step1Labels = labelEmbedding6 ∘ raw42697step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42697step1 raw42697step1Labels raw42697step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

theorem canonical42698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42698 raw42698Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw42698 raw42698Labels = mixedMoment B raw42698step0 raw42698step0Labels := by
      have hz : ∀ j, raw42698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42698step0 = (fun i j => raw42698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42698step0 raw42698; decide +kernel
      have hl : raw42698step0Labels = raw42698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42698 raw42698Labels permutation434 hz
    mixedMoment B raw42698step0 raw42698step0Labels = mixedMoment B raw42698step1 raw42698step1Labels := by
      have ha : raw42698step1 = raw42698step0 := by apply Matrix.ext; unfold raw42698step1 raw42698step0; decide +kernel
      have hl : raw42698step0Labels = labelEmbedding1 ∘ raw42698step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42698step0 raw42698step0Labels raw42698step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical42699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42699 raw42699Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw42699 raw42699Labels = mixedMoment B raw42699step0 raw42699step0Labels := by
      have hz : ∀ j, raw42699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42699step0 = (fun i j => raw42699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42699step0 raw42699; decide +kernel
      have hl : raw42699step0Labels = raw42699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42699 raw42699Labels permutation434 hz
    mixedMoment B raw42699step0 raw42699step0Labels = mixedMoment B raw42699step1 raw42699step1Labels := by
      have ha : raw42699step1 = (fun i j => raw42699step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42699step1 raw42699step0; decide +kernel
      have hl : raw42699step1Labels = raw42699step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42699step0 raw42699step0Labels permutation37 permutation7
    mixedMoment B raw42699step1 raw42699step1Labels = mixedMoment B raw42699step2 raw42699step2Labels := by
      have ha : raw42699step2 = -raw42699step1 := by apply Matrix.ext; change ∀ i j, raw42699step2 i j = -(raw42699step1 i j); unfold raw42699step2 raw42699step1; decide +kernel
      have hl : raw42699step2Labels = raw42699step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42699step2 raw42699step2Labels = mixedMoment B raw42699step3 raw42699step3Labels := by
      have ha : raw42699step3 = raw42699step2 := by apply Matrix.ext; unfold raw42699step3 raw42699step2; decide +kernel
      have hl : raw42699step2Labels = labelEmbedding6 ∘ raw42699step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42699step2 raw42699step2Labels raw42699step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

theorem canonical42700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42700 raw42700Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw42700 raw42700Labels = mixedMoment B raw42700step0 raw42700step0Labels := by
      have hz : ∀ j, raw42700 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42700step0 = (fun i j => raw42700 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42700step0 raw42700; decide +kernel
      have hl : raw42700step0Labels = raw42700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42700 raw42700Labels permutation434 hz
    mixedMoment B raw42700step0 raw42700step0Labels = mixedMoment B raw42700step1 raw42700step1Labels := by
      have ha : raw42700step1 = raw42700step0 := by apply Matrix.ext; unfold raw42700step1 raw42700step0; decide +kernel
      have hl : raw42700step0Labels = labelEmbedding1 ∘ raw42700step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42700step0 raw42700step0Labels raw42700step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

theorem canonical42701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42701 raw42701Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw42701 raw42701Labels = mixedMoment B raw42701step0 raw42701step0Labels := by
      have hz : ∀ j, raw42701 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42701step0 = (fun i j => raw42701 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42701step0 raw42701; decide +kernel
      have hl : raw42701step0Labels = raw42701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42701 raw42701Labels permutation434 hz
    mixedMoment B raw42701step0 raw42701step0Labels = mixedMoment B raw42701step1 raw42701step1Labels := by
      have ha : raw42701step1 = (fun i j => raw42701step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42701step1 raw42701step0; decide +kernel
      have hl : raw42701step1Labels = raw42701step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42701step0 raw42701step0Labels permutation35 permutation7
    mixedMoment B raw42701step1 raw42701step1Labels = mixedMoment B raw42701step2 raw42701step2Labels := by
      have ha : raw42701step2 = -raw42701step1 := by apply Matrix.ext; change ∀ i j, raw42701step2 i j = -(raw42701step1 i j); unfold raw42701step2 raw42701step1; decide +kernel
      have hl : raw42701step2Labels = raw42701step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42701step2 raw42701step2Labels = mixedMoment B raw42701step3 raw42701step3Labels := by
      have ha : raw42701step3 = raw42701step2 := by apply Matrix.ext; unfold raw42701step3 raw42701step2; decide +kernel
      have hl : raw42701step2Labels = labelEmbedding6 ∘ raw42701step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42701step2 raw42701step2Labels raw42701step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

theorem canonical42702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42702 raw42702Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw42702 raw42702Labels = mixedMoment B raw42702step0 raw42702step0Labels := by
      have hz : ∀ j, raw42702 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42702step0 = (fun i j => raw42702 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42702step0 raw42702; decide +kernel
      have hl : raw42702step0Labels = raw42702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42702 raw42702Labels permutation434 hz
    mixedMoment B raw42702step0 raw42702step0Labels = mixedMoment B raw42702step1 raw42702step1Labels := by
      have ha : raw42702step1 = raw42702step0 := by apply Matrix.ext; unfold raw42702step1 raw42702step0; decide +kernel
      have hl : raw42702step0Labels = labelEmbedding1 ∘ raw42702step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42702step0 raw42702step0Labels raw42702step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

theorem canonical42703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42703 raw42703Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw42703 raw42703Labels = mixedMoment B raw42703step0 raw42703step0Labels := by
      have hz : ∀ j, raw42703 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42703step0 = (fun i j => raw42703 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42703step0 raw42703; decide +kernel
      have hl : raw42703step0Labels = raw42703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42703 raw42703Labels permutation434 hz
    mixedMoment B raw42703step0 raw42703step0Labels = mixedMoment B raw42703step1 raw42703step1Labels := by
      have ha : raw42703step1 = (fun i j => raw42703step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42703step1 raw42703step0; decide +kernel
      have hl : raw42703step1Labels = raw42703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42703step0 raw42703step0Labels permutation44 permutation7
    mixedMoment B raw42703step1 raw42703step1Labels = mixedMoment B raw42703step2 raw42703step2Labels := by
      have ha : raw42703step2 = -raw42703step1 := by apply Matrix.ext; change ∀ i j, raw42703step2 i j = -(raw42703step1 i j); unfold raw42703step2 raw42703step1; decide +kernel
      have hl : raw42703step2Labels = raw42703step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42703step2 raw42703step2Labels = mixedMoment B raw42703step3 raw42703step3Labels := by
      have ha : raw42703step3 = raw42703step2 := by apply Matrix.ext; unfold raw42703step3 raw42703step2; decide +kernel
      have hl : raw42703step2Labels = labelEmbedding6 ∘ raw42703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42703step2 raw42703step2Labels raw42703step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

theorem canonical42704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42704 raw42704Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw42704 raw42704Labels = mixedMoment B raw42704step0 raw42704step0Labels := by
      have ha : raw42704step0 = (fun i j => raw42704 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42704step0 raw42704; decide +kernel
      have hl : raw42704step0Labels = raw42704Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42704 raw42704Labels permutation158 permutation2
    mixedMoment B raw42704step0 raw42704step0Labels = mixedMoment B raw42704step1 raw42704step1Labels := by
      have ha : raw42704step1 = raw42704step0 := by apply Matrix.ext; unfold raw42704step1 raw42704step0; decide +kernel
      have hl : raw42704step0Labels = labelEmbedding1 ∘ raw42704step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42704step0 raw42704step0Labels raw42704step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical42705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42705 raw42705Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw42705 raw42705Labels = mixedMoment B raw42705step0 raw42705step0Labels := by
      have ha : raw42705step0 = (fun i j => raw42705 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42705step0 raw42705; decide +kernel
      have hl : raw42705step0Labels = raw42705Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42705 raw42705Labels permutation202 permutation7
    mixedMoment B raw42705step0 raw42705step0Labels = mixedMoment B raw42705step1 raw42705step1Labels := by
      have ha : raw42705step1 = -raw42705step0 := by apply Matrix.ext; change ∀ i j, raw42705step1 i j = -(raw42705step0 i j); unfold raw42705step1 raw42705step0; decide +kernel
      have hl : raw42705step1Labels = raw42705step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42705step1 raw42705step1Labels = mixedMoment B raw42705step2 raw42705step2Labels := by
      have ha : raw42705step2 = raw42705step1 := by apply Matrix.ext; unfold raw42705step2 raw42705step1; decide +kernel
      have hl : raw42705step1Labels = labelEmbedding6 ∘ raw42705step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42705step1 raw42705step1Labels raw42705step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

theorem canonical42706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42706 raw42706Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw42706 raw42706Labels = mixedMoment B raw42706step0 raw42706step0Labels := by
      have ha : raw42706step0 = (fun i j => raw42706 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42706step0 raw42706; decide +kernel
      have hl : raw42706step0Labels = raw42706Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42706 raw42706Labels permutation156 permutation2
    mixedMoment B raw42706step0 raw42706step0Labels = mixedMoment B raw42706step1 raw42706step1Labels := by
      have ha : raw42706step1 = raw42706step0 := by apply Matrix.ext; unfold raw42706step1 raw42706step0; decide +kernel
      have hl : raw42706step0Labels = labelEmbedding1 ∘ raw42706step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42706step0 raw42706step0Labels raw42706step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

theorem canonical42707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42707 raw42707Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw42707 raw42707Labels = mixedMoment B raw42707step0 raw42707step0Labels := by
      have ha : raw42707step0 = (fun i j => raw42707 (permutation249 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42707step0 raw42707; decide +kernel
      have hl : raw42707step0Labels = raw42707Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42707 raw42707Labels permutation249 permutation7
    mixedMoment B raw42707step0 raw42707step0Labels = mixedMoment B raw42707step1 raw42707step1Labels := by
      have ha : raw42707step1 = -raw42707step0 := by apply Matrix.ext; change ∀ i j, raw42707step1 i j = -(raw42707step0 i j); unfold raw42707step1 raw42707step0; decide +kernel
      have hl : raw42707step1Labels = raw42707step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42707step1 raw42707step1Labels = mixedMoment B raw42707step2 raw42707step2Labels := by
      have ha : raw42707step2 = raw42707step1 := by apply Matrix.ext; unfold raw42707step2 raw42707step1; decide +kernel
      have hl : raw42707step1Labels = labelEmbedding6 ∘ raw42707step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42707step1 raw42707step1Labels raw42707step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5187 node5187Labels := by rfl

theorem canonical42708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42708 raw42708Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw42708 raw42708Labels = mixedMoment B raw42708step0 raw42708step0Labels := by
      have ha : raw42708step0 = (fun i j => raw42708 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42708step0 raw42708; decide +kernel
      have hl : raw42708step0Labels = raw42708Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42708 raw42708Labels permutation155 permutation2
    mixedMoment B raw42708step0 raw42708step0Labels = mixedMoment B raw42708step1 raw42708step1Labels := by
      have ha : raw42708step1 = raw42708step0 := by apply Matrix.ext; unfold raw42708step1 raw42708step0; decide +kernel
      have hl : raw42708step0Labels = labelEmbedding1 ∘ raw42708step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42708step0 raw42708step0Labels raw42708step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

theorem canonical42709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42709 raw42709Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw42709 raw42709Labels = mixedMoment B raw42709step0 raw42709step0Labels := by
      have ha : raw42709step0 = (fun i j => raw42709 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42709step0 raw42709; decide +kernel
      have hl : raw42709step0Labels = raw42709Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42709 raw42709Labels permutation169 permutation7
    mixedMoment B raw42709step0 raw42709step0Labels = mixedMoment B raw42709step1 raw42709step1Labels := by
      have ha : raw42709step1 = -raw42709step0 := by apply Matrix.ext; change ∀ i j, raw42709step1 i j = -(raw42709step0 i j); unfold raw42709step1 raw42709step0; decide +kernel
      have hl : raw42709step1Labels = raw42709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42709step1 raw42709step1Labels = mixedMoment B raw42709step2 raw42709step2Labels := by
      have ha : raw42709step2 = raw42709step1 := by apply Matrix.ext; unfold raw42709step2 raw42709step1; decide +kernel
      have hl : raw42709step1Labels = labelEmbedding6 ∘ raw42709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42709step1 raw42709step1Labels raw42709step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical42710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42710 raw42710Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw42710 raw42710Labels = mixedMoment B raw42710step0 raw42710step0Labels := by
      have ha : raw42710step0 = raw42710 := by apply Matrix.ext; unfold raw42710step0 raw42710; decide +kernel
      have hl : raw42710Labels = labelEmbedding1 ∘ raw42710step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42710 raw42710Labels raw42710step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

theorem canonical42711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42711 raw42711Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw42711 raw42711Labels = mixedMoment B raw42711step0 raw42711step0Labels := by
      have ha : raw42711step0 = (fun i j => raw42711 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42711step0 raw42711; decide +kernel
      have hl : raw42711step0Labels = raw42711Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42711 raw42711Labels permutation170 permutation7
    mixedMoment B raw42711step0 raw42711step0Labels = mixedMoment B raw42711step1 raw42711step1Labels := by
      have ha : raw42711step1 = -raw42711step0 := by apply Matrix.ext; change ∀ i j, raw42711step1 i j = -(raw42711step0 i j); unfold raw42711step1 raw42711step0; decide +kernel
      have hl : raw42711step1Labels = raw42711step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42711step1 raw42711step1Labels = mixedMoment B raw42711step2 raw42711step2Labels := by
      have ha : raw42711step2 = raw42711step1 := by apply Matrix.ext; unfold raw42711step2 raw42711step1; decide +kernel
      have hl : raw42711step1Labels = labelEmbedding6 ∘ raw42711step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42711step1 raw42711step1Labels raw42711step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical42712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42712 raw42712Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw42712 raw42712Labels = mixedMoment B raw42712step0 raw42712step0Labels := by
      have ha : raw42712step0 = raw42712 := by apply Matrix.ext; unfold raw42712step0 raw42712; decide +kernel
      have hl : raw42712Labels = labelEmbedding1 ∘ raw42712step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42712 raw42712Labels raw42712step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

theorem canonical42713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42713 raw42713Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw42713 raw42713Labels = mixedMoment B raw42713step0 raw42713step0Labels := by
      have ha : raw42713step0 = (fun i j => raw42713 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42713step0 raw42713; decide +kernel
      have hl : raw42713step0Labels = raw42713Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42713 raw42713Labels permutation224 permutation7
    mixedMoment B raw42713step0 raw42713step0Labels = mixedMoment B raw42713step1 raw42713step1Labels := by
      have ha : raw42713step1 = -raw42713step0 := by apply Matrix.ext; change ∀ i j, raw42713step1 i j = -(raw42713step0 i j); unfold raw42713step1 raw42713step0; decide +kernel
      have hl : raw42713step1Labels = raw42713step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42713step1 raw42713step1Labels = mixedMoment B raw42713step2 raw42713step2Labels := by
      have ha : raw42713step2 = raw42713step1 := by apply Matrix.ext; unfold raw42713step2 raw42713step1; decide +kernel
      have hl : raw42713step1Labels = labelEmbedding6 ∘ raw42713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42713step1 raw42713step1Labels raw42713step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5184 node5184Labels := by rfl

theorem canonical42714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42714 raw42714Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw42714 raw42714Labels = mixedMoment B raw42714step0 raw42714step0Labels := by
      have hz : ∀ j, raw42714 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42714step0 = (fun i j => raw42714 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42714step0 raw42714; decide +kernel
      have hl : raw42714step0Labels = raw42714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42714 raw42714Labels permutation434 hz
    mixedMoment B raw42714step0 raw42714step0Labels = mixedMoment B raw42714step1 raw42714step1Labels := by
      have ha : raw42714step1 = raw42714step0 := by apply Matrix.ext; unfold raw42714step1 raw42714step0; decide +kernel
      have hl : raw42714step0Labels = labelEmbedding1 ∘ raw42714step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42714step0 raw42714step0Labels raw42714step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

theorem canonical42715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42715 raw42715Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw42715 raw42715Labels = mixedMoment B raw42715step0 raw42715step0Labels := by
      have hz : ∀ j, raw42715 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42715step0 = (fun i j => raw42715 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42715step0 raw42715; decide +kernel
      have hl : raw42715step0Labels = raw42715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42715 raw42715Labels permutation434 hz
    mixedMoment B raw42715step0 raw42715step0Labels = mixedMoment B raw42715step1 raw42715step1Labels := by
      have ha : raw42715step1 = (fun i j => raw42715step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42715step1 raw42715step0; decide +kernel
      have hl : raw42715step1Labels = raw42715step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42715step0 raw42715step0Labels permutation36 permutation7
    mixedMoment B raw42715step1 raw42715step1Labels = mixedMoment B raw42715step2 raw42715step2Labels := by
      have ha : raw42715step2 = -raw42715step1 := by apply Matrix.ext; change ∀ i j, raw42715step2 i j = -(raw42715step1 i j); unfold raw42715step2 raw42715step1; decide +kernel
      have hl : raw42715step2Labels = raw42715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42715step2 raw42715step2Labels = mixedMoment B raw42715step3 raw42715step3Labels := by
      have ha : raw42715step3 = raw42715step2 := by apply Matrix.ext; unfold raw42715step3 raw42715step2; decide +kernel
      have hl : raw42715step2Labels = labelEmbedding6 ∘ raw42715step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42715step2 raw42715step2Labels raw42715step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical42716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42716 raw42716Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw42716 raw42716Labels = mixedMoment B raw42716step0 raw42716step0Labels := by
      have hz : ∀ j, raw42716 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42716step0 = (fun i j => raw42716 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42716step0 raw42716; decide +kernel
      have hl : raw42716step0Labels = raw42716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42716 raw42716Labels permutation434 hz
    mixedMoment B raw42716step0 raw42716step0Labels = mixedMoment B raw42716step1 raw42716step1Labels := by
      have ha : raw42716step1 = raw42716step0 := by apply Matrix.ext; unfold raw42716step1 raw42716step0; decide +kernel
      have hl : raw42716step0Labels = labelEmbedding1 ∘ raw42716step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42716step0 raw42716step0Labels raw42716step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

theorem canonical42717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42717 raw42717Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw42717 raw42717Labels = mixedMoment B raw42717step0 raw42717step0Labels := by
      have hz : ∀ j, raw42717 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42717step0 = (fun i j => raw42717 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42717step0 raw42717; decide +kernel
      have hl : raw42717step0Labels = raw42717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42717 raw42717Labels permutation434 hz
    mixedMoment B raw42717step0 raw42717step0Labels = mixedMoment B raw42717step1 raw42717step1Labels := by
      have ha : raw42717step1 = (fun i j => raw42717step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42717step1 raw42717step0; decide +kernel
      have hl : raw42717step1Labels = raw42717step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42717step0 raw42717step0Labels permutation143 permutation7
    mixedMoment B raw42717step1 raw42717step1Labels = mixedMoment B raw42717step2 raw42717step2Labels := by
      have ha : raw42717step2 = raw42717step1 := by apply Matrix.ext; unfold raw42717step2 raw42717step1; decide +kernel
      have hl : raw42717step1Labels = labelEmbedding6 ∘ raw42717step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42717step1 raw42717step1Labels raw42717step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

theorem canonical42718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42718 raw42718Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw42718 raw42718Labels = mixedMoment B raw42718step0 raw42718step0Labels := by
      have hz : ∀ j, raw42718 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42718step0 = (fun i j => raw42718 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42718step0 raw42718; decide +kernel
      have hl : raw42718step0Labels = raw42718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42718 raw42718Labels permutation434 hz
    mixedMoment B raw42718step0 raw42718step0Labels = mixedMoment B raw42718step1 raw42718step1Labels := by
      have hz : ∀ j, raw42718step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42718step1 = (fun i j => raw42718step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42718step1 raw42718step0; decide +kernel
      have hl : raw42718step1Labels = raw42718step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42718step0 raw42718step0Labels permutation80 hz
    mixedMoment B raw42718step1 raw42718step1Labels = mixedMoment B raw42718step2 raw42718step2Labels := by
      have ha : raw42718step2 = raw42718step1 := by apply Matrix.ext; unfold raw42718step2 raw42718step1; decide +kernel
      have hl : raw42718step1Labels = labelEmbedding1 ∘ raw42718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42718step1 raw42718step1Labels raw42718step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3549 node3549Labels := by rfl

theorem canonical42719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42719 raw42719Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw42719 raw42719Labels = mixedMoment B raw42719step0 raw42719step0Labels := by
      have hz : ∀ j, raw42719 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42719step0 = (fun i j => raw42719 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42719step0 raw42719; decide +kernel
      have hl : raw42719step0Labels = raw42719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42719 raw42719Labels permutation434 hz
    mixedMoment B raw42719step0 raw42719step0Labels = mixedMoment B raw42719step1 raw42719step1Labels := by
      have hz : ∀ j, raw42719step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42719step1 = (fun i j => raw42719step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42719step1 raw42719step0; decide +kernel
      have hl : raw42719step1Labels = raw42719step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42719step0 raw42719step0Labels permutation80 hz
    mixedMoment B raw42719step1 raw42719step1Labels = mixedMoment B raw42719step2 raw42719step2Labels := by
      have ha : raw42719step2 = (fun i j => raw42719step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42719step2 raw42719step1; decide +kernel
      have hl : raw42719step2Labels = raw42719step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42719step1 raw42719step1Labels permutation23 permutation6
    _ = mixedMoment B node5268 node5268Labels := by rfl

theorem canonical42720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42720 raw42720Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw42720 raw42720Labels = mixedMoment B raw42720step0 raw42720step0Labels := by
      have hz : ∀ j, raw42720 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42720step0 = (fun i j => raw42720 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42720step0 raw42720; decide +kernel
      have hl : raw42720step0Labels = raw42720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42720 raw42720Labels permutation434 hz
    mixedMoment B raw42720step0 raw42720step0Labels = mixedMoment B raw42720step1 raw42720step1Labels := by
      have hz : ∀ j, raw42720step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42720step1 = (fun i j => raw42720step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42720step1 raw42720step0; decide +kernel
      have hl : raw42720step1Labels = raw42720step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42720step0 raw42720step0Labels permutation80 hz
    mixedMoment B raw42720step1 raw42720step1Labels = mixedMoment B raw42720step2 raw42720step2Labels := by
      have ha : raw42720step2 = (fun i j => raw42720step1 (permutation28 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42720step2 raw42720step1; decide +kernel
      have hl : raw42720step2Labels = raw42720step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42720step1 raw42720step1Labels permutation28 permutation4
    mixedMoment B raw42720step2 raw42720step2Labels = mixedMoment B raw42720step3 raw42720step3Labels := by
      have ha : raw42720step3 = -raw42720step2 := by apply Matrix.ext; change ∀ i j, raw42720step3 i j = -(raw42720step2 i j); unfold raw42720step3 raw42720step2; decide +kernel
      have hl : raw42720step3Labels = raw42720step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42720step3 raw42720step3Labels = mixedMoment B raw42720step4 raw42720step4Labels := by
      have ha : raw42720step4 = raw42720step3 := by apply Matrix.ext; unfold raw42720step4 raw42720step3; decide +kernel
      have hl : raw42720step3Labels = labelEmbedding1 ∘ raw42720step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42720step3 raw42720step3Labels raw42720step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

theorem canonical42721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42721 raw42721Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw42721 raw42721Labels = mixedMoment B raw42721step0 raw42721step0Labels := by
      have hz : ∀ j, raw42721 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42721step0 = (fun i j => raw42721 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42721step0 raw42721; decide +kernel
      have hl : raw42721step0Labels = raw42721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42721 raw42721Labels permutation434 hz
    mixedMoment B raw42721step0 raw42721step0Labels = mixedMoment B raw42721step1 raw42721step1Labels := by
      have hz : ∀ j, raw42721step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42721step1 = (fun i j => raw42721step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42721step1 raw42721step0; decide +kernel
      have hl : raw42721step1Labels = raw42721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42721step0 raw42721step0Labels permutation80 hz
    mixedMoment B raw42721step1 raw42721step1Labels = mixedMoment B raw42721step2 raw42721step2Labels := by
      have ha : raw42721step2 = (fun i j => raw42721step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42721step2 raw42721step1; decide +kernel
      have hl : raw42721step2Labels = raw42721step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42721step1 raw42721step1Labels permutation29 permutation6
    _ = mixedMoment B node4609 node4609Labels := by rfl

theorem canonical42722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42722 raw42722Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw42722 raw42722Labels = mixedMoment B raw42722step0 raw42722step0Labels := by
      have hz : ∀ j, raw42722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42722step0 = (fun i j => raw42722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42722step0 raw42722; decide +kernel
      have hl : raw42722step0Labels = raw42722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42722 raw42722Labels permutation346 hz
    mixedMoment B raw42722step0 raw42722step0Labels = mixedMoment B raw42722step1 raw42722step1Labels := by
      have ha : raw42722step1 = (fun i j => raw42722step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42722step1 raw42722step0; decide +kernel
      have hl : raw42722step1Labels = raw42722step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42722step0 raw42722step0Labels permutation151 permutation2
    mixedMoment B raw42722step1 raw42722step1Labels = mixedMoment B raw42722step2 raw42722step2Labels := by
      have ha : raw42722step2 = -raw42722step1 := by apply Matrix.ext; change ∀ i j, raw42722step2 i j = -(raw42722step1 i j); unfold raw42722step2 raw42722step1; decide +kernel
      have hl : raw42722step2Labels = raw42722step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42722step2 raw42722step2Labels = mixedMoment B raw42722step3 raw42722step3Labels := by
      have ha : raw42722step3 = raw42722step2 := by apply Matrix.ext; unfold raw42722step3 raw42722step2; decide +kernel
      have hl : raw42722step2Labels = labelEmbedding1 ∘ raw42722step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42722step2 raw42722step2Labels raw42722step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical42723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42723 raw42723Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw42723 raw42723Labels = mixedMoment B raw42723step0 raw42723step0Labels := by
      have hz : ∀ j, raw42723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42723step0 = (fun i j => raw42723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42723step0 raw42723; decide +kernel
      have hl : raw42723step0Labels = raw42723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42723 raw42723Labels permutation346 hz
    mixedMoment B raw42723step0 raw42723step0Labels = mixedMoment B raw42723step1 raw42723step1Labels := by
      have ha : raw42723step1 = (fun i j => raw42723step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42723step1 raw42723step0; decide +kernel
      have hl : raw42723step1Labels = raw42723step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42723step0 raw42723step0Labels permutation149 permutation7
    mixedMoment B raw42723step1 raw42723step1Labels = mixedMoment B raw42723step2 raw42723step2Labels := by
      have ha : raw42723step2 = raw42723step1 := by apply Matrix.ext; unfold raw42723step2 raw42723step1; decide +kernel
      have hl : raw42723step1Labels = labelEmbedding6 ∘ raw42723step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42723step1 raw42723step1Labels raw42723step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

theorem canonical42724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42724 raw42724Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw42724 raw42724Labels = mixedMoment B raw42724step0 raw42724step0Labels := by
      have hz : ∀ j, raw42724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42724step0 = (fun i j => raw42724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42724step0 raw42724; decide +kernel
      have hl : raw42724step0Labels = raw42724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42724 raw42724Labels permutation346 hz
    mixedMoment B raw42724step0 raw42724step0Labels = mixedMoment B raw42724step1 raw42724step1Labels := by
      have ha : raw42724step1 = (fun i j => raw42724step0 (permutation88 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42724step1 raw42724step0; decide +kernel
      have hl : raw42724step1Labels = raw42724step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42724step0 raw42724step0Labels permutation88 permutation4
    mixedMoment B raw42724step1 raw42724step1Labels = mixedMoment B raw42724step2 raw42724step2Labels := by
      have ha : raw42724step2 = -raw42724step1 := by apply Matrix.ext; change ∀ i j, raw42724step2 i j = -(raw42724step1 i j); unfold raw42724step2 raw42724step1; decide +kernel
      have hl : raw42724step2Labels = raw42724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42724step2 raw42724step2Labels = mixedMoment B raw42724step3 raw42724step3Labels := by
      have ha : raw42724step3 = raw42724step2 := by apply Matrix.ext; unfold raw42724step3 raw42724step2; decide +kernel
      have hl : raw42724step2Labels = labelEmbedding1 ∘ raw42724step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42724step2 raw42724step2Labels raw42724step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

theorem canonical42725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42725 raw42725Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw42725 raw42725Labels = mixedMoment B raw42725step0 raw42725step0Labels := by
      have hz : ∀ j, raw42725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42725step0 = (fun i j => raw42725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42725step0 raw42725; decide +kernel
      have hl : raw42725step0Labels = raw42725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42725 raw42725Labels permutation346 hz
    mixedMoment B raw42725step0 raw42725step0Labels = mixedMoment B raw42725step1 raw42725step1Labels := by
      have ha : raw42725step1 = (fun i j => raw42725step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42725step1 raw42725step0; decide +kernel
      have hl : raw42725step1Labels = raw42725step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42725step0 raw42725step0Labels permutation95 permutation6
    _ = mixedMoment B node5139 node5139Labels := by rfl

theorem canonical42726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42726 raw42726Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw42726 raw42726Labels = mixedMoment B raw42726step0 raw42726step0Labels := by
      have hz : ∀ j, raw42726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42726step0 = (fun i j => raw42726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42726step0 raw42726; decide +kernel
      have hl : raw42726step0Labels = raw42726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42726 raw42726Labels permutation346 hz
    mixedMoment B raw42726step0 raw42726step0Labels = mixedMoment B raw42726step1 raw42726step1Labels := by
      have ha : raw42726step1 = (fun i j => raw42726step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42726step1 raw42726step0; decide +kernel
      have hl : raw42726step1Labels = raw42726step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42726step0 raw42726step0Labels permutation35 permutation2
    mixedMoment B raw42726step1 raw42726step1Labels = mixedMoment B raw42726step2 raw42726step2Labels := by
      have ha : raw42726step2 = raw42726step1 := by apply Matrix.ext; unfold raw42726step2 raw42726step1; decide +kernel
      have hl : raw42726step1Labels = labelEmbedding1 ∘ raw42726step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42726step1 raw42726step1Labels raw42726step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3543 node3543Labels := by rfl

theorem canonical42727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42727 raw42727Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw42727 raw42727Labels = mixedMoment B raw42727step0 raw42727step0Labels := by
      have hz : ∀ j, raw42727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42727step0 = (fun i j => raw42727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42727step0 raw42727; decide +kernel
      have hl : raw42727step0Labels = raw42727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42727 raw42727Labels permutation346 hz
    mixedMoment B raw42727step0 raw42727step0Labels = mixedMoment B raw42727step1 raw42727step1Labels := by
      have ha : raw42727step1 = (fun i j => raw42727step0 (permutation89 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42727step1 raw42727step0; decide +kernel
      have hl : raw42727step1Labels = raw42727step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42727step0 raw42727step0Labels permutation89 permutation6
    _ = mixedMoment B node5252 node5252Labels := by rfl

theorem canonical42728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42728 raw42728Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw42728 raw42728Labels = mixedMoment B raw42728step0 raw42728step0Labels := by
      have hz : ∀ j, raw42728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42728step0 = (fun i j => raw42728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42728step0 raw42728; decide +kernel
      have hl : raw42728step0Labels = raw42728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42728 raw42728Labels permutation346 hz
    mixedMoment B raw42728step0 raw42728step0Labels = mixedMoment B raw42728step1 raw42728step1Labels := by
      have ha : raw42728step1 = (fun i j => raw42728step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42728step1 raw42728step0; decide +kernel
      have hl : raw42728step1Labels = raw42728step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42728step0 raw42728step0Labels permutation36 permutation2
    mixedMoment B raw42728step1 raw42728step1Labels = mixedMoment B raw42728step2 raw42728step2Labels := by
      have ha : raw42728step2 = raw42728step1 := by apply Matrix.ext; unfold raw42728step2 raw42728step1; decide +kernel
      have hl : raw42728step1Labels = labelEmbedding1 ∘ raw42728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42728step1 raw42728step1Labels raw42728step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

theorem canonical42729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42729 raw42729Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw42729 raw42729Labels = mixedMoment B raw42729step0 raw42729step0Labels := by
      have hz : ∀ j, raw42729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42729step0 = (fun i j => raw42729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42729step0 raw42729; decide +kernel
      have hl : raw42729step0Labels = raw42729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42729 raw42729Labels permutation346 hz
    mixedMoment B raw42729step0 raw42729step0Labels = mixedMoment B raw42729step1 raw42729step1Labels := by
      have ha : raw42729step1 = (fun i j => raw42729step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42729step1 raw42729step0; decide +kernel
      have hl : raw42729step1Labels = raw42729step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42729step0 raw42729step0Labels permutation50 permutation7
    mixedMoment B raw42729step1 raw42729step1Labels = mixedMoment B raw42729step2 raw42729step2Labels := by
      have ha : raw42729step2 = -raw42729step1 := by apply Matrix.ext; change ∀ i j, raw42729step2 i j = -(raw42729step1 i j); unfold raw42729step2 raw42729step1; decide +kernel
      have hl : raw42729step2Labels = raw42729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42729step2 raw42729step2Labels = mixedMoment B raw42729step3 raw42729step3Labels := by
      have ha : raw42729step3 = raw42729step2 := by apply Matrix.ext; unfold raw42729step3 raw42729step2; decide +kernel
      have hl : raw42729step2Labels = labelEmbedding6 ∘ raw42729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42729step2 raw42729step2Labels raw42729step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5189 node5189Labels := by rfl

theorem canonical42730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42730 raw42730Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw42730 raw42730Labels = mixedMoment B raw42730step0 raw42730step0Labels := by
      have ha : raw42730step0 = (fun i j => raw42730 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42730step0 raw42730; decide +kernel
      have hl : raw42730step0Labels = raw42730Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42730 raw42730Labels permutation157 permutation2
    mixedMoment B raw42730step0 raw42730step0Labels = mixedMoment B raw42730step1 raw42730step1Labels := by
      have ha : raw42730step1 = raw42730step0 := by apply Matrix.ext; unfold raw42730step1 raw42730step0; decide +kernel
      have hl : raw42730step0Labels = labelEmbedding1 ∘ raw42730step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42730step0 raw42730step0Labels raw42730step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

theorem canonical42731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42731 raw42731Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw42731 raw42731Labels = mixedMoment B raw42731step0 raw42731step0Labels := by
      have ha : raw42731step0 = (fun i j => raw42731 (permutation494 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42731step0 raw42731; decide +kernel
      have hl : raw42731step0Labels = raw42731Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42731 raw42731Labels permutation494 permutation6
    _ = mixedMoment B node5128 node5128Labels := by rfl

theorem canonical42732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42732 raw42732Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw42732 raw42732Labels = mixedMoment B raw42732step0 raw42732step0Labels := by
      have hz : ∀ j, raw42732 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42732step0 = (fun i j => raw42732 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42732step0 raw42732; decide +kernel
      have hl : raw42732step0Labels = raw42732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42732 raw42732Labels permutation434 hz
    mixedMoment B raw42732step0 raw42732step0Labels = mixedMoment B raw42732step1 raw42732step1Labels := by
      have ha : raw42732step1 = (fun i j => raw42732step0 (permutation94 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42732step1 raw42732step0; decide +kernel
      have hl : raw42732step1Labels = raw42732step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42732step0 raw42732step0Labels permutation94 permutation4
    mixedMoment B raw42732step1 raw42732step1Labels = mixedMoment B raw42732step2 raw42732step2Labels := by
      have ha : raw42732step2 = -raw42732step1 := by apply Matrix.ext; change ∀ i j, raw42732step2 i j = -(raw42732step1 i j); unfold raw42732step2 raw42732step1; decide +kernel
      have hl : raw42732step2Labels = raw42732step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42732step2 raw42732step2Labels = mixedMoment B raw42732step3 raw42732step3Labels := by
      have ha : raw42732step3 = raw42732step2 := by apply Matrix.ext; unfold raw42732step3 raw42732step2; decide +kernel
      have hl : raw42732step2Labels = labelEmbedding1 ∘ raw42732step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42732step2 raw42732step2Labels raw42732step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

theorem canonical42733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42733 raw42733Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw42733 raw42733Labels = mixedMoment B raw42733step0 raw42733step0Labels := by
      have hz : ∀ j, raw42733 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42733step0 = (fun i j => raw42733 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42733step0 raw42733; decide +kernel
      have hl : raw42733step0Labels = raw42733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42733 raw42733Labels permutation434 hz
    mixedMoment B raw42733step0 raw42733step0Labels = mixedMoment B raw42733step1 raw42733step1Labels := by
      have ha : raw42733step1 = (fun i j => raw42733step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42733step1 raw42733step0; decide +kernel
      have hl : raw42733step1Labels = raw42733step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42733step0 raw42733step0Labels permutation97 permutation6
    _ = mixedMoment B node4817 node4817Labels := by rfl

theorem canonical42734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42734 raw42734Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw42734 raw42734Labels = mixedMoment B raw42734step0 raw42734step0Labels := by
      have hz : ∀ j, raw42734 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42734step0 = (fun i j => raw42734 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42734step0 raw42734; decide +kernel
      have hl : raw42734step0Labels = raw42734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42734 raw42734Labels permutation434 hz
    mixedMoment B raw42734step0 raw42734step0Labels = mixedMoment B raw42734step1 raw42734step1Labels := by
      have ha : raw42734step1 = (fun i j => raw42734step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42734step1 raw42734step0; decide +kernel
      have hl : raw42734step1Labels = raw42734step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42734step0 raw42734step0Labels permutation91 permutation4
    mixedMoment B raw42734step1 raw42734step1Labels = mixedMoment B raw42734step2 raw42734step2Labels := by
      have ha : raw42734step2 = -raw42734step1 := by apply Matrix.ext; change ∀ i j, raw42734step2 i j = -(raw42734step1 i j); unfold raw42734step2 raw42734step1; decide +kernel
      have hl : raw42734step2Labels = raw42734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42734step2 raw42734step2Labels = mixedMoment B raw42734step3 raw42734step3Labels := by
      have ha : raw42734step3 = raw42734step2 := by apply Matrix.ext; unfold raw42734step3 raw42734step2; decide +kernel
      have hl : raw42734step2Labels = labelEmbedding1 ∘ raw42734step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42734step2 raw42734step2Labels raw42734step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical42735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42735 raw42735Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw42735 raw42735Labels = mixedMoment B raw42735step0 raw42735step0Labels := by
      have hz : ∀ j, raw42735 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42735step0 = (fun i j => raw42735 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42735step0 raw42735; decide +kernel
      have hl : raw42735step0Labels = raw42735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42735 raw42735Labels permutation434 hz
    mixedMoment B raw42735step0 raw42735step0Labels = mixedMoment B raw42735step1 raw42735step1Labels := by
      have ha : raw42735step1 = (fun i j => raw42735step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42735step1 raw42735step0; decide +kernel
      have hl : raw42735step1Labels = raw42735step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42735step0 raw42735step0Labels permutation103 permutation6
    _ = mixedMoment B node4853 node4853Labels := by rfl

theorem canonical42736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42736 raw42736Labels = mixedMoment B node2153 node2153Labels := by
  calc
    mixedMoment B raw42736 raw42736Labels = mixedMoment B raw42736step0 raw42736step0Labels := by
      have hz : ∀ j, raw42736 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42736step0 = (fun i j => raw42736 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42736step0 raw42736; decide +kernel
      have hl : raw42736step0Labels = raw42736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42736 raw42736Labels permutation434 hz
    mixedMoment B raw42736step0 raw42736step0Labels = mixedMoment B raw42736step1 raw42736step1Labels := by
      have ha : raw42736step1 = (fun i j => raw42736step0 (permutation100 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42736step1 raw42736step0; decide +kernel
      have hl : raw42736step1Labels = raw42736step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42736step0 raw42736step0Labels permutation100 permutation4
    mixedMoment B raw42736step1 raw42736step1Labels = mixedMoment B raw42736step2 raw42736step2Labels := by
      have ha : raw42736step2 = -raw42736step1 := by apply Matrix.ext; change ∀ i j, raw42736step2 i j = -(raw42736step1 i j); unfold raw42736step2 raw42736step1; decide +kernel
      have hl : raw42736step2Labels = raw42736step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42736step2 raw42736step2Labels = mixedMoment B raw42736step3 raw42736step3Labels := by
      have ha : raw42736step3 = raw42736step2 := by apply Matrix.ext; unfold raw42736step3 raw42736step2; decide +kernel
      have hl : raw42736step2Labels = labelEmbedding1 ∘ raw42736step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42736step2 raw42736step2Labels raw42736step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2153 node2153Labels := by rfl

theorem canonical42737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42737 raw42737Labels = mixedMoment B node4682 node4682Labels := by
  calc
    mixedMoment B raw42737 raw42737Labels = mixedMoment B raw42737step0 raw42737step0Labels := by
      have hz : ∀ j, raw42737 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42737step0 = (fun i j => raw42737 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42737step0 raw42737; decide +kernel
      have hl : raw42737step0Labels = raw42737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42737 raw42737Labels permutation434 hz
    mixedMoment B raw42737step0 raw42737step0Labels = mixedMoment B raw42737step1 raw42737step1Labels := by
      have ha : raw42737step1 = (fun i j => raw42737step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42737step1 raw42737step0; decide +kernel
      have hl : raw42737step1Labels = raw42737step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42737step0 raw42737step0Labels permutation101 permutation6
    _ = mixedMoment B node4682 node4682Labels := by rfl

theorem canonical42738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42738 raw42738Labels = mixedMoment B node2147 node2147Labels := by
  calc
    mixedMoment B raw42738 raw42738Labels = mixedMoment B raw42738step0 raw42738step0Labels := by
      have ha : raw42738step0 = (fun i j => raw42738 (permutation423 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42738step0 raw42738; decide +kernel
      have hl : raw42738step0Labels = raw42738Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42738 raw42738Labels permutation423 permutation4
    mixedMoment B raw42738step0 raw42738step0Labels = mixedMoment B raw42738step1 raw42738step1Labels := by
      have ha : raw42738step1 = -raw42738step0 := by apply Matrix.ext; change ∀ i j, raw42738step1 i j = -(raw42738step0 i j); unfold raw42738step1 raw42738step0; decide +kernel
      have hl : raw42738step1Labels = raw42738step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42738step1 raw42738step1Labels = mixedMoment B raw42738step2 raw42738step2Labels := by
      have ha : raw42738step2 = raw42738step1 := by apply Matrix.ext; unfold raw42738step2 raw42738step1; decide +kernel
      have hl : raw42738step1Labels = labelEmbedding1 ∘ raw42738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42738step1 raw42738step1Labels raw42738step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2147 node2147Labels := by rfl

theorem canonical42739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42739 raw42739Labels = mixedMoment B node4664 node4664Labels := by
  calc
    mixedMoment B raw42739 raw42739Labels = mixedMoment B raw42739step0 raw42739step0Labels := by
      have ha : raw42739step0 = (fun i j => raw42739 (permutation431 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42739step0 raw42739; decide +kernel
      have hl : raw42739step0Labels = raw42739Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42739 raw42739Labels permutation431 permutation6
    _ = mixedMoment B node4664 node4664Labels := by rfl

theorem canonical42740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42740 raw42740Labels = mixedMoment B node2175 node2175Labels := by
  calc
    mixedMoment B raw42740 raw42740Labels = mixedMoment B raw42740step0 raw42740step0Labels := by
      have ha : raw42740step0 = (fun i j => raw42740 (permutation391 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42740step0 raw42740; decide +kernel
      have hl : raw42740step0Labels = raw42740Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42740 raw42740Labels permutation391 permutation4
    mixedMoment B raw42740step0 raw42740step0Labels = mixedMoment B raw42740step1 raw42740step1Labels := by
      have ha : raw42740step1 = -raw42740step0 := by apply Matrix.ext; change ∀ i j, raw42740step1 i j = -(raw42740step0 i j); unfold raw42740step1 raw42740step0; decide +kernel
      have hl : raw42740step1Labels = raw42740step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42740step1 raw42740step1Labels = mixedMoment B raw42740step2 raw42740step2Labels := by
      have ha : raw42740step2 = raw42740step1 := by apply Matrix.ext; unfold raw42740step2 raw42740step1; decide +kernel
      have hl : raw42740step1Labels = labelEmbedding1 ∘ raw42740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42740step1 raw42740step1Labels raw42740step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2175 node2175Labels := by rfl

theorem canonical42741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42741 raw42741Labels = mixedMoment B node4761 node4761Labels := by
  calc
    mixedMoment B raw42741 raw42741Labels = mixedMoment B raw42741step0 raw42741step0Labels := by
      have ha : raw42741step0 = (fun i j => raw42741 (permutation392 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42741step0 raw42741; decide +kernel
      have hl : raw42741step0Labels = raw42741Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42741 raw42741Labels permutation392 permutation6
    _ = mixedMoment B node4761 node4761Labels := by rfl

theorem canonical42742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42742 raw42742Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw42742 raw42742Labels = mixedMoment B raw42742step0 raw42742step0Labels := by
      have ha : raw42742step0 = (fun i j => raw42742 (permutation387 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42742step0 raw42742; decide +kernel
      have hl : raw42742step0Labels = raw42742Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42742 raw42742Labels permutation387 permutation4
    mixedMoment B raw42742step0 raw42742step0Labels = mixedMoment B raw42742step1 raw42742step1Labels := by
      have ha : raw42742step1 = -raw42742step0 := by apply Matrix.ext; change ∀ i j, raw42742step1 i j = -(raw42742step0 i j); unfold raw42742step1 raw42742step0; decide +kernel
      have hl : raw42742step1Labels = raw42742step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42742step1 raw42742step1Labels = mixedMoment B raw42742step2 raw42742step2Labels := by
      have ha : raw42742step2 = raw42742step1 := by apply Matrix.ext; unfold raw42742step2 raw42742step1; decide +kernel
      have hl : raw42742step1Labels = labelEmbedding1 ∘ raw42742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42742step1 raw42742step1Labels raw42742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

theorem canonical42743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42743 raw42743Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw42743 raw42743Labels = mixedMoment B raw42743step0 raw42743step0Labels := by
      have ha : raw42743step0 = (fun i j => raw42743 (permutation394 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42743step0 raw42743; decide +kernel
      have hl : raw42743step0Labels = raw42743Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42743 raw42743Labels permutation394 permutation6
    _ = mixedMoment B node4792 node4792Labels := by rfl

theorem canonical42744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42744 raw42744Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw42744 raw42744Labels = mixedMoment B raw42744step0 raw42744step0Labels := by
      have ha : raw42744step0 = (fun i j => raw42744 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42744step0 raw42744; decide +kernel
      have hl : raw42744step0Labels = raw42744Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42744 raw42744Labels permutation158 permutation2
    mixedMoment B raw42744step0 raw42744step0Labels = mixedMoment B raw42744step1 raw42744step1Labels := by
      have ha : raw42744step1 = raw42744step0 := by apply Matrix.ext; unfold raw42744step1 raw42744step0; decide +kernel
      have hl : raw42744step0Labels = labelEmbedding1 ∘ raw42744step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42744step0 raw42744step0Labels raw42744step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

theorem canonical42745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42745 raw42745Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw42745 raw42745Labels = mixedMoment B raw42745step0 raw42745step0Labels := by
      have ha : raw42745step0 = (fun i j => raw42745 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42745step0 raw42745; decide +kernel
      have hl : raw42745step0Labels = raw42745Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42745 raw42745Labels permutation173 permutation7
    mixedMoment B raw42745step0 raw42745step0Labels = mixedMoment B raw42745step1 raw42745step1Labels := by
      have ha : raw42745step1 = -raw42745step0 := by apply Matrix.ext; change ∀ i j, raw42745step1 i j = -(raw42745step0 i j); unfold raw42745step1 raw42745step0; decide +kernel
      have hl : raw42745step1Labels = raw42745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42745step1 raw42745step1Labels = mixedMoment B raw42745step2 raw42745step2Labels := by
      have ha : raw42745step2 = raw42745step1 := by apply Matrix.ext; unfold raw42745step2 raw42745step1; decide +kernel
      have hl : raw42745step1Labels = labelEmbedding6 ∘ raw42745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42745step1 raw42745step1Labels raw42745step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5086 node5086Labels := by rfl

theorem canonical42746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42746 raw42746Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw42746 raw42746Labels = mixedMoment B raw42746step0 raw42746step0Labels := by
      have ha : raw42746step0 = (fun i j => raw42746 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42746step0 raw42746; decide +kernel
      have hl : raw42746step0Labels = raw42746Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42746 raw42746Labels permutation158 permutation2
    mixedMoment B raw42746step0 raw42746step0Labels = mixedMoment B raw42746step1 raw42746step1Labels := by
      have ha : raw42746step1 = raw42746step0 := by apply Matrix.ext; unfold raw42746step1 raw42746step0; decide +kernel
      have hl : raw42746step0Labels = labelEmbedding1 ∘ raw42746step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42746step0 raw42746step0Labels raw42746step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

theorem canonical42747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42747 raw42747Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw42747 raw42747Labels = mixedMoment B raw42747step0 raw42747step0Labels := by
      have ha : raw42747step0 = (fun i j => raw42747 (permutation167 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42747step0 raw42747; decide +kernel
      have hl : raw42747step0Labels = raw42747Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42747 raw42747Labels permutation167 permutation7
    mixedMoment B raw42747step0 raw42747step0Labels = mixedMoment B raw42747step1 raw42747step1Labels := by
      have ha : raw42747step1 = -raw42747step0 := by apply Matrix.ext; change ∀ i j, raw42747step1 i j = -(raw42747step0 i j); unfold raw42747step1 raw42747step0; decide +kernel
      have hl : raw42747step1Labels = raw42747step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42747step1 raw42747step1Labels = mixedMoment B raw42747step2 raw42747step2Labels := by
      have ha : raw42747step2 = raw42747step1 := by apply Matrix.ext; unfold raw42747step2 raw42747step1; decide +kernel
      have hl : raw42747step1Labels = labelEmbedding6 ∘ raw42747step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42747step1 raw42747step1Labels raw42747step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

theorem canonical42748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42748 raw42748Labels = mixedMoment B node3462 node3462Labels := by
  calc
    mixedMoment B raw42748 raw42748Labels = mixedMoment B raw42748step0 raw42748step0Labels := by
      have ha : raw42748step0 = (fun i j => raw42748 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42748step0 raw42748; decide +kernel
      have hl : raw42748step0Labels = raw42748Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42748 raw42748Labels permutation158 permutation2
    mixedMoment B raw42748step0 raw42748step0Labels = mixedMoment B raw42748step1 raw42748step1Labels := by
      have ha : raw42748step1 = raw42748step0 := by apply Matrix.ext; unfold raw42748step1 raw42748step0; decide +kernel
      have hl : raw42748step0Labels = labelEmbedding1 ∘ raw42748step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42748step0 raw42748step0Labels raw42748step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3462 node3462Labels := by rfl

theorem canonical42749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42749 raw42749Labels = mixedMoment B node5042 node5042Labels := by
  calc
    mixedMoment B raw42749 raw42749Labels = mixedMoment B raw42749step0 raw42749step0Labels := by
      have ha : raw42749step0 = (fun i j => raw42749 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42749step0 raw42749; decide +kernel
      have hl : raw42749step0Labels = raw42749Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42749 raw42749Labels permutation166 permutation7
    mixedMoment B raw42749step0 raw42749step0Labels = mixedMoment B raw42749step1 raw42749step1Labels := by
      have ha : raw42749step1 = -raw42749step0 := by apply Matrix.ext; change ∀ i j, raw42749step1 i j = -(raw42749step0 i j); unfold raw42749step1 raw42749step0; decide +kernel
      have hl : raw42749step1Labels = raw42749step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42749step1 raw42749step1Labels = mixedMoment B raw42749step2 raw42749step2Labels := by
      have ha : raw42749step2 = raw42749step1 := by apply Matrix.ext; unfold raw42749step2 raw42749step1; decide +kernel
      have hl : raw42749step1Labels = labelEmbedding6 ∘ raw42749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42749step1 raw42749step1Labels raw42749step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5042 node5042Labels := by rfl

theorem canonical42750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42750 raw42750Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw42750 raw42750Labels = mixedMoment B raw42750step0 raw42750step0Labels := by
      have hz : ∀ j, raw42750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42750step0 = (fun i j => raw42750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42750step0 raw42750; decide +kernel
      have hl : raw42750step0Labels = raw42750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42750 raw42750Labels permutation434 hz
    mixedMoment B raw42750step0 raw42750step0Labels = mixedMoment B raw42750step1 raw42750step1Labels := by
      have ha : raw42750step1 = raw42750step0 := by apply Matrix.ext; unfold raw42750step1 raw42750step0; decide +kernel
      have hl : raw42750step0Labels = labelEmbedding1 ∘ raw42750step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42750step0 raw42750step0Labels raw42750step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

theorem canonical42751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42751 raw42751Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw42751 raw42751Labels = mixedMoment B raw42751step0 raw42751step0Labels := by
      have hz : ∀ j, raw42751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42751step0 = (fun i j => raw42751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42751step0 raw42751; decide +kernel
      have hl : raw42751step0Labels = raw42751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42751 raw42751Labels permutation434 hz
    mixedMoment B raw42751step0 raw42751step0Labels = mixedMoment B raw42751step1 raw42751step1Labels := by
      have ha : raw42751step1 = (fun i j => raw42751step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42751step1 raw42751step0; decide +kernel
      have hl : raw42751step1Labels = raw42751step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42751step0 raw42751step0Labels permutation36 permutation7
    mixedMoment B raw42751step1 raw42751step1Labels = mixedMoment B raw42751step2 raw42751step2Labels := by
      have ha : raw42751step2 = -raw42751step1 := by apply Matrix.ext; change ∀ i j, raw42751step2 i j = -(raw42751step1 i j); unfold raw42751step2 raw42751step1; decide +kernel
      have hl : raw42751step2Labels = raw42751step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42751step2 raw42751step2Labels = mixedMoment B raw42751step3 raw42751step3Labels := by
      have ha : raw42751step3 = raw42751step2 := by apply Matrix.ext; unfold raw42751step3 raw42751step2; decide +kernel
      have hl : raw42751step2Labels = labelEmbedding6 ∘ raw42751step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42751step2 raw42751step2Labels raw42751step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5090 node5090Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2688 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2688) =
      Integer.Sparse.eval keyMomentRow2688 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2688).leftCharge (GramAssembly.key 2688).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3579) := by
    have ha : gramCharges (GramAssembly.key 2688).leftCharge (GramAssembly.key 2688).rightCharge = raw42688 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42688Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42688 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2688).leftCharge (GramAssembly.key 2688).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5201) := by
    have ha : gramCharges (GramAssembly.key 2688).leftCharge (GramAssembly.key 2688).rightCharge = raw42689 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42689Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42689 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2688).leftCharge (GramAssembly.key 2688).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2688).leftCharge (GramAssembly.key 2688).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2688, Integer.Sparse.eval]
  ring

theorem keyMoment2689 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2689) =
      Integer.Sparse.eval keyMomentRow2689 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2689).leftCharge (GramAssembly.key 2689).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3530) := by
    have ha : gramCharges (GramAssembly.key 2689).leftCharge (GramAssembly.key 2689).rightCharge = raw42690 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42690Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42690 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2689).leftCharge (GramAssembly.key 2689).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5147) := by
    have ha : gramCharges (GramAssembly.key 2689).leftCharge (GramAssembly.key 2689).rightCharge = raw42691 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42691Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42691 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2689).leftCharge (GramAssembly.key 2689).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2689).leftCharge (GramAssembly.key 2689).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2689, Integer.Sparse.eval]
  ring

theorem keyMoment2690 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2690) =
      Integer.Sparse.eval keyMomentRow2690 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2690).leftCharge (GramAssembly.key 2690).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3578) := by
    have ha : gramCharges (GramAssembly.key 2690).leftCharge (GramAssembly.key 2690).rightCharge = raw42692 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42692Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42692 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2690).leftCharge (GramAssembly.key 2690).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5199) := by
    have ha : gramCharges (GramAssembly.key 2690).leftCharge (GramAssembly.key 2690).rightCharge = raw42693 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42693Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42693 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2690).leftCharge (GramAssembly.key 2690).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2690).leftCharge (GramAssembly.key 2690).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2690, Integer.Sparse.eval]
  ring

theorem keyMoment2691 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2691) =
      Integer.Sparse.eval keyMomentRow2691 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2691).leftCharge (GramAssembly.key 2691).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3580) := by
    have ha : gramCharges (GramAssembly.key 2691).leftCharge (GramAssembly.key 2691).rightCharge = raw42694 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42694Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42694 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2691).leftCharge (GramAssembly.key 2691).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5282) := by
    have ha : gramCharges (GramAssembly.key 2691).leftCharge (GramAssembly.key 2691).rightCharge = raw42695 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42695Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42695 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2691).leftCharge (GramAssembly.key 2691).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2691).leftCharge (GramAssembly.key 2691).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2691, Integer.Sparse.eval]
  ring

theorem keyMoment2692 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2692) =
      Integer.Sparse.eval keyMomentRow2692 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2692).leftCharge (GramAssembly.key 2692).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3562) := by
    have ha : gramCharges (GramAssembly.key 2692).leftCharge (GramAssembly.key 2692).rightCharge = raw42696 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42696Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42696 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2692).leftCharge (GramAssembly.key 2692).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5145) := by
    have ha : gramCharges (GramAssembly.key 2692).leftCharge (GramAssembly.key 2692).rightCharge = raw42697 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42697Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42697 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2692).leftCharge (GramAssembly.key 2692).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2692).leftCharge (GramAssembly.key 2692).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2692, Integer.Sparse.eval]
  ring

theorem keyMoment2693 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2693) =
      Integer.Sparse.eval keyMomentRow2693 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2693).leftCharge (GramAssembly.key 2693).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3541) := by
    have ha : gramCharges (GramAssembly.key 2693).leftCharge (GramAssembly.key 2693).rightCharge = raw42698 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42698Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42698 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2693).leftCharge (GramAssembly.key 2693).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2693).leftCharge (GramAssembly.key 2693).rightCharge = raw42699 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42699Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42699 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2693).leftCharge (GramAssembly.key 2693).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2693).leftCharge (GramAssembly.key 2693).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2693, Integer.Sparse.eval]
  ring

theorem keyMoment2694 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2694) =
      Integer.Sparse.eval keyMomentRow2694 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2694).leftCharge (GramAssembly.key 2694).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3540) := by
    have ha : gramCharges (GramAssembly.key 2694).leftCharge (GramAssembly.key 2694).rightCharge = raw42700 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42700Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42700 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2694).leftCharge (GramAssembly.key 2694).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2694).leftCharge (GramAssembly.key 2694).rightCharge = raw42701 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42701Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42701 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2694).leftCharge (GramAssembly.key 2694).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2694).leftCharge (GramAssembly.key 2694).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2694, Integer.Sparse.eval]
  ring

theorem keyMoment2695 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2695) =
      Integer.Sparse.eval keyMomentRow2695 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2695).leftCharge (GramAssembly.key 2695).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3538) := by
    have ha : gramCharges (GramAssembly.key 2695).leftCharge (GramAssembly.key 2695).rightCharge = raw42702 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42702Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42702 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2695).leftCharge (GramAssembly.key 2695).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5188) := by
    have ha : gramCharges (GramAssembly.key 2695).leftCharge (GramAssembly.key 2695).rightCharge = raw42703 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42703Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42703 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2695).leftCharge (GramAssembly.key 2695).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2695).leftCharge (GramAssembly.key 2695).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2695, Integer.Sparse.eval]
  ring

theorem keyMoment2696 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2696) =
      Integer.Sparse.eval keyMomentRow2696 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2696).leftCharge (GramAssembly.key 2696).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3516) := by
    have ha : gramCharges (GramAssembly.key 2696).leftCharge (GramAssembly.key 2696).rightCharge = raw42704 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42704Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42704 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2696).leftCharge (GramAssembly.key 2696).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5129) := by
    have ha : gramCharges (GramAssembly.key 2696).leftCharge (GramAssembly.key 2696).rightCharge = raw42705 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42705Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42705 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2696).leftCharge (GramAssembly.key 2696).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2696).leftCharge (GramAssembly.key 2696).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2696, Integer.Sparse.eval]
  ring

theorem keyMoment2697 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2697) =
      Integer.Sparse.eval keyMomentRow2697 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2697).leftCharge (GramAssembly.key 2697).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3537) := by
    have ha : gramCharges (GramAssembly.key 2697).leftCharge (GramAssembly.key 2697).rightCharge = raw42706 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42706Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42706 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2697).leftCharge (GramAssembly.key 2697).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5187) := by
    have ha : gramCharges (GramAssembly.key 2697).leftCharge (GramAssembly.key 2697).rightCharge = raw42707 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42707Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42707 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2697).leftCharge (GramAssembly.key 2697).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2697).leftCharge (GramAssembly.key 2697).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2697, Integer.Sparse.eval]
  ring

theorem keyMoment2698 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2698) =
      Integer.Sparse.eval keyMomentRow2698 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2698).leftCharge (GramAssembly.key 2698).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3539) := by
    have ha : gramCharges (GramAssembly.key 2698).leftCharge (GramAssembly.key 2698).rightCharge = raw42708 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42708Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42708 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2698).leftCharge (GramAssembly.key 2698).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2698).leftCharge (GramAssembly.key 2698).rightCharge = raw42709 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42709Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42709 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2698).leftCharge (GramAssembly.key 2698).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2698).leftCharge (GramAssembly.key 2698).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2698, Integer.Sparse.eval]
  ring

theorem keyMoment2699 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2699) =
      Integer.Sparse.eval keyMomentRow2699 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2699).leftCharge (GramAssembly.key 2699).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3526) := by
    have ha : gramCharges (GramAssembly.key 2699).leftCharge (GramAssembly.key 2699).rightCharge = raw42710 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42710Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42710 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2699).leftCharge (GramAssembly.key 2699).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2699).leftCharge (GramAssembly.key 2699).rightCharge = raw42711 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42711Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42711 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2699).leftCharge (GramAssembly.key 2699).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2699).leftCharge (GramAssembly.key 2699).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2699, Integer.Sparse.eval]
  ring

theorem keyMoment2700 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2700) =
      Integer.Sparse.eval keyMomentRow2700 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2700).leftCharge (GramAssembly.key 2700).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3524) := by
    have ha : gramCharges (GramAssembly.key 2700).leftCharge (GramAssembly.key 2700).rightCharge = raw42712 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42712Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42712 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2700).leftCharge (GramAssembly.key 2700).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5184) := by
    have ha : gramCharges (GramAssembly.key 2700).leftCharge (GramAssembly.key 2700).rightCharge = raw42713 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42713Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42713 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2700).leftCharge (GramAssembly.key 2700).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2700).leftCharge (GramAssembly.key 2700).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2700, Integer.Sparse.eval]
  ring

theorem keyMoment2701 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2701) =
      Integer.Sparse.eval keyMomentRow2701 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2701).leftCharge (GramAssembly.key 2701).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3535) := by
    have ha : gramCharges (GramAssembly.key 2701).leftCharge (GramAssembly.key 2701).rightCharge = raw42714 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42714Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42714 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2701).leftCharge (GramAssembly.key 2701).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5266) := by
    have ha : gramCharges (GramAssembly.key 2701).leftCharge (GramAssembly.key 2701).rightCharge = raw42715 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42715Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42715 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2701).leftCharge (GramAssembly.key 2701).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2701).leftCharge (GramAssembly.key 2701).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2701, Integer.Sparse.eval]
  ring

theorem keyMoment2702 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2702) =
      Integer.Sparse.eval keyMomentRow2702 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2702).leftCharge (GramAssembly.key 2702).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3530) := by
    have ha : gramCharges (GramAssembly.key 2702).leftCharge (GramAssembly.key 2702).rightCharge = raw42716 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42716Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42716 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2702).leftCharge (GramAssembly.key 2702).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5147) := by
    have ha : gramCharges (GramAssembly.key 2702).leftCharge (GramAssembly.key 2702).rightCharge = raw42717 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42717Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42717 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2702).leftCharge (GramAssembly.key 2702).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2702).leftCharge (GramAssembly.key 2702).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2702, Integer.Sparse.eval]
  ring

theorem keyMoment2703 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2703) =
      Integer.Sparse.eval keyMomentRow2703 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2703).leftCharge (GramAssembly.key 2703).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3549) := by
    have ha : gramCharges (GramAssembly.key 2703).leftCharge (GramAssembly.key 2703).rightCharge = raw42718 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42718Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42718 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2703).leftCharge (GramAssembly.key 2703).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5268) := by
    have ha : gramCharges (GramAssembly.key 2703).leftCharge (GramAssembly.key 2703).rightCharge = raw42719 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42719Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42719 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2703).leftCharge (GramAssembly.key 2703).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2703).leftCharge (GramAssembly.key 2703).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2703, Integer.Sparse.eval]
  ring

theorem keyMoment2704 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2704) =
      Integer.Sparse.eval keyMomentRow2704 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2704).leftCharge (GramAssembly.key 2704).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3302) := by
    have ha : gramCharges (GramAssembly.key 2704).leftCharge (GramAssembly.key 2704).rightCharge = raw42720 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42720Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42720 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2704).leftCharge (GramAssembly.key 2704).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4609) := by
    have ha : gramCharges (GramAssembly.key 2704).leftCharge (GramAssembly.key 2704).rightCharge = raw42721 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42721Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42721 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2704).leftCharge (GramAssembly.key 2704).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2704).leftCharge (GramAssembly.key 2704).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2704, Integer.Sparse.eval]
  ring

theorem keyMoment2705 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2705) =
      Integer.Sparse.eval keyMomentRow2705 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2705).leftCharge (GramAssembly.key 2705).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3291) := by
    have ha : gramCharges (GramAssembly.key 2705).leftCharge (GramAssembly.key 2705).rightCharge = raw42722 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42722Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42722 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2705).leftCharge (GramAssembly.key 2705).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4591) := by
    have ha : gramCharges (GramAssembly.key 2705).leftCharge (GramAssembly.key 2705).rightCharge = raw42723 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42723Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42723 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2705).leftCharge (GramAssembly.key 2705).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2705).leftCharge (GramAssembly.key 2705).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2705, Integer.Sparse.eval]
  ring

theorem keyMoment2706 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2706) =
      Integer.Sparse.eval keyMomentRow2706 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2706).leftCharge (GramAssembly.key 2706).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3523) := by
    have ha : gramCharges (GramAssembly.key 2706).leftCharge (GramAssembly.key 2706).rightCharge = raw42724 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42724Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42724 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2706).leftCharge (GramAssembly.key 2706).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5139) := by
    have ha : gramCharges (GramAssembly.key 2706).leftCharge (GramAssembly.key 2706).rightCharge = raw42725 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42725Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42725 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2706).leftCharge (GramAssembly.key 2706).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2706).leftCharge (GramAssembly.key 2706).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2706, Integer.Sparse.eval]
  ring

theorem keyMoment2707 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2707) =
      Integer.Sparse.eval keyMomentRow2707 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2707).leftCharge (GramAssembly.key 2707).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3543) := by
    have ha : gramCharges (GramAssembly.key 2707).leftCharge (GramAssembly.key 2707).rightCharge = raw42726 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42726Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42726 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2707).leftCharge (GramAssembly.key 2707).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5252) := by
    have ha : gramCharges (GramAssembly.key 2707).leftCharge (GramAssembly.key 2707).rightCharge = raw42727 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42727Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42727 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2707).leftCharge (GramAssembly.key 2707).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2707).leftCharge (GramAssembly.key 2707).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2707, Integer.Sparse.eval]
  ring

theorem keyMoment2708 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2708) =
      Integer.Sparse.eval keyMomentRow2708 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2708).leftCharge (GramAssembly.key 2708).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3542) := by
    have ha : gramCharges (GramAssembly.key 2708).leftCharge (GramAssembly.key 2708).rightCharge = raw42728 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42728Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42728 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2708).leftCharge (GramAssembly.key 2708).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5189) := by
    have ha : gramCharges (GramAssembly.key 2708).leftCharge (GramAssembly.key 2708).rightCharge = raw42729 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42729Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42729 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2708).leftCharge (GramAssembly.key 2708).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2708).leftCharge (GramAssembly.key 2708).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2708, Integer.Sparse.eval]
  ring

theorem keyMoment2709 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2709) =
      Integer.Sparse.eval keyMomentRow2709 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2709).leftCharge (GramAssembly.key 2709).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3519) := by
    have ha : gramCharges (GramAssembly.key 2709).leftCharge (GramAssembly.key 2709).rightCharge = raw42730 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42730Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42730 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2709).leftCharge (GramAssembly.key 2709).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5128) := by
    have ha : gramCharges (GramAssembly.key 2709).leftCharge (GramAssembly.key 2709).rightCharge = raw42731 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42731Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42731 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2709).leftCharge (GramAssembly.key 2709).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2709).leftCharge (GramAssembly.key 2709).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2709, Integer.Sparse.eval]
  ring

theorem keyMoment2710 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2710) =
      Integer.Sparse.eval keyMomentRow2710 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2710).leftCharge (GramAssembly.key 2710).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2207) := by
    have ha : gramCharges (GramAssembly.key 2710).leftCharge (GramAssembly.key 2710).rightCharge = raw42732 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42732Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42732 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2710).leftCharge (GramAssembly.key 2710).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4817) := by
    have ha : gramCharges (GramAssembly.key 2710).leftCharge (GramAssembly.key 2710).rightCharge = raw42733 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42733Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42733 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2710).leftCharge (GramAssembly.key 2710).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2710).leftCharge (GramAssembly.key 2710).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2710, Integer.Sparse.eval]
  ring

theorem keyMoment2711 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2711) =
      Integer.Sparse.eval keyMomentRow2711 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2711).leftCharge (GramAssembly.key 2711).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2259) := by
    have ha : gramCharges (GramAssembly.key 2711).leftCharge (GramAssembly.key 2711).rightCharge = raw42734 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42734Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42734 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2711).leftCharge (GramAssembly.key 2711).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4853) := by
    have ha : gramCharges (GramAssembly.key 2711).leftCharge (GramAssembly.key 2711).rightCharge = raw42735 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42735Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42735 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2711).leftCharge (GramAssembly.key 2711).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2711).leftCharge (GramAssembly.key 2711).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2711, Integer.Sparse.eval]
  ring

theorem keyMoment2712 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2712) =
      Integer.Sparse.eval keyMomentRow2712 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2712).leftCharge (GramAssembly.key 2712).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2153) := by
    have ha : gramCharges (GramAssembly.key 2712).leftCharge (GramAssembly.key 2712).rightCharge = raw42736 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42736Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42736 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2712).leftCharge (GramAssembly.key 2712).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4682) := by
    have ha : gramCharges (GramAssembly.key 2712).leftCharge (GramAssembly.key 2712).rightCharge = raw42737 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42737Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42737 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2712).leftCharge (GramAssembly.key 2712).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2712).leftCharge (GramAssembly.key 2712).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2712, Integer.Sparse.eval]
  ring

theorem keyMoment2713 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2713) =
      Integer.Sparse.eval keyMomentRow2713 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2713).leftCharge (GramAssembly.key 2713).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2147) := by
    have ha : gramCharges (GramAssembly.key 2713).leftCharge (GramAssembly.key 2713).rightCharge = raw42738 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42738Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42738 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2713).leftCharge (GramAssembly.key 2713).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4664) := by
    have ha : gramCharges (GramAssembly.key 2713).leftCharge (GramAssembly.key 2713).rightCharge = raw42739 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42739Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42739 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2713).leftCharge (GramAssembly.key 2713).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2713).leftCharge (GramAssembly.key 2713).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2713, Integer.Sparse.eval]
  ring

theorem keyMoment2714 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2714) =
      Integer.Sparse.eval keyMomentRow2714 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2714).leftCharge (GramAssembly.key 2714).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2175) := by
    have ha : gramCharges (GramAssembly.key 2714).leftCharge (GramAssembly.key 2714).rightCharge = raw42740 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42740Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42740 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2714).leftCharge (GramAssembly.key 2714).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4761) := by
    have ha : gramCharges (GramAssembly.key 2714).leftCharge (GramAssembly.key 2714).rightCharge = raw42741 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42741Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42741 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2714).leftCharge (GramAssembly.key 2714).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2714).leftCharge (GramAssembly.key 2714).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2714, Integer.Sparse.eval]
  ring

theorem keyMoment2715 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2715) =
      Integer.Sparse.eval keyMomentRow2715 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2715).leftCharge (GramAssembly.key 2715).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2201) := by
    have ha : gramCharges (GramAssembly.key 2715).leftCharge (GramAssembly.key 2715).rightCharge = raw42742 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42742Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42742 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2715).leftCharge (GramAssembly.key 2715).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4792) := by
    have ha : gramCharges (GramAssembly.key 2715).leftCharge (GramAssembly.key 2715).rightCharge = raw42743 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42743Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42743 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2715).leftCharge (GramAssembly.key 2715).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2715).leftCharge (GramAssembly.key 2715).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2715, Integer.Sparse.eval]
  ring

theorem keyMoment2716 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2716) =
      Integer.Sparse.eval keyMomentRow2716 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2716).leftCharge (GramAssembly.key 2716).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3464) := by
    have ha : gramCharges (GramAssembly.key 2716).leftCharge (GramAssembly.key 2716).rightCharge = raw42744 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42744Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42744 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2716).leftCharge (GramAssembly.key 2716).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5086) := by
    have ha : gramCharges (GramAssembly.key 2716).leftCharge (GramAssembly.key 2716).rightCharge = raw42745 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42745Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42745 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2716).leftCharge (GramAssembly.key 2716).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2716).leftCharge (GramAssembly.key 2716).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2716, Integer.Sparse.eval]
  ring

theorem keyMoment2717 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2717) =
      Integer.Sparse.eval keyMomentRow2717 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3463) := by
    have ha : gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge = raw42746 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42746Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42746 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5074) := by
    have ha : gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge = raw42747 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42747Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42747 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2717, Integer.Sparse.eval]
  ring

theorem keyMoment2718 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2718) =
      Integer.Sparse.eval keyMomentRow2718 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2718).leftCharge (GramAssembly.key 2718).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3462) := by
    have ha : gramCharges (GramAssembly.key 2718).leftCharge (GramAssembly.key 2718).rightCharge = raw42748 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42748Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42748 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2718).leftCharge (GramAssembly.key 2718).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5042) := by
    have ha : gramCharges (GramAssembly.key 2718).leftCharge (GramAssembly.key 2718).rightCharge = raw42749 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42749Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42749 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2718).leftCharge (GramAssembly.key 2718).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2718).leftCharge (GramAssembly.key 2718).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2718, Integer.Sparse.eval]
  ring

theorem keyMoment2719 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2719) =
      Integer.Sparse.eval keyMomentRow2719 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2719).leftCharge (GramAssembly.key 2719).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3480) := by
    have ha : gramCharges (GramAssembly.key 2719).leftCharge (GramAssembly.key 2719).rightCharge = raw42750 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42750Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42750 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2719).leftCharge (GramAssembly.key 2719).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5090) := by
    have ha : gramCharges (GramAssembly.key 2719).leftCharge (GramAssembly.key 2719).rightCharge = raw42751 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42751Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42751 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2719).leftCharge (GramAssembly.key 2719).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2719).leftCharge (GramAssembly.key 2719).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2719, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2688 : keyMomentRows (2688 : Fin 2886) =
    keyMomentRow2688 := by decide +kernel

theorem keyMomentRowsAt2689 : keyMomentRows (2689 : Fin 2886) =
    keyMomentRow2689 := by decide +kernel

theorem keyMomentRowsAt2690 : keyMomentRows (2690 : Fin 2886) =
    keyMomentRow2690 := by decide +kernel

theorem keyMomentRowsAt2691 : keyMomentRows (2691 : Fin 2886) =
    keyMomentRow2691 := by decide +kernel

theorem keyMomentRowsAt2692 : keyMomentRows (2692 : Fin 2886) =
    keyMomentRow2692 := by decide +kernel

theorem keyMomentRowsAt2693 : keyMomentRows (2693 : Fin 2886) =
    keyMomentRow2693 := by decide +kernel

theorem keyMomentRowsAt2694 : keyMomentRows (2694 : Fin 2886) =
    keyMomentRow2694 := by decide +kernel

theorem keyMomentRowsAt2695 : keyMomentRows (2695 : Fin 2886) =
    keyMomentRow2695 := by decide +kernel

theorem keyMomentRowsAt2696 : keyMomentRows (2696 : Fin 2886) =
    keyMomentRow2696 := by decide +kernel

theorem keyMomentRowsAt2697 : keyMomentRows (2697 : Fin 2886) =
    keyMomentRow2697 := by decide +kernel

theorem keyMomentRowsAt2698 : keyMomentRows (2698 : Fin 2886) =
    keyMomentRow2698 := by decide +kernel

theorem keyMomentRowsAt2699 : keyMomentRows (2699 : Fin 2886) =
    keyMomentRow2699 := by decide +kernel

theorem keyMomentRowsAt2700 : keyMomentRows (2700 : Fin 2886) =
    keyMomentRow2700 := by decide +kernel

theorem keyMomentRowsAt2701 : keyMomentRows (2701 : Fin 2886) =
    keyMomentRow2701 := by decide +kernel

theorem keyMomentRowsAt2702 : keyMomentRows (2702 : Fin 2886) =
    keyMomentRow2702 := by decide +kernel

theorem keyMomentRowsAt2703 : keyMomentRows (2703 : Fin 2886) =
    keyMomentRow2703 := by decide +kernel

theorem keyMomentRowsAt2704 : keyMomentRows (2704 : Fin 2886) =
    keyMomentRow2704 := by decide +kernel

theorem keyMomentRowsAt2705 : keyMomentRows (2705 : Fin 2886) =
    keyMomentRow2705 := by decide +kernel

theorem keyMomentRowsAt2706 : keyMomentRows (2706 : Fin 2886) =
    keyMomentRow2706 := by decide +kernel

theorem keyMomentRowsAt2707 : keyMomentRows (2707 : Fin 2886) =
    keyMomentRow2707 := by decide +kernel

theorem keyMomentRowsAt2708 : keyMomentRows (2708 : Fin 2886) =
    keyMomentRow2708 := by decide +kernel

theorem keyMomentRowsAt2709 : keyMomentRows (2709 : Fin 2886) =
    keyMomentRow2709 := by decide +kernel

theorem keyMomentRowsAt2710 : keyMomentRows (2710 : Fin 2886) =
    keyMomentRow2710 := by decide +kernel

theorem keyMomentRowsAt2711 : keyMomentRows (2711 : Fin 2886) =
    keyMomentRow2711 := by decide +kernel

theorem keyMomentRowsAt2712 : keyMomentRows (2712 : Fin 2886) =
    keyMomentRow2712 := by decide +kernel

theorem keyMomentRowsAt2713 : keyMomentRows (2713 : Fin 2886) =
    keyMomentRow2713 := by decide +kernel

theorem keyMomentRowsAt2714 : keyMomentRows (2714 : Fin 2886) =
    keyMomentRow2714 := by decide +kernel

theorem keyMomentRowsAt2715 : keyMomentRows (2715 : Fin 2886) =
    keyMomentRow2715 := by decide +kernel

theorem keyMomentRowsAt2716 : keyMomentRows (2716 : Fin 2886) =
    keyMomentRow2716 := by decide +kernel

theorem keyMomentRowsAt2717 : keyMomentRows (2717 : Fin 2886) =
    keyMomentRow2717 := by decide +kernel

theorem keyMomentRowsAt2718 : keyMomentRows (2718 : Fin 2886) =
    keyMomentRow2718 := by decide +kernel

theorem keyMomentRowsAt2719 : keyMomentRows (2719 : Fin 2886) =
    keyMomentRow2719 := by decide +kernel

theorem keyMomentChunkSound84_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 84) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2688 ∨ k.val = 2689 ∨ k.val = 2690 ∨ k.val = 2691 ∨ k.val = 2692 ∨ k.val = 2693 ∨ k.val = 2694 ∨ k.val = 2695 ∨ k.val = 2696 ∨ k.val = 2697 ∨ k.val = 2698 ∨ k.val = 2699 ∨ k.val = 2700 ∨ k.val = 2701 ∨ k.val = 2702 ∨ k.val = 2703 ∨ k.val = 2704 ∨ k.val = 2705 ∨ k.val = 2706 ∨ k.val = 2707 ∨ k.val = 2708 ∨ k.val = 2709 ∨ k.val = 2710 ∨ k.val = 2711 ∨ k.val = 2712 ∨ k.val = 2713 ∨ k.val = 2714 ∨ k.val = 2715 ∨ k.val = 2716 ∨ k.val = 2717 ∨ k.val = 2718 ∨ k.val = 2719 := by omega
  rcases heq with h2688 | h2689 | h2690 | h2691 | h2692 | h2693 | h2694 | h2695 | h2696 | h2697 | h2698 | h2699 | h2700 | h2701 | h2702 | h2703 | h2704 | h2705 | h2706 | h2707 | h2708 | h2709 | h2710 | h2711 | h2712 | h2713 | h2714 | h2715 | h2716 | h2717 | h2718 | h2719
  · have he : k = (2688 : Fin 2886) := Fin.ext h2688
    subst k
    rw [keyMomentRowsAt2688]
    exact keyMoment2688 B hB
  · have he : k = (2689 : Fin 2886) := Fin.ext h2689
    subst k
    rw [keyMomentRowsAt2689]
    exact keyMoment2689 B hB
  · have he : k = (2690 : Fin 2886) := Fin.ext h2690
    subst k
    rw [keyMomentRowsAt2690]
    exact keyMoment2690 B hB
  · have he : k = (2691 : Fin 2886) := Fin.ext h2691
    subst k
    rw [keyMomentRowsAt2691]
    exact keyMoment2691 B hB
  · have he : k = (2692 : Fin 2886) := Fin.ext h2692
    subst k
    rw [keyMomentRowsAt2692]
    exact keyMoment2692 B hB
  · have he : k = (2693 : Fin 2886) := Fin.ext h2693
    subst k
    rw [keyMomentRowsAt2693]
    exact keyMoment2693 B hB
  · have he : k = (2694 : Fin 2886) := Fin.ext h2694
    subst k
    rw [keyMomentRowsAt2694]
    exact keyMoment2694 B hB
  · have he : k = (2695 : Fin 2886) := Fin.ext h2695
    subst k
    rw [keyMomentRowsAt2695]
    exact keyMoment2695 B hB
  · have he : k = (2696 : Fin 2886) := Fin.ext h2696
    subst k
    rw [keyMomentRowsAt2696]
    exact keyMoment2696 B hB
  · have he : k = (2697 : Fin 2886) := Fin.ext h2697
    subst k
    rw [keyMomentRowsAt2697]
    exact keyMoment2697 B hB
  · have he : k = (2698 : Fin 2886) := Fin.ext h2698
    subst k
    rw [keyMomentRowsAt2698]
    exact keyMoment2698 B hB
  · have he : k = (2699 : Fin 2886) := Fin.ext h2699
    subst k
    rw [keyMomentRowsAt2699]
    exact keyMoment2699 B hB
  · have he : k = (2700 : Fin 2886) := Fin.ext h2700
    subst k
    rw [keyMomentRowsAt2700]
    exact keyMoment2700 B hB
  · have he : k = (2701 : Fin 2886) := Fin.ext h2701
    subst k
    rw [keyMomentRowsAt2701]
    exact keyMoment2701 B hB
  · have he : k = (2702 : Fin 2886) := Fin.ext h2702
    subst k
    rw [keyMomentRowsAt2702]
    exact keyMoment2702 B hB
  · have he : k = (2703 : Fin 2886) := Fin.ext h2703
    subst k
    rw [keyMomentRowsAt2703]
    exact keyMoment2703 B hB
  · have he : k = (2704 : Fin 2886) := Fin.ext h2704
    subst k
    rw [keyMomentRowsAt2704]
    exact keyMoment2704 B hB
  · have he : k = (2705 : Fin 2886) := Fin.ext h2705
    subst k
    rw [keyMomentRowsAt2705]
    exact keyMoment2705 B hB
  · have he : k = (2706 : Fin 2886) := Fin.ext h2706
    subst k
    rw [keyMomentRowsAt2706]
    exact keyMoment2706 B hB
  · have he : k = (2707 : Fin 2886) := Fin.ext h2707
    subst k
    rw [keyMomentRowsAt2707]
    exact keyMoment2707 B hB
  · have he : k = (2708 : Fin 2886) := Fin.ext h2708
    subst k
    rw [keyMomentRowsAt2708]
    exact keyMoment2708 B hB
  · have he : k = (2709 : Fin 2886) := Fin.ext h2709
    subst k
    rw [keyMomentRowsAt2709]
    exact keyMoment2709 B hB
  · have he : k = (2710 : Fin 2886) := Fin.ext h2710
    subst k
    rw [keyMomentRowsAt2710]
    exact keyMoment2710 B hB
  · have he : k = (2711 : Fin 2886) := Fin.ext h2711
    subst k
    rw [keyMomentRowsAt2711]
    exact keyMoment2711 B hB
  · have he : k = (2712 : Fin 2886) := Fin.ext h2712
    subst k
    rw [keyMomentRowsAt2712]
    exact keyMoment2712 B hB
  · have he : k = (2713 : Fin 2886) := Fin.ext h2713
    subst k
    rw [keyMomentRowsAt2713]
    exact keyMoment2713 B hB
  · have he : k = (2714 : Fin 2886) := Fin.ext h2714
    subst k
    rw [keyMomentRowsAt2714]
    exact keyMoment2714 B hB
  · have he : k = (2715 : Fin 2886) := Fin.ext h2715
    subst k
    rw [keyMomentRowsAt2715]
    exact keyMoment2715 B hB
  · have he : k = (2716 : Fin 2886) := Fin.ext h2716
    subst k
    rw [keyMomentRowsAt2716]
    exact keyMoment2716 B hB
  · have he : k = (2717 : Fin 2886) := Fin.ext h2717
    subst k
    rw [keyMomentRowsAt2717]
    exact keyMoment2717 B hB
  · have he : k = (2718 : Fin 2886) := Fin.ext h2718
    subst k
    rw [keyMomentRowsAt2718]
    exact keyMoment2718 B hB
  · have he : k = (2719 : Fin 2886) := Fin.ext h2719
    subst k
    rw [keyMomentRowsAt2719]
    exact keyMoment2719 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound84_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound84_e_oai
