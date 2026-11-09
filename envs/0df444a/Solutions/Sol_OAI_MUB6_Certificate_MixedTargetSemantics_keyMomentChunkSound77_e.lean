-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound77_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:03:50.477286+00:00
-- url     : https://prove2.me/submissions/8348d898-f347-4281-868f-0311bfed89a1

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E113
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical330
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical42240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42240 raw42240Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw42240 raw42240Labels = mixedMoment B raw42240step0 raw42240step0Labels := by
      have ha : raw42240step0 = (fun i j => raw42240 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42240step0 raw42240; decide +kernel
      have hl : raw42240step0Labels = raw42240Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42240 raw42240Labels permutation682 permutation2
    mixedMoment B raw42240step0 raw42240step0Labels = mixedMoment B raw42240step1 raw42240step1Labels := by
      have ha : raw42240step1 = -raw42240step0 := by apply Matrix.ext; change ∀ i j, raw42240step1 i j = -(raw42240step0 i j); unfold raw42240step1 raw42240step0; decide +kernel
      have hl : raw42240step1Labels = raw42240step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42240step1 raw42240step1Labels = mixedMoment B raw42240step2 raw42240step2Labels := by
      have ha : raw42240step2 = raw42240step1 := by apply Matrix.ext; unfold raw42240step2 raw42240step1; decide +kernel
      have hl : raw42240step1Labels = labelEmbedding1 ∘ raw42240step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42240step1 raw42240step1Labels raw42240step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

theorem canonical42241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42241 raw42241Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw42241 raw42241Labels = mixedMoment B raw42241step0 raw42241step0Labels := by
      have ha : raw42241step0 = (fun i j => raw42241 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42241step0 raw42241; decide +kernel
      have hl : raw42241step0Labels = raw42241Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42241 raw42241Labels permutation646 permutation7
    mixedMoment B raw42241step0 raw42241step0Labels = mixedMoment B raw42241step1 raw42241step1Labels := by
      have ha : raw42241step1 = raw42241step0 := by apply Matrix.ext; unfold raw42241step1 raw42241step0; decide +kernel
      have hl : raw42241step0Labels = labelEmbedding6 ∘ raw42241step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42241step0 raw42241step0Labels raw42241step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

theorem canonical42242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42242 raw42242Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw42242 raw42242Labels = mixedMoment B raw42242step0 raw42242step0Labels := by
      have ha : raw42242step0 = (fun i j => raw42242 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42242step0 raw42242; decide +kernel
      have hl : raw42242step0Labels = raw42242Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42242 raw42242Labels permutation682 permutation2
    mixedMoment B raw42242step0 raw42242step0Labels = mixedMoment B raw42242step1 raw42242step1Labels := by
      have ha : raw42242step1 = -raw42242step0 := by apply Matrix.ext; change ∀ i j, raw42242step1 i j = -(raw42242step0 i j); unfold raw42242step1 raw42242step0; decide +kernel
      have hl : raw42242step1Labels = raw42242step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42242step1 raw42242step1Labels = mixedMoment B raw42242step2 raw42242step2Labels := by
      have ha : raw42242step2 = raw42242step1 := by apply Matrix.ext; unfold raw42242step2 raw42242step1; decide +kernel
      have hl : raw42242step1Labels = labelEmbedding1 ∘ raw42242step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42242step1 raw42242step1Labels raw42242step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

theorem canonical42243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42243 raw42243Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw42243 raw42243Labels = mixedMoment B raw42243step0 raw42243step0Labels := by
      have ha : raw42243step0 = (fun i j => raw42243 (permutation643 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42243step0 raw42243; decide +kernel
      have hl : raw42243step0Labels = raw42243Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42243 raw42243Labels permutation643 permutation7
    mixedMoment B raw42243step0 raw42243step0Labels = mixedMoment B raw42243step1 raw42243step1Labels := by
      have ha : raw42243step1 = raw42243step0 := by apply Matrix.ext; unfold raw42243step1 raw42243step0; decide +kernel
      have hl : raw42243step0Labels = labelEmbedding6 ∘ raw42243step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42243step0 raw42243step0Labels raw42243step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

theorem canonical42244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42244 raw42244Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw42244 raw42244Labels = mixedMoment B raw42244step0 raw42244step0Labels := by
      have ha : raw42244step0 = (fun i j => raw42244 (permutation617 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42244step0 raw42244; decide +kernel
      have hl : raw42244step0Labels = raw42244Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42244 raw42244Labels permutation617 permutation4
    mixedMoment B raw42244step0 raw42244step0Labels = mixedMoment B raw42244step1 raw42244step1Labels := by
      have ha : raw42244step1 = raw42244step0 := by apply Matrix.ext; unfold raw42244step1 raw42244step0; decide +kernel
      have hl : raw42244step0Labels = labelEmbedding1 ∘ raw42244step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42244step0 raw42244step0Labels raw42244step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2718 node2718Labels := by rfl

theorem canonical42245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42245 raw42245Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw42245 raw42245Labels = mixedMoment B raw42245step0 raw42245step0Labels := by
      have ha : raw42245step0 = (fun i j => raw42245 (permutation617 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42245step0 raw42245; decide +kernel
      have hl : raw42245step0Labels = raw42245Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42245 raw42245Labels permutation617 permutation4
    mixedMoment B raw42245step0 raw42245step0Labels = mixedMoment B raw42245step1 raw42245step1Labels := by
      have ha : raw42245step1 = raw42245step0 := by apply Matrix.ext; unfold raw42245step1 raw42245step0; decide +kernel
      have hl : raw42245step0Labels = labelEmbedding10 ∘ raw42245step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42245step0 raw42245step0Labels raw42245step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

theorem canonical42246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42246 raw42246Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw42246 raw42246Labels = mixedMoment B raw42246step0 raw42246step0Labels := by
      have ha : raw42246step0 = (fun i j => raw42246 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42246step0 raw42246; decide +kernel
      have hl : raw42246step0Labels = raw42246Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42246 raw42246Labels permutation157 permutation2
    mixedMoment B raw42246step0 raw42246step0Labels = mixedMoment B raw42246step1 raw42246step1Labels := by
      have ha : raw42246step1 = raw42246step0 := by apply Matrix.ext; unfold raw42246step1 raw42246step0; decide +kernel
      have hl : raw42246step0Labels = labelEmbedding1 ∘ raw42246step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42246step0 raw42246step0Labels raw42246step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

theorem canonical42247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42247 raw42247Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw42247 raw42247Labels = mixedMoment B raw42247step0 raw42247step0Labels := by
      have ha : raw42247step0 = (fun i j => raw42247 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42247step0 raw42247; decide +kernel
      have hl : raw42247step0Labels = raw42247Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42247 raw42247Labels permutation157 permutation2
    mixedMoment B raw42247step0 raw42247step0Labels = mixedMoment B raw42247step1 raw42247step1Labels := by
      have ha : raw42247step1 = raw42247step0 := by apply Matrix.ext; unfold raw42247step1 raw42247step0; decide +kernel
      have hl : raw42247step0Labels = labelEmbedding8 ∘ raw42247step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42247step0 raw42247step0Labels raw42247step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

theorem canonical42248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42248 raw42248Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw42248 raw42248Labels = mixedMoment B raw42248step0 raw42248step0Labels := by
      have hz : ∀ j, raw42248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42248step0 = (fun i j => raw42248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42248step0 raw42248; decide +kernel
      have hl : raw42248step0Labels = raw42248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42248 raw42248Labels permutation434 hz
    mixedMoment B raw42248step0 raw42248step0Labels = mixedMoment B raw42248step1 raw42248step1Labels := by
      have hz : ∀ j, raw42248step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42248step1 = (fun i j => raw42248step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42248step1 raw42248step0; decide +kernel
      have hl : raw42248step1Labels = raw42248step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42248step0 raw42248step0Labels permutation80 hz
    mixedMoment B raw42248step1 raw42248step1Labels = mixedMoment B raw42248step2 raw42248step2Labels := by
      have ha : raw42248step2 = (fun i j => raw42248step1 (permutation28 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42248step2 raw42248step1; decide +kernel
      have hl : raw42248step2Labels = raw42248step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42248step1 raw42248step1Labels permutation28 permutation4
    mixedMoment B raw42248step2 raw42248step2Labels = mixedMoment B raw42248step3 raw42248step3Labels := by
      have ha : raw42248step3 = raw42248step2 := by apply Matrix.ext; unfold raw42248step3 raw42248step2; decide +kernel
      have hl : raw42248step2Labels = labelEmbedding1 ∘ raw42248step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42248step2 raw42248step2Labels raw42248step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

theorem canonical42249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42249 raw42249Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw42249 raw42249Labels = mixedMoment B raw42249step0 raw42249step0Labels := by
      have hz : ∀ j, raw42249 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42249step0 = (fun i j => raw42249 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42249step0 raw42249; decide +kernel
      have hl : raw42249step0Labels = raw42249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42249 raw42249Labels permutation434 hz
    mixedMoment B raw42249step0 raw42249step0Labels = mixedMoment B raw42249step1 raw42249step1Labels := by
      have hz : ∀ j, raw42249step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42249step1 = (fun i j => raw42249step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42249step1 raw42249step0; decide +kernel
      have hl : raw42249step1Labels = raw42249step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42249step0 raw42249step0Labels permutation80 hz
    mixedMoment B raw42249step1 raw42249step1Labels = mixedMoment B raw42249step2 raw42249step2Labels := by
      have ha : raw42249step2 = (fun i j => raw42249step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42249step2 raw42249step1; decide +kernel
      have hl : raw42249step2Labels = raw42249step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42249step1 raw42249step1Labels permutation28 permutation5
    mixedMoment B raw42249step2 raw42249step2Labels = mixedMoment B raw42249step3 raw42249step3Labels := by
      have ha : raw42249step3 = raw42249step2 := by apply Matrix.ext; unfold raw42249step3 raw42249step2; decide +kernel
      have hl : raw42249step2Labels = labelEmbedding9 ∘ raw42249step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42249step2 raw42249step2Labels raw42249step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

theorem canonical42250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42250 raw42250Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw42250 raw42250Labels = mixedMoment B raw42250step0 raw42250step0Labels := by
      have hz : ∀ j, raw42250 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42250step0 = (fun i j => raw42250 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42250step0 raw42250; decide +kernel
      have hl : raw42250step0Labels = raw42250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42250 raw42250Labels permutation434 hz
    mixedMoment B raw42250step0 raw42250step0Labels = mixedMoment B raw42250step1 raw42250step1Labels := by
      have hz : ∀ j, raw42250step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42250step1 = (fun i j => raw42250step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42250step1 raw42250step0; decide +kernel
      have hl : raw42250step1Labels = raw42250step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42250step0 raw42250step0Labels permutation80 hz
    mixedMoment B raw42250step1 raw42250step1Labels = mixedMoment B raw42250step2 raw42250step2Labels := by
      have ha : raw42250step2 = (fun i j => raw42250step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42250step2 raw42250step1; decide +kernel
      have hl : raw42250step2Labels = raw42250step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42250step1 raw42250step1Labels permutation22 permutation4
    mixedMoment B raw42250step2 raw42250step2Labels = mixedMoment B raw42250step3 raw42250step3Labels := by
      have ha : raw42250step3 = raw42250step2 := by apply Matrix.ext; unfold raw42250step3 raw42250step2; decide +kernel
      have hl : raw42250step2Labels = labelEmbedding1 ∘ raw42250step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42250step2 raw42250step2Labels raw42250step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical42251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42251 raw42251Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw42251 raw42251Labels = mixedMoment B raw42251step0 raw42251step0Labels := by
      have hz : ∀ j, raw42251 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42251step0 = (fun i j => raw42251 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42251step0 raw42251; decide +kernel
      have hl : raw42251step0Labels = raw42251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42251 raw42251Labels permutation434 hz
    mixedMoment B raw42251step0 raw42251step0Labels = mixedMoment B raw42251step1 raw42251step1Labels := by
      have hz : ∀ j, raw42251step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42251step1 = (fun i j => raw42251step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42251step1 raw42251step0; decide +kernel
      have hl : raw42251step1Labels = raw42251step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42251step0 raw42251step0Labels permutation80 hz
    mixedMoment B raw42251step1 raw42251step1Labels = mixedMoment B raw42251step2 raw42251step2Labels := by
      have ha : raw42251step2 = (fun i j => raw42251step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42251step2 raw42251step1; decide +kernel
      have hl : raw42251step2Labels = raw42251step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42251step1 raw42251step1Labels permutation26 permutation6
    _ = mixedMoment B node4617 node4617Labels := by rfl

theorem canonical42252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42252 raw42252Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw42252 raw42252Labels = mixedMoment B raw42252step0 raw42252step0Labels := by
      have hz : ∀ j, raw42252 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42252step0 = (fun i j => raw42252 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42252step0 raw42252; decide +kernel
      have hl : raw42252step0Labels = raw42252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42252 raw42252Labels permutation346 hz
    mixedMoment B raw42252step0 raw42252step0Labels = mixedMoment B raw42252step1 raw42252step1Labels := by
      have ha : raw42252step1 = (fun i j => raw42252step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42252step1 raw42252step0; decide +kernel
      have hl : raw42252step1Labels = raw42252step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42252step0 raw42252step0Labels permutation104 permutation4
    mixedMoment B raw42252step1 raw42252step1Labels = mixedMoment B raw42252step2 raw42252step2Labels := by
      have ha : raw42252step2 = -raw42252step1 := by apply Matrix.ext; change ∀ i j, raw42252step2 i j = -(raw42252step1 i j); unfold raw42252step2 raw42252step1; decide +kernel
      have hl : raw42252step2Labels = raw42252step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42252step2 raw42252step2Labels = mixedMoment B raw42252step3 raw42252step3Labels := by
      have ha : raw42252step3 = raw42252step2 := by apply Matrix.ext; unfold raw42252step3 raw42252step2; decide +kernel
      have hl : raw42252step2Labels = labelEmbedding1 ∘ raw42252step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42252step2 raw42252step2Labels raw42252step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical42253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42253 raw42253Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw42253 raw42253Labels = mixedMoment B raw42253step0 raw42253step0Labels := by
      have hz : ∀ j, raw42253 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42253step0 = (fun i j => raw42253 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42253step0 raw42253; decide +kernel
      have hl : raw42253step0Labels = raw42253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42253 raw42253Labels permutation346 hz
    mixedMoment B raw42253step0 raw42253step0Labels = mixedMoment B raw42253step1 raw42253step1Labels := by
      have ha : raw42253step1 = (fun i j => raw42253step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42253step1 raw42253step0; decide +kernel
      have hl : raw42253step1Labels = raw42253step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42253step0 raw42253step0Labels permutation122 permutation6
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical42254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42254 raw42254Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw42254 raw42254Labels = mixedMoment B raw42254step0 raw42254step0Labels := by
      have hz : ∀ j, raw42254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42254step0 = (fun i j => raw42254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42254step0 raw42254; decide +kernel
      have hl : raw42254step0Labels = raw42254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42254 raw42254Labels permutation346 hz
    mixedMoment B raw42254step0 raw42254step0Labels = mixedMoment B raw42254step1 raw42254step1Labels := by
      have ha : raw42254step1 = (fun i j => raw42254step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42254step1 raw42254step0; decide +kernel
      have hl : raw42254step1Labels = raw42254step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42254step0 raw42254step0Labels permutation151 permutation2
    mixedMoment B raw42254step1 raw42254step1Labels = mixedMoment B raw42254step2 raw42254step2Labels := by
      have ha : raw42254step2 = -raw42254step1 := by apply Matrix.ext; change ∀ i j, raw42254step2 i j = -(raw42254step1 i j); unfold raw42254step2 raw42254step1; decide +kernel
      have hl : raw42254step2Labels = raw42254step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42254step2 raw42254step2Labels = mixedMoment B raw42254step3 raw42254step3Labels := by
      have ha : raw42254step3 = raw42254step2 := by apply Matrix.ext; unfold raw42254step3 raw42254step2; decide +kernel
      have hl : raw42254step2Labels = labelEmbedding1 ∘ raw42254step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42254step2 raw42254step2Labels raw42254step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3303 node3303Labels := by rfl

theorem canonical42255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42255 raw42255Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw42255 raw42255Labels = mixedMoment B raw42255step0 raw42255step0Labels := by
      have hz : ∀ j, raw42255 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42255step0 = (fun i j => raw42255 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42255step0 raw42255; decide +kernel
      have hl : raw42255step0Labels = raw42255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42255 raw42255Labels permutation346 hz
    mixedMoment B raw42255step0 raw42255step0Labels = mixedMoment B raw42255step1 raw42255step1Labels := by
      have ha : raw42255step1 = (fun i j => raw42255step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42255step1 raw42255step0; decide +kernel
      have hl : raw42255step1Labels = raw42255step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42255step0 raw42255step0Labels permutation128 permutation6
    _ = mixedMoment B node4616 node4616Labels := by rfl

theorem canonical42256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42256 raw42256Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw42256 raw42256Labels = mixedMoment B raw42256step0 raw42256step0Labels := by
      have hz : ∀ j, raw42256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42256step0 = (fun i j => raw42256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42256step0 raw42256; decide +kernel
      have hl : raw42256step0Labels = raw42256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42256 raw42256Labels permutation346 hz
    mixedMoment B raw42256step0 raw42256step0Labels = mixedMoment B raw42256step1 raw42256step1Labels := by
      have ha : raw42256step1 = (fun i j => raw42256step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42256step1 raw42256step0; decide +kernel
      have hl : raw42256step1Labels = raw42256step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42256step0 raw42256step0Labels permutation151 permutation2
    mixedMoment B raw42256step1 raw42256step1Labels = mixedMoment B raw42256step2 raw42256step2Labels := by
      have ha : raw42256step2 = -raw42256step1 := by apply Matrix.ext; change ∀ i j, raw42256step2 i j = -(raw42256step1 i j); unfold raw42256step2 raw42256step1; decide +kernel
      have hl : raw42256step2Labels = raw42256step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42256step2 raw42256step2Labels = mixedMoment B raw42256step3 raw42256step3Labels := by
      have ha : raw42256step3 = raw42256step2 := by apply Matrix.ext; unfold raw42256step3 raw42256step2; decide +kernel
      have hl : raw42256step2Labels = labelEmbedding1 ∘ raw42256step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42256step2 raw42256step2Labels raw42256step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

theorem canonical42257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42257 raw42257Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw42257 raw42257Labels = mixedMoment B raw42257step0 raw42257step0Labels := by
      have hz : ∀ j, raw42257 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42257step0 = (fun i j => raw42257 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42257step0 raw42257; decide +kernel
      have hl : raw42257step0Labels = raw42257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42257 raw42257Labels permutation346 hz
    mixedMoment B raw42257step0 raw42257step0Labels = mixedMoment B raw42257step1 raw42257step1Labels := by
      have ha : raw42257step1 = (fun i j => raw42257step0 (permutation148 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42257step1 raw42257step0; decide +kernel
      have hl : raw42257step1Labels = raw42257step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42257step0 raw42257step0Labels permutation148 permutation7
    mixedMoment B raw42257step1 raw42257step1Labels = mixedMoment B raw42257step2 raw42257step2Labels := by
      have ha : raw42257step2 = raw42257step1 := by apply Matrix.ext; unfold raw42257step2 raw42257step1; decide +kernel
      have hl : raw42257step1Labels = labelEmbedding6 ∘ raw42257step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42257step1 raw42257step1Labels raw42257step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

theorem canonical42258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42258 raw42258Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw42258 raw42258Labels = mixedMoment B raw42258step0 raw42258step0Labels := by
      have hz : ∀ j, raw42258 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42258step0 = (fun i j => raw42258 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42258step0 raw42258; decide +kernel
      have hl : raw42258step0Labels = raw42258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42258 raw42258Labels permutation346 hz
    mixedMoment B raw42258step0 raw42258step0Labels = mixedMoment B raw42258step1 raw42258step1Labels := by
      have ha : raw42258step1 = (fun i j => raw42258step0 (permutation138 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42258step1 raw42258step0; decide +kernel
      have hl : raw42258step1Labels = raw42258step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42258step0 raw42258step0Labels permutation138 permutation4
    mixedMoment B raw42258step1 raw42258step1Labels = mixedMoment B raw42258step2 raw42258step2Labels := by
      have ha : raw42258step2 = raw42258step1 := by apply Matrix.ext; unfold raw42258step2 raw42258step1; decide +kernel
      have hl : raw42258step1Labels = labelEmbedding1 ∘ raw42258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42258step1 raw42258step1Labels raw42258step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical42259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42259 raw42259Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw42259 raw42259Labels = mixedMoment B raw42259step0 raw42259step0Labels := by
      have hz : ∀ j, raw42259 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42259step0 = (fun i j => raw42259 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42259step0 raw42259; decide +kernel
      have hl : raw42259step0Labels = raw42259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42259 raw42259Labels permutation346 hz
    mixedMoment B raw42259step0 raw42259step0Labels = mixedMoment B raw42259step1 raw42259step1Labels := by
      have ha : raw42259step1 = (fun i j => raw42259step0 (permutation92 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42259step1 raw42259step0; decide +kernel
      have hl : raw42259step1Labels = raw42259step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42259step0 raw42259step0Labels permutation92 permutation6
    _ = mixedMoment B node5161 node5161Labels := by rfl

theorem canonical42260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42260 raw42260Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw42260 raw42260Labels = mixedMoment B raw42260step0 raw42260step0Labels := by
      have hz : ∀ j, raw42260 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42260step0 = (fun i j => raw42260 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42260step0 raw42260; decide +kernel
      have hl : raw42260step0Labels = raw42260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42260 raw42260Labels permutation346 hz
    mixedMoment B raw42260step0 raw42260step0Labels = mixedMoment B raw42260step1 raw42260step1Labels := by
      have ha : raw42260step1 = (fun i j => raw42260step0 (permutation80 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42260step1 raw42260step0; decide +kernel
      have hl : raw42260step1Labels = raw42260step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42260step0 raw42260step0Labels permutation80 permutation4
    mixedMoment B raw42260step1 raw42260step1Labels = mixedMoment B raw42260step2 raw42260step2Labels := by
      have ha : raw42260step2 = -raw42260step1 := by apply Matrix.ext; change ∀ i j, raw42260step2 i j = -(raw42260step1 i j); unfold raw42260step2 raw42260step1; decide +kernel
      have hl : raw42260step2Labels = raw42260step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42260step2 raw42260step2Labels = mixedMoment B raw42260step3 raw42260step3Labels := by
      have ha : raw42260step3 = raw42260step2 := by apply Matrix.ext; unfold raw42260step3 raw42260step2; decide +kernel
      have hl : raw42260step2Labels = labelEmbedding1 ∘ raw42260step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42260step2 raw42260step2Labels raw42260step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical42261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42261 raw42261Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw42261 raw42261Labels = mixedMoment B raw42261step0 raw42261step0Labels := by
      have hz : ∀ j, raw42261 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42261step0 = (fun i j => raw42261 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42261step0 raw42261; decide +kernel
      have hl : raw42261step0Labels = raw42261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42261 raw42261Labels permutation346 hz
    mixedMoment B raw42261step0 raw42261step0Labels = mixedMoment B raw42261step1 raw42261step1Labels := by
      have ha : raw42261step1 = (fun i j => raw42261step0 (permutation92 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42261step1 raw42261step0; decide +kernel
      have hl : raw42261step1Labels = raw42261step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42261step0 raw42261step0Labels permutation92 permutation6
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical42262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42262 raw42262Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw42262 raw42262Labels = mixedMoment B raw42262step0 raw42262step0Labels := by
      have hz : ∀ j, raw42262 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42262step0 = (fun i j => raw42262 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42262step0 raw42262; decide +kernel
      have hl : raw42262step0Labels = raw42262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42262 raw42262Labels permutation346 hz
    mixedMoment B raw42262step0 raw42262step0Labels = mixedMoment B raw42262step1 raw42262step1Labels := by
      have ha : raw42262step1 = (fun i j => raw42262step0 (permutation134 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42262step1 raw42262step0; decide +kernel
      have hl : raw42262step1Labels = raw42262step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42262step0 raw42262step0Labels permutation134 permutation4
    mixedMoment B raw42262step1 raw42262step1Labels = mixedMoment B raw42262step2 raw42262step2Labels := by
      have ha : raw42262step2 = raw42262step1 := by apply Matrix.ext; unfold raw42262step2 raw42262step1; decide +kernel
      have hl : raw42262step1Labels = labelEmbedding1 ∘ raw42262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42262step1 raw42262step1Labels raw42262step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2736 node2736Labels := by rfl

theorem canonical42263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42263 raw42263Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw42263 raw42263Labels = mixedMoment B raw42263step0 raw42263step0Labels := by
      have hz : ∀ j, raw42263 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42263step0 = (fun i j => raw42263 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42263step0 raw42263; decide +kernel
      have hl : raw42263step0Labels = raw42263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42263 raw42263Labels permutation346 hz
    mixedMoment B raw42263step0 raw42263step0Labels = mixedMoment B raw42263step1 raw42263step1Labels := by
      have ha : raw42263step1 = (fun i j => raw42263step0 (permutation134 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42263step1 raw42263step0; decide +kernel
      have hl : raw42263step1Labels = raw42263step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42263step0 raw42263step0Labels permutation134 permutation4
    mixedMoment B raw42263step1 raw42263step1Labels = mixedMoment B raw42263step2 raw42263step2Labels := by
      have ha : raw42263step2 = raw42263step1 := by apply Matrix.ext; unfold raw42263step2 raw42263step1; decide +kernel
      have hl : raw42263step1Labels = labelEmbedding10 ∘ raw42263step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42263step1 raw42263step1Labels raw42263step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

theorem canonical42264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42264 raw42264Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw42264 raw42264Labels = mixedMoment B raw42264step0 raw42264step0Labels := by
      have ha : raw42264step0 = (fun i j => raw42264 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42264step0 raw42264; decide +kernel
      have hl : raw42264step0Labels = raw42264Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42264 raw42264Labels permutation682 permutation2
    mixedMoment B raw42264step0 raw42264step0Labels = mixedMoment B raw42264step1 raw42264step1Labels := by
      have ha : raw42264step1 = -raw42264step0 := by apply Matrix.ext; change ∀ i j, raw42264step1 i j = -(raw42264step0 i j); unfold raw42264step1 raw42264step0; decide +kernel
      have hl : raw42264step1Labels = raw42264step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42264step1 raw42264step1Labels = mixedMoment B raw42264step2 raw42264step2Labels := by
      have ha : raw42264step2 = raw42264step1 := by apply Matrix.ext; unfold raw42264step2 raw42264step1; decide +kernel
      have hl : raw42264step1Labels = labelEmbedding1 ∘ raw42264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42264step1 raw42264step1Labels raw42264step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical42265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42265 raw42265Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw42265 raw42265Labels = mixedMoment B raw42265step0 raw42265step0Labels := by
      have ha : raw42265step0 = (fun i j => raw42265 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42265step0 raw42265; decide +kernel
      have hl : raw42265step0Labels = raw42265Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42265 raw42265Labels permutation682 permutation7
    mixedMoment B raw42265step0 raw42265step0Labels = mixedMoment B raw42265step1 raw42265step1Labels := by
      have ha : raw42265step1 = raw42265step0 := by apply Matrix.ext; unfold raw42265step1 raw42265step0; decide +kernel
      have hl : raw42265step0Labels = labelEmbedding6 ∘ raw42265step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42265step0 raw42265step0Labels raw42265step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

theorem canonical42266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42266 raw42266Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw42266 raw42266Labels = mixedMoment B raw42266step0 raw42266step0Labels := by
      have ha : raw42266step0 = (fun i j => raw42266 (permutation443 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42266step0 raw42266; decide +kernel
      have hl : raw42266step0Labels = raw42266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42266 raw42266Labels permutation443 permutation4
    mixedMoment B raw42266step0 raw42266step0Labels = mixedMoment B raw42266step1 raw42266step1Labels := by
      have ha : raw42266step1 = -raw42266step0 := by apply Matrix.ext; change ∀ i j, raw42266step1 i j = -(raw42266step0 i j); unfold raw42266step1 raw42266step0; decide +kernel
      have hl : raw42266step1Labels = raw42266step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42266step1 raw42266step1Labels = mixedMoment B raw42266step2 raw42266step2Labels := by
      have ha : raw42266step2 = raw42266step1 := by apply Matrix.ext; unfold raw42266step2 raw42266step1; decide +kernel
      have hl : raw42266step1Labels = labelEmbedding1 ∘ raw42266step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42266step1 raw42266step1Labels raw42266step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

theorem canonical42267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42267 raw42267Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw42267 raw42267Labels = mixedMoment B raw42267step0 raw42267step0Labels := by
      have ha : raw42267step0 = (fun i j => raw42267 (permutation484 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42267step0 raw42267; decide +kernel
      have hl : raw42267step0Labels = raw42267Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42267 raw42267Labels permutation484 permutation6
    _ = mixedMoment B node5160 node5160Labels := by rfl

theorem canonical42268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42268 raw42268Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw42268 raw42268Labels = mixedMoment B raw42268step0 raw42268step0Labels := by
      have ha : raw42268step0 = (fun i j => raw42268 (permutation437 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42268step0 raw42268; decide +kernel
      have hl : raw42268step0Labels = raw42268Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42268 raw42268Labels permutation437 permutation4
    mixedMoment B raw42268step0 raw42268step0Labels = mixedMoment B raw42268step1 raw42268step1Labels := by
      have ha : raw42268step1 = -raw42268step0 := by apply Matrix.ext; change ∀ i j, raw42268step1 i j = -(raw42268step0 i j); unfold raw42268step1 raw42268step0; decide +kernel
      have hl : raw42268step1Labels = raw42268step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42268step1 raw42268step1Labels = mixedMoment B raw42268step2 raw42268step2Labels := by
      have ha : raw42268step2 = raw42268step1 := by apply Matrix.ext; unfold raw42268step2 raw42268step1; decide +kernel
      have hl : raw42268step1Labels = labelEmbedding1 ∘ raw42268step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42268step1 raw42268step1Labels raw42268step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

theorem canonical42269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42269 raw42269Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw42269 raw42269Labels = mixedMoment B raw42269step0 raw42269step0Labels := by
      have ha : raw42269step0 = (fun i j => raw42269 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42269step0 raw42269; decide +kernel
      have hl : raw42269step0Labels = raw42269Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42269 raw42269Labels permutation499 permutation6
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical42270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42270 raw42270Labels = mixedMoment B node3973 node3973Labels := by
  calc
    mixedMoment B raw42270 raw42270Labels = mixedMoment B raw42270step0 raw42270step0Labels := by
      have ha : raw42270step0 = (fun i j => raw42270 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42270step0 raw42270; decide +kernel
      have hl : raw42270step0Labels = raw42270Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42270 raw42270Labels permutation156 permutation2
    mixedMoment B raw42270step0 raw42270step0Labels = mixedMoment B raw42270step1 raw42270step1Labels := by
      have ha : raw42270step1 = raw42270step0 := by apply Matrix.ext; unfold raw42270step1 raw42270step0; decide +kernel
      have hl : raw42270step0Labels = labelEmbedding1 ∘ raw42270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42270step0 raw42270step0Labels raw42270step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3973 node3973Labels := by rfl

theorem canonical42271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42271 raw42271Labels = mixedMoment B node5461 node5461Labels := by
  calc
    mixedMoment B raw42271 raw42271Labels = mixedMoment B raw42271step0 raw42271step0Labels := by
      have ha : raw42271step0 = (fun i j => raw42271 (permutation484 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42271step0 raw42271; decide +kernel
      have hl : raw42271step0Labels = raw42271Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42271 raw42271Labels permutation484 permutation6
    _ = mixedMoment B node5461 node5461Labels := by rfl

theorem canonical42272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42272 raw42272Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw42272 raw42272Labels = mixedMoment B raw42272step0 raw42272step0Labels := by
      have ha : raw42272step0 = (fun i j => raw42272 (permutation444 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42272step0 raw42272; decide +kernel
      have hl : raw42272step0Labels = raw42272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42272 raw42272Labels permutation444 permutation4
    mixedMoment B raw42272step0 raw42272step0Labels = mixedMoment B raw42272step1 raw42272step1Labels := by
      have ha : raw42272step1 = -raw42272step0 := by apply Matrix.ext; change ∀ i j, raw42272step1 i j = -(raw42272step0 i j); unfold raw42272step1 raw42272step0; decide +kernel
      have hl : raw42272step1Labels = raw42272step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42272step1 raw42272step1Labels = mixedMoment B raw42272step2 raw42272step2Labels := by
      have ha : raw42272step2 = raw42272step1 := by apply Matrix.ext; unfold raw42272step2 raw42272step1; decide +kernel
      have hl : raw42272step1Labels = labelEmbedding1 ∘ raw42272step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42272step1 raw42272step1Labels raw42272step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

theorem canonical42273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42273 raw42273Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw42273 raw42273Labels = mixedMoment B raw42273step0 raw42273step0Labels := by
      have ha : raw42273step0 = (fun i j => raw42273 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42273step0 raw42273; decide +kernel
      have hl : raw42273step0Labels = raw42273Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42273 raw42273Labels permutation499 permutation6
    _ = mixedMoment B node5144 node5144Labels := by rfl

theorem canonical42274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42274 raw42274Labels = mixedMoment B node3842 node3842Labels := by
  calc
    mixedMoment B raw42274 raw42274Labels = mixedMoment B raw42274step0 raw42274step0Labels := by
      have ha : raw42274step0 = (fun i j => raw42274 (permutation419 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42274step0 raw42274; decide +kernel
      have hl : raw42274step0Labels = raw42274Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42274 raw42274Labels permutation419 permutation4
    mixedMoment B raw42274step0 raw42274step0Labels = mixedMoment B raw42274step1 raw42274step1Labels := by
      have ha : raw42274step1 = raw42274step0 := by apply Matrix.ext; unfold raw42274step1 raw42274step0; decide +kernel
      have hl : raw42274step0Labels = labelEmbedding1 ∘ raw42274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42274step0 raw42274step0Labels raw42274step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3842 node3842Labels := by rfl

theorem canonical42275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42275 raw42275Labels = mixedMoment B node5419 node5419Labels := by
  calc
    mixedMoment B raw42275 raw42275Labels = mixedMoment B raw42275step0 raw42275step0Labels := by
      have ha : raw42275step0 = (fun i j => raw42275 (permutation370 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42275step0 raw42275; decide +kernel
      have hl : raw42275step0Labels = raw42275Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42275 raw42275Labels permutation370 permutation6
    mixedMoment B raw42275step0 raw42275step0Labels = mixedMoment B raw42275step1 raw42275step1Labels := by
      have ha : raw42275step1 = -raw42275step0 := by apply Matrix.ext; change ∀ i j, raw42275step1 i j = -(raw42275step0 i j); unfold raw42275step1 raw42275step0; decide +kernel
      have hl : raw42275step1Labels = raw42275step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5419 node5419Labels := by rfl

theorem canonical42276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42276 raw42276Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw42276 raw42276Labels = mixedMoment B raw42276step0 raw42276step0Labels := by
      have hz : ∀ j, raw42276 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42276step0 = (fun i j => raw42276 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42276step0 raw42276; decide +kernel
      have hl : raw42276step0Labels = raw42276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42276 raw42276Labels permutation434 hz
    mixedMoment B raw42276step0 raw42276step0Labels = mixedMoment B raw42276step1 raw42276step1Labels := by
      have ha : raw42276step1 = (fun i j => raw42276step0 (permutation82 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42276step1 raw42276step0; decide +kernel
      have hl : raw42276step1Labels = raw42276step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42276step0 raw42276step0Labels permutation82 permutation4
    mixedMoment B raw42276step1 raw42276step1Labels = mixedMoment B raw42276step2 raw42276step2Labels := by
      have ha : raw42276step2 = -raw42276step1 := by apply Matrix.ext; change ∀ i j, raw42276step2 i j = -(raw42276step1 i j); unfold raw42276step2 raw42276step1; decide +kernel
      have hl : raw42276step2Labels = raw42276step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42276step2 raw42276step2Labels = mixedMoment B raw42276step3 raw42276step3Labels := by
      have ha : raw42276step3 = raw42276step2 := by apply Matrix.ext; unfold raw42276step3 raw42276step2; decide +kernel
      have hl : raw42276step2Labels = labelEmbedding1 ∘ raw42276step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42276step2 raw42276step2Labels raw42276step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

theorem canonical42277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42277 raw42277Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw42277 raw42277Labels = mixedMoment B raw42277step0 raw42277step0Labels := by
      have hz : ∀ j, raw42277 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42277step0 = (fun i j => raw42277 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42277step0 raw42277; decide +kernel
      have hl : raw42277step0Labels = raw42277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42277 raw42277Labels permutation434 hz
    mixedMoment B raw42277step0 raw42277step0Labels = mixedMoment B raw42277step1 raw42277step1Labels := by
      have ha : raw42277step1 = (fun i j => raw42277step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42277step1 raw42277step0; decide +kernel
      have hl : raw42277step1Labels = raw42277step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42277step0 raw42277step0Labels permutation151 permutation3
    mixedMoment B raw42277step1 raw42277step1Labels = mixedMoment B raw42277step2 raw42277step2Labels := by
      have ha : raw42277step2 = -raw42277step1 := by apply Matrix.ext; change ∀ i j, raw42277step2 i j = -(raw42277step1 i j); unfold raw42277step2 raw42277step1; decide +kernel
      have hl : raw42277step2Labels = raw42277step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42277step2 raw42277step2Labels = mixedMoment B raw42277step3 raw42277step3Labels := by
      have ha : raw42277step3 = raw42277step2 := by apply Matrix.ext; unfold raw42277step3 raw42277step2; decide +kernel
      have hl : raw42277step2Labels = labelEmbedding7 ∘ raw42277step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42277step2 raw42277step2Labels raw42277step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

theorem canonical42278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42278 raw42278Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw42278 raw42278Labels = mixedMoment B raw42278step0 raw42278step0Labels := by
      have hz : ∀ j, raw42278 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42278step0 = (fun i j => raw42278 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42278step0 raw42278; decide +kernel
      have hl : raw42278step0Labels = raw42278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42278 raw42278Labels permutation434 hz
    mixedMoment B raw42278step0 raw42278step0Labels = mixedMoment B raw42278step1 raw42278step1Labels := by
      have ha : raw42278step1 = (fun i j => raw42278step0 (permutation85 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42278step1 raw42278step0; decide +kernel
      have hl : raw42278step1Labels = raw42278step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42278step0 raw42278step0Labels permutation85 permutation4
    mixedMoment B raw42278step1 raw42278step1Labels = mixedMoment B raw42278step2 raw42278step2Labels := by
      have ha : raw42278step2 = -raw42278step1 := by apply Matrix.ext; change ∀ i j, raw42278step2 i j = -(raw42278step1 i j); unfold raw42278step2 raw42278step1; decide +kernel
      have hl : raw42278step2Labels = raw42278step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42278step2 raw42278step2Labels = mixedMoment B raw42278step3 raw42278step3Labels := by
      have ha : raw42278step3 = raw42278step2 := by apply Matrix.ext; unfold raw42278step3 raw42278step2; decide +kernel
      have hl : raw42278step2Labels = labelEmbedding1 ∘ raw42278step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42278step2 raw42278step2Labels raw42278step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

theorem canonical42279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42279 raw42279Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw42279 raw42279Labels = mixedMoment B raw42279step0 raw42279step0Labels := by
      have hz : ∀ j, raw42279 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42279step0 = (fun i j => raw42279 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42279step0 raw42279; decide +kernel
      have hl : raw42279step0Labels = raw42279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42279 raw42279Labels permutation434 hz
    mixedMoment B raw42279step0 raw42279step0Labels = mixedMoment B raw42279step1 raw42279step1Labels := by
      have ha : raw42279step1 = (fun i j => raw42279step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42279step1 raw42279step0; decide +kernel
      have hl : raw42279step1Labels = raw42279step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42279step0 raw42279step0Labels permutation102 permutation6
    _ = mixedMoment B node5446 node5446Labels := by rfl

theorem canonical42280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42280 raw42280Labels = mixedMoment B node3868 node3868Labels := by
  calc
    mixedMoment B raw42280 raw42280Labels = mixedMoment B raw42280step0 raw42280step0Labels := by
      have hz : ∀ j, raw42280 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42280step0 = (fun i j => raw42280 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42280step0 raw42280; decide +kernel
      have hl : raw42280step0Labels = raw42280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42280 raw42280Labels permutation434 hz
    mixedMoment B raw42280step0 raw42280step0Labels = mixedMoment B raw42280step1 raw42280step1Labels := by
      have ha : raw42280step1 = (fun i j => raw42280step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42280step1 raw42280step0; decide +kernel
      have hl : raw42280step1Labels = raw42280step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42280step0 raw42280step0Labels permutation151 permutation2
    mixedMoment B raw42280step1 raw42280step1Labels = mixedMoment B raw42280step2 raw42280step2Labels := by
      have ha : raw42280step2 = -raw42280step1 := by apply Matrix.ext; change ∀ i j, raw42280step2 i j = -(raw42280step1 i j); unfold raw42280step2 raw42280step1; decide +kernel
      have hl : raw42280step2Labels = raw42280step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42280step2 raw42280step2Labels = mixedMoment B raw42280step3 raw42280step3Labels := by
      have ha : raw42280step3 = raw42280step2 := by apply Matrix.ext; unfold raw42280step3 raw42280step2; decide +kernel
      have hl : raw42280step2Labels = labelEmbedding1 ∘ raw42280step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42280step2 raw42280step2Labels raw42280step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3868 node3868Labels := by rfl

theorem canonical42281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42281 raw42281Labels = mixedMoment B node5385 node5385Labels := by
  calc
    mixedMoment B raw42281 raw42281Labels = mixedMoment B raw42281step0 raw42281step0Labels := by
      have hz : ∀ j, raw42281 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42281step0 = (fun i j => raw42281 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42281step0 raw42281; decide +kernel
      have hl : raw42281step0Labels = raw42281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42281 raw42281Labels permutation434 hz
    mixedMoment B raw42281step0 raw42281step0Labels = mixedMoment B raw42281step1 raw42281step1Labels := by
      have ha : raw42281step1 = (fun i j => raw42281step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42281step1 raw42281step0; decide +kernel
      have hl : raw42281step1Labels = raw42281step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42281step0 raw42281step0Labels permutation99 permutation6
    _ = mixedMoment B node5385 node5385Labels := by rfl

theorem canonical42282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42282 raw42282Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw42282 raw42282Labels = mixedMoment B raw42282step0 raw42282step0Labels := by
      have ha : raw42282step0 = (fun i j => raw42282 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42282step0 raw42282; decide +kernel
      have hl : raw42282step0Labels = raw42282Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42282 raw42282Labels permutation682 permutation2
    mixedMoment B raw42282step0 raw42282step0Labels = mixedMoment B raw42282step1 raw42282step1Labels := by
      have ha : raw42282step1 = -raw42282step0 := by apply Matrix.ext; change ∀ i j, raw42282step1 i j = -(raw42282step0 i j); unfold raw42282step1 raw42282step0; decide +kernel
      have hl : raw42282step1Labels = raw42282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42282step1 raw42282step1Labels = mixedMoment B raw42282step2 raw42282step2Labels := by
      have ha : raw42282step2 = raw42282step1 := by apply Matrix.ext; unfold raw42282step2 raw42282step1; decide +kernel
      have hl : raw42282step1Labels = labelEmbedding1 ∘ raw42282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42282step1 raw42282step1Labels raw42282step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

theorem canonical42283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42283 raw42283Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw42283 raw42283Labels = mixedMoment B raw42283step0 raw42283step0Labels := by
      have ha : raw42283step0 = (fun i j => raw42283 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42283step0 raw42283; decide +kernel
      have hl : raw42283step0Labels = raw42283Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42283 raw42283Labels permutation645 permutation7
    mixedMoment B raw42283step0 raw42283step0Labels = mixedMoment B raw42283step1 raw42283step1Labels := by
      have ha : raw42283step1 = raw42283step0 := by apply Matrix.ext; unfold raw42283step1 raw42283step0; decide +kernel
      have hl : raw42283step0Labels = labelEmbedding6 ∘ raw42283step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42283step0 raw42283step0Labels raw42283step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

theorem canonical42284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42284 raw42284Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw42284 raw42284Labels = mixedMoment B raw42284step0 raw42284step0Labels := by
      have ha : raw42284step0 = (fun i j => raw42284 (permutation354 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42284step0 raw42284; decide +kernel
      have hl : raw42284step0Labels = raw42284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42284 raw42284Labels permutation354 permutation4
    mixedMoment B raw42284step0 raw42284step0Labels = mixedMoment B raw42284step1 raw42284step1Labels := by
      have ha : raw42284step1 = -raw42284step0 := by apply Matrix.ext; change ∀ i j, raw42284step1 i j = -(raw42284step0 i j); unfold raw42284step1 raw42284step0; decide +kernel
      have hl : raw42284step1Labels = raw42284step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42284step1 raw42284step1Labels = mixedMoment B raw42284step2 raw42284step2Labels := by
      have ha : raw42284step2 = raw42284step1 := by apply Matrix.ext; unfold raw42284step2 raw42284step1; decide +kernel
      have hl : raw42284step1Labels = labelEmbedding1 ∘ raw42284step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42284step1 raw42284step1Labels raw42284step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3869 node3869Labels := by rfl

theorem canonical42285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42285 raw42285Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw42285 raw42285Labels = mixedMoment B raw42285step0 raw42285step0Labels := by
      have ha : raw42285step0 = (fun i j => raw42285 (permutation390 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42285step0 raw42285; decide +kernel
      have hl : raw42285step0Labels = raw42285Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42285 raw42285Labels permutation390 permutation6
    _ = mixedMoment B node5414 node5414Labels := by rfl

theorem canonical42286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42286 raw42286Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw42286 raw42286Labels = mixedMoment B raw42286step0 raw42286step0Labels := by
      have ha : raw42286step0 = (fun i j => raw42286 (permutation355 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42286step0 raw42286; decide +kernel
      have hl : raw42286step0Labels = raw42286Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42286 raw42286Labels permutation355 permutation4
    mixedMoment B raw42286step0 raw42286step0Labels = mixedMoment B raw42286step1 raw42286step1Labels := by
      have ha : raw42286step1 = -raw42286step0 := by apply Matrix.ext; change ∀ i j, raw42286step1 i j = -(raw42286step0 i j); unfold raw42286step1 raw42286step0; decide +kernel
      have hl : raw42286step1Labels = raw42286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42286step1 raw42286step1Labels = mixedMoment B raw42286step2 raw42286step2Labels := by
      have ha : raw42286step2 = raw42286step1 := by apply Matrix.ext; unfold raw42286step2 raw42286step1; decide +kernel
      have hl : raw42286step1Labels = labelEmbedding1 ∘ raw42286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42286step1 raw42286step1Labels raw42286step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

theorem canonical42287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42287 raw42287Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42287 raw42287Labels = mixedMoment B raw42287step0 raw42287step0Labels := by
      have ha : raw42287step0 = (fun i j => raw42287 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42287step0 raw42287; decide +kernel
      have hl : raw42287step0Labels = raw42287Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42287 raw42287Labels permutation393 permutation6
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical42288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42288 raw42288Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw42288 raw42288Labels = mixedMoment B raw42288step0 raw42288step0Labels := by
      have ha : raw42288step0 = raw42288 := by apply Matrix.ext; unfold raw42288step0 raw42288; decide +kernel
      have hl : raw42288Labels = labelEmbedding1 ∘ raw42288step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42288 raw42288Labels raw42288step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3954 node3954Labels := by rfl

theorem canonical42289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42289 raw42289Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42289 raw42289Labels = mixedMoment B raw42289step0 raw42289step0Labels := by
      have ha : raw42289step0 = (fun i j => raw42289 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42289step0 raw42289; decide +kernel
      have hl : raw42289step0Labels = raw42289Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42289 raw42289Labels permutation682 permutation3
    mixedMoment B raw42289step0 raw42289step0Labels = mixedMoment B raw42289step1 raw42289step1Labels := by
      have ha : raw42289step1 = -raw42289step0 := by apply Matrix.ext; change ∀ i j, raw42289step1 i j = -(raw42289step0 i j); unfold raw42289step1 raw42289step0; decide +kernel
      have hl : raw42289step1Labels = raw42289step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42289step1 raw42289step1Labels = mixedMoment B raw42289step2 raw42289step2Labels := by
      have ha : raw42289step2 = raw42289step1 := by apply Matrix.ext; unfold raw42289step2 raw42289step1; decide +kernel
      have hl : raw42289step1Labels = labelEmbedding7 ∘ raw42289step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42289step1 raw42289step1Labels raw42289step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical42290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42290 raw42290Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw42290 raw42290Labels = mixedMoment B raw42290step0 raw42290step0Labels := by
      have ha : raw42290step0 = (fun i j => raw42290 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42290step0 raw42290; decide +kernel
      have hl : raw42290step0Labels = raw42290Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42290 raw42290Labels permutation682 permutation2
    mixedMoment B raw42290step0 raw42290step0Labels = mixedMoment B raw42290step1 raw42290step1Labels := by
      have ha : raw42290step1 = -raw42290step0 := by apply Matrix.ext; change ∀ i j, raw42290step1 i j = -(raw42290step0 i j); unfold raw42290step1 raw42290step0; decide +kernel
      have hl : raw42290step1Labels = raw42290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42290step1 raw42290step1Labels = mixedMoment B raw42290step2 raw42290step2Labels := by
      have ha : raw42290step2 = raw42290step1 := by apply Matrix.ext; unfold raw42290step2 raw42290step1; decide +kernel
      have hl : raw42290step1Labels = labelEmbedding1 ∘ raw42290step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42290step1 raw42290step1Labels raw42290step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3869 node3869Labels := by rfl

theorem canonical42291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42291 raw42291Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw42291 raw42291Labels = mixedMoment B raw42291step0 raw42291step0Labels := by
      have ha : raw42291step0 = (fun i j => raw42291 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42291step0 raw42291; decide +kernel
      have hl : raw42291step0Labels = raw42291Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42291 raw42291Labels permutation639 permutation7
    mixedMoment B raw42291step0 raw42291step0Labels = mixedMoment B raw42291step1 raw42291step1Labels := by
      have ha : raw42291step1 = raw42291step0 := by apply Matrix.ext; unfold raw42291step1 raw42291step0; decide +kernel
      have hl : raw42291step0Labels = labelEmbedding6 ∘ raw42291step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42291step0 raw42291step0Labels raw42291step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5414 node5414Labels := by rfl

theorem canonical42292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42292 raw42292Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw42292 raw42292Labels = mixedMoment B raw42292step0 raw42292step0Labels := by
      have hz : ∀ j, raw42292 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42292step0 = (fun i j => raw42292 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42292step0 raw42292; decide +kernel
      have hl : raw42292step0Labels = raw42292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42292 raw42292Labels permutation434 hz
    mixedMoment B raw42292step0 raw42292step0Labels = mixedMoment B raw42292step1 raw42292step1Labels := by
      have ha : raw42292step1 = raw42292step0 := by apply Matrix.ext; unfold raw42292step1 raw42292step0; decide +kernel
      have hl : raw42292step0Labels = labelEmbedding1 ∘ raw42292step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42292step0 raw42292step0Labels raw42292step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

theorem canonical42293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42293 raw42293Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw42293 raw42293Labels = mixedMoment B raw42293step0 raw42293step0Labels := by
      have hz : ∀ j, raw42293 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42293step0 = (fun i j => raw42293 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42293step0 raw42293; decide +kernel
      have hl : raw42293step0Labels = raw42293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42293 raw42293Labels permutation434 hz
    mixedMoment B raw42293step0 raw42293step0Labels = mixedMoment B raw42293step1 raw42293step1Labels := by
      have ha : raw42293step1 = (fun i j => raw42293step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42293step1 raw42293step0; decide +kernel
      have hl : raw42293step1Labels = raw42293step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42293step0 raw42293step0Labels permutation151 permutation3
    mixedMoment B raw42293step1 raw42293step1Labels = mixedMoment B raw42293step2 raw42293step2Labels := by
      have ha : raw42293step2 = -raw42293step1 := by apply Matrix.ext; change ∀ i j, raw42293step2 i j = -(raw42293step1 i j); unfold raw42293step2 raw42293step1; decide +kernel
      have hl : raw42293step2Labels = raw42293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42293step2 raw42293step2Labels = mixedMoment B raw42293step3 raw42293step3Labels := by
      have ha : raw42293step3 = raw42293step2 := by apply Matrix.ext; unfold raw42293step3 raw42293step2; decide +kernel
      have hl : raw42293step2Labels = labelEmbedding7 ∘ raw42293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42293step2 raw42293step2Labels raw42293step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

theorem canonical42294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42294 raw42294Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw42294 raw42294Labels = mixedMoment B raw42294step0 raw42294step0Labels := by
      have hz : ∀ j, raw42294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42294step0 = (fun i j => raw42294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42294step0 raw42294; decide +kernel
      have hl : raw42294step0Labels = raw42294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42294 raw42294Labels permutation434 hz
    mixedMoment B raw42294step0 raw42294step0Labels = mixedMoment B raw42294step1 raw42294step1Labels := by
      have ha : raw42294step1 = (fun i j => raw42294step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42294step1 raw42294step0; decide +kernel
      have hl : raw42294step1Labels = raw42294step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42294step0 raw42294step0Labels permutation151 permutation2
    mixedMoment B raw42294step1 raw42294step1Labels = mixedMoment B raw42294step2 raw42294step2Labels := by
      have ha : raw42294step2 = -raw42294step1 := by apply Matrix.ext; change ∀ i j, raw42294step2 i j = -(raw42294step1 i j); unfold raw42294step2 raw42294step1; decide +kernel
      have hl : raw42294step2Labels = raw42294step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42294step2 raw42294step2Labels = mixedMoment B raw42294step3 raw42294step3Labels := by
      have ha : raw42294step3 = raw42294step2 := by apply Matrix.ext; unfold raw42294step3 raw42294step2; decide +kernel
      have hl : raw42294step2Labels = labelEmbedding1 ∘ raw42294step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42294step2 raw42294step2Labels raw42294step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

theorem canonical42295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42295 raw42295Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw42295 raw42295Labels = mixedMoment B raw42295step0 raw42295step0Labels := by
      have hz : ∀ j, raw42295 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42295step0 = (fun i j => raw42295 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42295step0 raw42295; decide +kernel
      have hl : raw42295step0Labels = raw42295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42295 raw42295Labels permutation434 hz
    mixedMoment B raw42295step0 raw42295step0Labels = mixedMoment B raw42295step1 raw42295step1Labels := by
      have ha : raw42295step1 = (fun i j => raw42295step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42295step1 raw42295step0; decide +kernel
      have hl : raw42295step1Labels = raw42295step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42295step0 raw42295step0Labels permutation144 permutation7
    mixedMoment B raw42295step1 raw42295step1Labels = mixedMoment B raw42295step2 raw42295step2Labels := by
      have ha : raw42295step2 = raw42295step1 := by apply Matrix.ext; unfold raw42295step2 raw42295step1; decide +kernel
      have hl : raw42295step1Labels = labelEmbedding6 ∘ raw42295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42295step1 raw42295step1Labels raw42295step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

theorem canonical42296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42296 raw42296Labels = mixedMoment B node3955 node3955Labels := by
  calc
    mixedMoment B raw42296 raw42296Labels = mixedMoment B raw42296step0 raw42296step0Labels := by
      have ha : raw42296step0 = (fun i j => raw42296 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42296step0 raw42296; decide +kernel
      have hl : raw42296step0Labels = raw42296Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42296 raw42296Labels permutation157 permutation2
    mixedMoment B raw42296step0 raw42296step0Labels = mixedMoment B raw42296step1 raw42296step1Labels := by
      have ha : raw42296step1 = raw42296step0 := by apply Matrix.ext; unfold raw42296step1 raw42296step0; decide +kernel
      have hl : raw42296step0Labels = labelEmbedding1 ∘ raw42296step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42296step0 raw42296step0Labels raw42296step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3955 node3955Labels := by rfl

theorem canonical42297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42297 raw42297Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw42297 raw42297Labels = mixedMoment B raw42297step0 raw42297step0Labels := by
      have ha : raw42297step0 = (fun i j => raw42297 (permutation337 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42297step0 raw42297; decide +kernel
      have hl : raw42297step0Labels = raw42297Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42297 raw42297Labels permutation337 permutation6
    mixedMoment B raw42297step0 raw42297step0Labels = mixedMoment B raw42297step1 raw42297step1Labels := by
      have ha : raw42297step1 = -raw42297step0 := by apply Matrix.ext; change ∀ i j, raw42297step1 i j = -(raw42297step0 i j); unfold raw42297step1 raw42297step0; decide +kernel
      have hl : raw42297step1Labels = raw42297step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5470 node5470Labels := by rfl

theorem canonical42298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42298 raw42298Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw42298 raw42298Labels = mixedMoment B raw42298step0 raw42298step0Labels := by
      have hz : ∀ j, raw42298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42298step0 = (fun i j => raw42298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42298step0 raw42298; decide +kernel
      have hl : raw42298step0Labels = raw42298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42298 raw42298Labels permutation434 hz
    mixedMoment B raw42298step0 raw42298step0Labels = mixedMoment B raw42298step1 raw42298step1Labels := by
      have hz : ∀ j, raw42298step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42298step1 = (fun i j => raw42298step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42298step1 raw42298step0; decide +kernel
      have hl : raw42298step1Labels = raw42298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42298step0 raw42298step0Labels permutation80 hz
    mixedMoment B raw42298step1 raw42298step1Labels = mixedMoment B raw42298step2 raw42298step2Labels := by
      have ha : raw42298step2 = (fun i j => raw42298step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42298step2 raw42298step1; decide +kernel
      have hl : raw42298step2Labels = raw42298step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42298step1 raw42298step1Labels permutation20 permutation4
    mixedMoment B raw42298step2 raw42298step2Labels = mixedMoment B raw42298step3 raw42298step3Labels := by
      have ha : raw42298step3 = -raw42298step2 := by apply Matrix.ext; change ∀ i j, raw42298step3 i j = -(raw42298step2 i j); unfold raw42298step3 raw42298step2; decide +kernel
      have hl : raw42298step3Labels = raw42298step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42298step3 raw42298step3Labels = mixedMoment B raw42298step4 raw42298step4Labels := by
      have ha : raw42298step4 = raw42298step3 := by apply Matrix.ext; unfold raw42298step4 raw42298step3; decide +kernel
      have hl : raw42298step3Labels = labelEmbedding1 ∘ raw42298step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42298step3 raw42298step3Labels raw42298step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

theorem canonical42299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42299 raw42299Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw42299 raw42299Labels = mixedMoment B raw42299step0 raw42299step0Labels := by
      have hz : ∀ j, raw42299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42299step0 = (fun i j => raw42299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42299step0 raw42299; decide +kernel
      have hl : raw42299step0Labels = raw42299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42299 raw42299Labels permutation434 hz
    mixedMoment B raw42299step0 raw42299step0Labels = mixedMoment B raw42299step1 raw42299step1Labels := by
      have hz : ∀ j, raw42299step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42299step1 = (fun i j => raw42299step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42299step1 raw42299step0; decide +kernel
      have hl : raw42299step1Labels = raw42299step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42299step0 raw42299step0Labels permutation80 hz
    mixedMoment B raw42299step1 raw42299step1Labels = mixedMoment B raw42299step2 raw42299step2Labels := by
      have ha : raw42299step2 = (fun i j => raw42299step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42299step2 raw42299step1; decide +kernel
      have hl : raw42299step2Labels = raw42299step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42299step1 raw42299step1Labels permutation24 permutation6
    _ = mixedMoment B node5300 node5300Labels := by rfl

theorem canonical42300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42300 raw42300Labels = mixedMoment B node3306 node3306Labels := by
  calc
    mixedMoment B raw42300 raw42300Labels = mixedMoment B raw42300step0 raw42300step0Labels := by
      have hz : ∀ j, raw42300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42300step0 = (fun i j => raw42300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42300step0 raw42300; decide +kernel
      have hl : raw42300step0Labels = raw42300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42300 raw42300Labels permutation434 hz
    mixedMoment B raw42300step0 raw42300step0Labels = mixedMoment B raw42300step1 raw42300step1Labels := by
      have hz : ∀ j, raw42300step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42300step1 = (fun i j => raw42300step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42300step1 raw42300step0; decide +kernel
      have hl : raw42300step1Labels = raw42300step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42300step0 raw42300step0Labels permutation80 hz
    mixedMoment B raw42300step1 raw42300step1Labels = mixedMoment B raw42300step2 raw42300step2Labels := by
      have ha : raw42300step2 = (fun i j => raw42300step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42300step2 raw42300step1; decide +kernel
      have hl : raw42300step2Labels = raw42300step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42300step1 raw42300step1Labels permutation31 permutation2
    mixedMoment B raw42300step2 raw42300step2Labels = mixedMoment B raw42300step3 raw42300step3Labels := by
      have ha : raw42300step3 = -raw42300step2 := by apply Matrix.ext; change ∀ i j, raw42300step3 i j = -(raw42300step2 i j); unfold raw42300step3 raw42300step2; decide +kernel
      have hl : raw42300step3Labels = raw42300step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42300step3 raw42300step3Labels = mixedMoment B raw42300step4 raw42300step4Labels := by
      have ha : raw42300step4 = raw42300step3 := by apply Matrix.ext; unfold raw42300step4 raw42300step3; decide +kernel
      have hl : raw42300step3Labels = labelEmbedding1 ∘ raw42300step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42300step3 raw42300step3Labels raw42300step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3306 node3306Labels := by rfl

theorem canonical42301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42301 raw42301Labels = mixedMoment B node4620 node4620Labels := by
  calc
    mixedMoment B raw42301 raw42301Labels = mixedMoment B raw42301step0 raw42301step0Labels := by
      have hz : ∀ j, raw42301 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42301step0 = (fun i j => raw42301 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42301step0 raw42301; decide +kernel
      have hl : raw42301step0Labels = raw42301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42301 raw42301Labels permutation434 hz
    mixedMoment B raw42301step0 raw42301step0Labels = mixedMoment B raw42301step1 raw42301step1Labels := by
      have hz : ∀ j, raw42301step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42301step1 = (fun i j => raw42301step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42301step1 raw42301step0; decide +kernel
      have hl : raw42301step1Labels = raw42301step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42301step0 raw42301step0Labels permutation80 hz
    mixedMoment B raw42301step1 raw42301step1Labels = mixedMoment B raw42301step2 raw42301step2Labels := by
      have ha : raw42301step2 = (fun i j => raw42301step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42301step2 raw42301step1; decide +kernel
      have hl : raw42301step2Labels = raw42301step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42301step1 raw42301step1Labels permutation27 permutation6
    _ = mixedMoment B node4620 node4620Labels := by rfl

theorem canonical42302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42302 raw42302Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw42302 raw42302Labels = mixedMoment B raw42302step0 raw42302step0Labels := by
      have hz : ∀ j, raw42302 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42302step0 = (fun i j => raw42302 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42302step0 raw42302; decide +kernel
      have hl : raw42302step0Labels = raw42302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42302 raw42302Labels permutation346 hz
    mixedMoment B raw42302step0 raw42302step0Labels = mixedMoment B raw42302step1 raw42302step1Labels := by
      have ha : raw42302step1 = (fun i j => raw42302step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42302step1 raw42302step0; decide +kernel
      have hl : raw42302step1Labels = raw42302step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42302step0 raw42302step0Labels permutation151 permutation2
    mixedMoment B raw42302step1 raw42302step1Labels = mixedMoment B raw42302step2 raw42302step2Labels := by
      have ha : raw42302step2 = -raw42302step1 := by apply Matrix.ext; change ∀ i j, raw42302step2 i j = -(raw42302step1 i j); unfold raw42302step2 raw42302step1; decide +kernel
      have hl : raw42302step2Labels = raw42302step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42302step2 raw42302step2Labels = mixedMoment B raw42302step3 raw42302step3Labels := by
      have ha : raw42302step3 = raw42302step2 := by apply Matrix.ext; unfold raw42302step3 raw42302step2; decide +kernel
      have hl : raw42302step2Labels = labelEmbedding1 ∘ raw42302step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42302step2 raw42302step2Labels raw42302step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical42303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42303 raw42303Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw42303 raw42303Labels = mixedMoment B raw42303step0 raw42303step0Labels := by
      have hz : ∀ j, raw42303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42303step0 = (fun i j => raw42303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42303step0 raw42303; decide +kernel
      have hl : raw42303step0Labels = raw42303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42303 raw42303Labels permutation346 hz
    mixedMoment B raw42303step0 raw42303step0Labels = mixedMoment B raw42303step1 raw42303step1Labels := by
      have ha : raw42303step1 = (fun i j => raw42303step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42303step1 raw42303step0; decide +kernel
      have hl : raw42303step1Labels = raw42303step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42303step0 raw42303step0Labels permutation150 permutation7
    mixedMoment B raw42303step1 raw42303step1Labels = mixedMoment B raw42303step2 raw42303step2Labels := by
      have ha : raw42303step2 = raw42303step1 := by apply Matrix.ext; unfold raw42303step2 raw42303step1; decide +kernel
      have hl : raw42303step1Labels = labelEmbedding6 ∘ raw42303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42303step1 raw42303step1Labels raw42303step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2464 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2464) =
      Integer.Sparse.eval keyMomentRow2464 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2464).leftCharge (GramAssembly.key 2464).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3558) := by
    have ha : gramCharges (GramAssembly.key 2464).leftCharge (GramAssembly.key 2464).rightCharge = raw42240 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42240Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42240 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2464).leftCharge (GramAssembly.key 2464).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5160) := by
    have ha : gramCharges (GramAssembly.key 2464).leftCharge (GramAssembly.key 2464).rightCharge = raw42241 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42241Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42241 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2464).leftCharge (GramAssembly.key 2464).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2464).leftCharge (GramAssembly.key 2464).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2464, Integer.Sparse.eval] <;> ring

theorem keyMoment2465 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2465) =
      Integer.Sparse.eval keyMomentRow2465 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2465).leftCharge (GramAssembly.key 2465).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3517) := by
    have ha : gramCharges (GramAssembly.key 2465).leftCharge (GramAssembly.key 2465).rightCharge = raw42242 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42242Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42242 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2465).leftCharge (GramAssembly.key 2465).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5138) := by
    have ha : gramCharges (GramAssembly.key 2465).leftCharge (GramAssembly.key 2465).rightCharge = raw42243 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42243Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42243 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2465).leftCharge (GramAssembly.key 2465).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2465).leftCharge (GramAssembly.key 2465).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2465, Integer.Sparse.eval] <;> ring

theorem keyMoment2466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2466) =
      Integer.Sparse.eval keyMomentRow2466 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2466).leftCharge (GramAssembly.key 2466).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2718) := by
    have ha : gramCharges (GramAssembly.key 2466).leftCharge (GramAssembly.key 2466).rightCharge = raw42244 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42244Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42244 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2466).leftCharge (GramAssembly.key 2466).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5255) := by
    have ha : gramCharges (GramAssembly.key 2466).leftCharge (GramAssembly.key 2466).rightCharge = raw42245 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42245Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42245 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2466).leftCharge (GramAssembly.key 2466).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2466).leftCharge (GramAssembly.key 2466).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2466, Integer.Sparse.eval] <;> ring

theorem keyMoment2467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2467) =
      Integer.Sparse.eval keyMomentRow2467 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2467).leftCharge (GramAssembly.key 2467).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3978) := by
    have ha : gramCharges (GramAssembly.key 2467).leftCharge (GramAssembly.key 2467).rightCharge = raw42246 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42246Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42246 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2467).leftCharge (GramAssembly.key 2467).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5480) := by
    have ha : gramCharges (GramAssembly.key 2467).leftCharge (GramAssembly.key 2467).rightCharge = raw42247 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42247Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42247 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2467).leftCharge (GramAssembly.key 2467).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2467).leftCharge (GramAssembly.key 2467).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2467, Integer.Sparse.eval] <;> ring

theorem keyMoment2468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2468) =
      Integer.Sparse.eval keyMomentRow2468 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2468).leftCharge (GramAssembly.key 2468).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3098) := by
    have ha : gramCharges (GramAssembly.key 2468).leftCharge (GramAssembly.key 2468).rightCharge = raw42248 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42248Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42248 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2468).leftCharge (GramAssembly.key 2468).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5295) := by
    have ha : gramCharges (GramAssembly.key 2468).leftCharge (GramAssembly.key 2468).rightCharge = raw42249 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42249Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42249 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2468).leftCharge (GramAssembly.key 2468).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2468).leftCharge (GramAssembly.key 2468).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2468, Integer.Sparse.eval] <;> ring

theorem keyMoment2469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2469) =
      Integer.Sparse.eval keyMomentRow2469 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2469).leftCharge (GramAssembly.key 2469).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2737) := by
    have ha : gramCharges (GramAssembly.key 2469).leftCharge (GramAssembly.key 2469).rightCharge = raw42250 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42250Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42250 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2469).leftCharge (GramAssembly.key 2469).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4617) := by
    have ha : gramCharges (GramAssembly.key 2469).leftCharge (GramAssembly.key 2469).rightCharge = raw42251 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42251Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42251 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2469).leftCharge (GramAssembly.key 2469).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2469).leftCharge (GramAssembly.key 2469).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2469, Integer.Sparse.eval] <;> ring

theorem keyMoment2470 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2470) =
      Integer.Sparse.eval keyMomentRow2470 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2470).leftCharge (GramAssembly.key 2470).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3573) := by
    have ha : gramCharges (GramAssembly.key 2470).leftCharge (GramAssembly.key 2470).rightCharge = raw42252 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42252Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42252 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2470).leftCharge (GramAssembly.key 2470).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2470).leftCharge (GramAssembly.key 2470).rightCharge = raw42253 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42253Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42253 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2470).leftCharge (GramAssembly.key 2470).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2470).leftCharge (GramAssembly.key 2470).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2470, Integer.Sparse.eval] <;> ring

theorem keyMoment2471 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2471) =
      Integer.Sparse.eval keyMomentRow2471 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2471).leftCharge (GramAssembly.key 2471).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3303) := by
    have ha : gramCharges (GramAssembly.key 2471).leftCharge (GramAssembly.key 2471).rightCharge = raw42254 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42254Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42254 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2471).leftCharge (GramAssembly.key 2471).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4616) := by
    have ha : gramCharges (GramAssembly.key 2471).leftCharge (GramAssembly.key 2471).rightCharge = raw42255 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42255Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42255 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2471).leftCharge (GramAssembly.key 2471).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2471).leftCharge (GramAssembly.key 2471).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2471, Integer.Sparse.eval] <;> ring

theorem keyMoment2472 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2472) =
      Integer.Sparse.eval keyMomentRow2472 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2472).leftCharge (GramAssembly.key 2472).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3296) := by
    have ha : gramCharges (GramAssembly.key 2472).leftCharge (GramAssembly.key 2472).rightCharge = raw42256 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42256Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42256 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2472).leftCharge (GramAssembly.key 2472).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4607) := by
    have ha : gramCharges (GramAssembly.key 2472).leftCharge (GramAssembly.key 2472).rightCharge = raw42257 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42257Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42257 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2472).leftCharge (GramAssembly.key 2472).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2472).leftCharge (GramAssembly.key 2472).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2472, Integer.Sparse.eval] <;> ring

theorem keyMoment2473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2473) =
      Integer.Sparse.eval keyMomentRow2473 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2473).leftCharge (GramAssembly.key 2473).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2719) := by
    have ha : gramCharges (GramAssembly.key 2473).leftCharge (GramAssembly.key 2473).rightCharge = raw42258 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42258Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42258 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2473).leftCharge (GramAssembly.key 2473).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5161) := by
    have ha : gramCharges (GramAssembly.key 2473).leftCharge (GramAssembly.key 2473).rightCharge = raw42259 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42259Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42259 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2473).leftCharge (GramAssembly.key 2473).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2473).leftCharge (GramAssembly.key 2473).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2473, Integer.Sparse.eval] <;> ring

theorem keyMoment2474 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2474) =
      Integer.Sparse.eval keyMomentRow2474 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2474).leftCharge (GramAssembly.key 2474).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3572) := by
    have ha : gramCharges (GramAssembly.key 2474).leftCharge (GramAssembly.key 2474).rightCharge = raw42260 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42260Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42260 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2474).leftCharge (GramAssembly.key 2474).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5289) := by
    have ha : gramCharges (GramAssembly.key 2474).leftCharge (GramAssembly.key 2474).rightCharge = raw42261 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42261Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42261 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2474).leftCharge (GramAssembly.key 2474).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2474).leftCharge (GramAssembly.key 2474).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2474, Integer.Sparse.eval] <;> ring

theorem keyMoment2475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2475) =
      Integer.Sparse.eval keyMomentRow2475 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2475).leftCharge (GramAssembly.key 2475).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2736) := by
    have ha : gramCharges (GramAssembly.key 2475).leftCharge (GramAssembly.key 2475).rightCharge = raw42262 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42262Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42262 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2475).leftCharge (GramAssembly.key 2475).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5269) := by
    have ha : gramCharges (GramAssembly.key 2475).leftCharge (GramAssembly.key 2475).rightCharge = raw42263 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42263Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42263 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2475).leftCharge (GramAssembly.key 2475).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2475).leftCharge (GramAssembly.key 2475).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2475, Integer.Sparse.eval] <;> ring

theorem keyMoment2476 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2476) =
      Integer.Sparse.eval keyMomentRow2476 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2476).leftCharge (GramAssembly.key 2476).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3289) := by
    have ha : gramCharges (GramAssembly.key 2476).leftCharge (GramAssembly.key 2476).rightCharge = raw42264 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42264Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42264 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2476).leftCharge (GramAssembly.key 2476).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4599) := by
    have ha : gramCharges (GramAssembly.key 2476).leftCharge (GramAssembly.key 2476).rightCharge = raw42265 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42265Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42265 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2476).leftCharge (GramAssembly.key 2476).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2476).leftCharge (GramAssembly.key 2476).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2476, Integer.Sparse.eval] <;> ring

theorem keyMoment2477 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2477) =
      Integer.Sparse.eval keyMomentRow2477 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2477).leftCharge (GramAssembly.key 2477).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3558) := by
    have ha : gramCharges (GramAssembly.key 2477).leftCharge (GramAssembly.key 2477).rightCharge = raw42266 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42266Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42266 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2477).leftCharge (GramAssembly.key 2477).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5160) := by
    have ha : gramCharges (GramAssembly.key 2477).leftCharge (GramAssembly.key 2477).rightCharge = raw42267 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42267Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42267 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2477).leftCharge (GramAssembly.key 2477).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2477).leftCharge (GramAssembly.key 2477).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2477, Integer.Sparse.eval] <;> ring

theorem keyMoment2478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2478) =
      Integer.Sparse.eval keyMomentRow2478 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2478).leftCharge (GramAssembly.key 2478).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3571) := by
    have ha : gramCharges (GramAssembly.key 2478).leftCharge (GramAssembly.key 2478).rightCharge = raw42268 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42268Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42268 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2478).leftCharge (GramAssembly.key 2478).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5281) := by
    have ha : gramCharges (GramAssembly.key 2478).leftCharge (GramAssembly.key 2478).rightCharge = raw42269 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42269Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42269 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2478).leftCharge (GramAssembly.key 2478).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2478).leftCharge (GramAssembly.key 2478).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2478, Integer.Sparse.eval] <;> ring

theorem keyMoment2479 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2479) =
      Integer.Sparse.eval keyMomentRow2479 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2479).leftCharge (GramAssembly.key 2479).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3973) := by
    have ha : gramCharges (GramAssembly.key 2479).leftCharge (GramAssembly.key 2479).rightCharge = raw42270 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42270Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42270 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2479).leftCharge (GramAssembly.key 2479).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5461) := by
    have ha : gramCharges (GramAssembly.key 2479).leftCharge (GramAssembly.key 2479).rightCharge = raw42271 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42271Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42271 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2479).leftCharge (GramAssembly.key 2479).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2479).leftCharge (GramAssembly.key 2479).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2479, Integer.Sparse.eval] <;> ring

theorem keyMoment2480 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2480) =
      Integer.Sparse.eval keyMomentRow2480 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2480).leftCharge (GramAssembly.key 2480).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3557) := by
    have ha : gramCharges (GramAssembly.key 2480).leftCharge (GramAssembly.key 2480).rightCharge = raw42272 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42272Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42272 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2480).leftCharge (GramAssembly.key 2480).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5144) := by
    have ha : gramCharges (GramAssembly.key 2480).leftCharge (GramAssembly.key 2480).rightCharge = raw42273 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42273Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42273 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2480).leftCharge (GramAssembly.key 2480).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2480).leftCharge (GramAssembly.key 2480).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2480, Integer.Sparse.eval] <;> ring

theorem keyMoment2481 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2481) =
      Integer.Sparse.eval keyMomentRow2481 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2481).leftCharge (GramAssembly.key 2481).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3842) := by
    have ha : gramCharges (GramAssembly.key 2481).leftCharge (GramAssembly.key 2481).rightCharge = raw42274 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42274Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42274 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2481).leftCharge (GramAssembly.key 2481).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5419) := by
    have ha : gramCharges (GramAssembly.key 2481).leftCharge (GramAssembly.key 2481).rightCharge = raw42275 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42275Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42275 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2481).leftCharge (GramAssembly.key 2481).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2481).leftCharge (GramAssembly.key 2481).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2481, Integer.Sparse.eval] <;> ring

theorem keyMoment2482 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2482) =
      Integer.Sparse.eval keyMomentRow2482 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2482).leftCharge (GramAssembly.key 2482).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3877) := by
    have ha : gramCharges (GramAssembly.key 2482).leftCharge (GramAssembly.key 2482).rightCharge = raw42276 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42276Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42276 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2482).leftCharge (GramAssembly.key 2482).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5436) := by
    have ha : gramCharges (GramAssembly.key 2482).leftCharge (GramAssembly.key 2482).rightCharge = raw42277 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42277Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42277 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2482).leftCharge (GramAssembly.key 2482).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2482).leftCharge (GramAssembly.key 2482).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2482, Integer.Sparse.eval] <;> ring

theorem keyMoment2483 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2483) =
      Integer.Sparse.eval keyMomentRow2483 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2483).leftCharge (GramAssembly.key 2483).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3884) := by
    have ha : gramCharges (GramAssembly.key 2483).leftCharge (GramAssembly.key 2483).rightCharge = raw42278 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42278Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42278 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2483).leftCharge (GramAssembly.key 2483).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5446) := by
    have ha : gramCharges (GramAssembly.key 2483).leftCharge (GramAssembly.key 2483).rightCharge = raw42279 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42279Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42279 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2483).leftCharge (GramAssembly.key 2483).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2483).leftCharge (GramAssembly.key 2483).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2483, Integer.Sparse.eval] <;> ring

theorem keyMoment2484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2484) =
      Integer.Sparse.eval keyMomentRow2484 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2484).leftCharge (GramAssembly.key 2484).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3868) := by
    have ha : gramCharges (GramAssembly.key 2484).leftCharge (GramAssembly.key 2484).rightCharge = raw42280 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42280Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42280 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2484).leftCharge (GramAssembly.key 2484).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5385) := by
    have ha : gramCharges (GramAssembly.key 2484).leftCharge (GramAssembly.key 2484).rightCharge = raw42281 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42281Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42281 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2484).leftCharge (GramAssembly.key 2484).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2484).leftCharge (GramAssembly.key 2484).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2484, Integer.Sparse.eval] <;> ring

theorem keyMoment2485 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2485) =
      Integer.Sparse.eval keyMomentRow2485 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2485).leftCharge (GramAssembly.key 2485).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3832) := by
    have ha : gramCharges (GramAssembly.key 2485).leftCharge (GramAssembly.key 2485).rightCharge = raw42282 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42282Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42282 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2485).leftCharge (GramAssembly.key 2485).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5379) := by
    have ha : gramCharges (GramAssembly.key 2485).leftCharge (GramAssembly.key 2485).rightCharge = raw42283 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42283Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42283 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2485).leftCharge (GramAssembly.key 2485).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2485).leftCharge (GramAssembly.key 2485).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2485, Integer.Sparse.eval] <;> ring

theorem keyMoment2486 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2486) =
      Integer.Sparse.eval keyMomentRow2486 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2486).leftCharge (GramAssembly.key 2486).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3869) := by
    have ha : gramCharges (GramAssembly.key 2486).leftCharge (GramAssembly.key 2486).rightCharge = raw42284 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42284Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42284 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2486).leftCharge (GramAssembly.key 2486).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5414) := by
    have ha : gramCharges (GramAssembly.key 2486).leftCharge (GramAssembly.key 2486).rightCharge = raw42285 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42285Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42285 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2486).leftCharge (GramAssembly.key 2486).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2486).leftCharge (GramAssembly.key 2486).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2486, Integer.Sparse.eval] <;> ring

theorem keyMoment2487 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2487) =
      Integer.Sparse.eval keyMomentRow2487 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2487).leftCharge (GramAssembly.key 2487).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3874) := by
    have ha : gramCharges (GramAssembly.key 2487).leftCharge (GramAssembly.key 2487).rightCharge = raw42286 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42286Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42286 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2487).leftCharge (GramAssembly.key 2487).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2487).leftCharge (GramAssembly.key 2487).rightCharge = raw42287 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42287Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42287 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2487).leftCharge (GramAssembly.key 2487).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2487).leftCharge (GramAssembly.key 2487).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2487, Integer.Sparse.eval] <;> ring

theorem keyMoment2488 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2488) =
      Integer.Sparse.eval keyMomentRow2488 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2488).leftCharge (GramAssembly.key 2488).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3954) := by
    have ha : gramCharges (GramAssembly.key 2488).leftCharge (GramAssembly.key 2488).rightCharge = raw42288 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42288Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42288 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2488).leftCharge (GramAssembly.key 2488).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2488).leftCharge (GramAssembly.key 2488).rightCharge = raw42289 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42289Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42289 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2488).leftCharge (GramAssembly.key 2488).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2488).leftCharge (GramAssembly.key 2488).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2488, Integer.Sparse.eval] <;> ring

theorem keyMoment2489 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2489) =
      Integer.Sparse.eval keyMomentRow2489 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2489).leftCharge (GramAssembly.key 2489).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3869) := by
    have ha : gramCharges (GramAssembly.key 2489).leftCharge (GramAssembly.key 2489).rightCharge = raw42290 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42290Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42290 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2489).leftCharge (GramAssembly.key 2489).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5414) := by
    have ha : gramCharges (GramAssembly.key 2489).leftCharge (GramAssembly.key 2489).rightCharge = raw42291 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42291Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42291 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2489).leftCharge (GramAssembly.key 2489).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2489).leftCharge (GramAssembly.key 2489).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2489, Integer.Sparse.eval] <;> ring

theorem keyMoment2490 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2490) =
      Integer.Sparse.eval keyMomentRow2490 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2490).leftCharge (GramAssembly.key 2490).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3959) := by
    have ha : gramCharges (GramAssembly.key 2490).leftCharge (GramAssembly.key 2490).rightCharge = raw42292 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42292Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42292 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2490).leftCharge (GramAssembly.key 2490).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5446) := by
    have ha : gramCharges (GramAssembly.key 2490).leftCharge (GramAssembly.key 2490).rightCharge = raw42293 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42293Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42293 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2490).leftCharge (GramAssembly.key 2490).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2490).leftCharge (GramAssembly.key 2490).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2490, Integer.Sparse.eval] <;> ring

theorem keyMoment2491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2491) =
      Integer.Sparse.eval keyMomentRow2491 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2491).leftCharge (GramAssembly.key 2491).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3565) := by
    have ha : gramCharges (GramAssembly.key 2491).leftCharge (GramAssembly.key 2491).rightCharge = raw42294 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42294Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42294 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2491).leftCharge (GramAssembly.key 2491).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5164) := by
    have ha : gramCharges (GramAssembly.key 2491).leftCharge (GramAssembly.key 2491).rightCharge = raw42295 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42295Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42295 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2491).leftCharge (GramAssembly.key 2491).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2491).leftCharge (GramAssembly.key 2491).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2491, Integer.Sparse.eval] <;> ring

theorem keyMoment2492 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2492) =
      Integer.Sparse.eval keyMomentRow2492 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2492).leftCharge (GramAssembly.key 2492).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3955) := by
    have ha : gramCharges (GramAssembly.key 2492).leftCharge (GramAssembly.key 2492).rightCharge = raw42296 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42296Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42296 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2492).leftCharge (GramAssembly.key 2492).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5470) := by
    have ha : gramCharges (GramAssembly.key 2492).leftCharge (GramAssembly.key 2492).rightCharge = raw42297 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42297Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42297 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2492).leftCharge (GramAssembly.key 2492).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2492).leftCharge (GramAssembly.key 2492).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2492, Integer.Sparse.eval] <;> ring

theorem keyMoment2493 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2493) =
      Integer.Sparse.eval keyMomentRow2493 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2493).leftCharge (GramAssembly.key 2493).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3584) := by
    have ha : gramCharges (GramAssembly.key 2493).leftCharge (GramAssembly.key 2493).rightCharge = raw42298 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42298Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42298 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2493).leftCharge (GramAssembly.key 2493).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5300) := by
    have ha : gramCharges (GramAssembly.key 2493).leftCharge (GramAssembly.key 2493).rightCharge = raw42299 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42299Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42299 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2493).leftCharge (GramAssembly.key 2493).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2493).leftCharge (GramAssembly.key 2493).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2493, Integer.Sparse.eval] <;> ring

theorem keyMoment2494 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2494) =
      Integer.Sparse.eval keyMomentRow2494 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2494).leftCharge (GramAssembly.key 2494).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3306) := by
    have ha : gramCharges (GramAssembly.key 2494).leftCharge (GramAssembly.key 2494).rightCharge = raw42300 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42300Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42300 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2494).leftCharge (GramAssembly.key 2494).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4620) := by
    have ha : gramCharges (GramAssembly.key 2494).leftCharge (GramAssembly.key 2494).rightCharge = raw42301 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42301Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42301 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2494).leftCharge (GramAssembly.key 2494).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2494).leftCharge (GramAssembly.key 2494).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2494, Integer.Sparse.eval] <;> ring

theorem keyMoment2495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2495) =
      Integer.Sparse.eval keyMomentRow2495 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2495).leftCharge (GramAssembly.key 2495).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3294) := by
    have ha : gramCharges (GramAssembly.key 2495).leftCharge (GramAssembly.key 2495).rightCharge = raw42302 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42302Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42302 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2495).leftCharge (GramAssembly.key 2495).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4603) := by
    have ha : gramCharges (GramAssembly.key 2495).leftCharge (GramAssembly.key 2495).rightCharge = raw42303 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42303Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42303 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2495).leftCharge (GramAssembly.key 2495).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2495).leftCharge (GramAssembly.key 2495).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2495, Integer.Sparse.eval] <;> ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2464 : keyMomentRows (2464 : Fin 2886) =
    keyMomentRow2464 := by decide +kernel

theorem keyMomentRowsAt2465 : keyMomentRows (2465 : Fin 2886) =
    keyMomentRow2465 := by decide +kernel

theorem keyMomentRowsAt2466 : keyMomentRows (2466 : Fin 2886) =
    keyMomentRow2466 := by decide +kernel

theorem keyMomentRowsAt2467 : keyMomentRows (2467 : Fin 2886) =
    keyMomentRow2467 := by decide +kernel

theorem keyMomentRowsAt2468 : keyMomentRows (2468 : Fin 2886) =
    keyMomentRow2468 := by decide +kernel

theorem keyMomentRowsAt2469 : keyMomentRows (2469 : Fin 2886) =
    keyMomentRow2469 := by decide +kernel

theorem keyMomentRowsAt2470 : keyMomentRows (2470 : Fin 2886) =
    keyMomentRow2470 := by decide +kernel

theorem keyMomentRowsAt2471 : keyMomentRows (2471 : Fin 2886) =
    keyMomentRow2471 := by decide +kernel

theorem keyMomentRowsAt2472 : keyMomentRows (2472 : Fin 2886) =
    keyMomentRow2472 := by decide +kernel

theorem keyMomentRowsAt2473 : keyMomentRows (2473 : Fin 2886) =
    keyMomentRow2473 := by decide +kernel

theorem keyMomentRowsAt2474 : keyMomentRows (2474 : Fin 2886) =
    keyMomentRow2474 := by decide +kernel

theorem keyMomentRowsAt2475 : keyMomentRows (2475 : Fin 2886) =
    keyMomentRow2475 := by decide +kernel

theorem keyMomentRowsAt2476 : keyMomentRows (2476 : Fin 2886) =
    keyMomentRow2476 := by decide +kernel

theorem keyMomentRowsAt2477 : keyMomentRows (2477 : Fin 2886) =
    keyMomentRow2477 := by decide +kernel

theorem keyMomentRowsAt2478 : keyMomentRows (2478 : Fin 2886) =
    keyMomentRow2478 := by decide +kernel

theorem keyMomentRowsAt2479 : keyMomentRows (2479 : Fin 2886) =
    keyMomentRow2479 := by decide +kernel

theorem keyMomentRowsAt2480 : keyMomentRows (2480 : Fin 2886) =
    keyMomentRow2480 := by decide +kernel

theorem keyMomentRowsAt2481 : keyMomentRows (2481 : Fin 2886) =
    keyMomentRow2481 := by decide +kernel

theorem keyMomentRowsAt2482 : keyMomentRows (2482 : Fin 2886) =
    keyMomentRow2482 := by decide +kernel

theorem keyMomentRowsAt2483 : keyMomentRows (2483 : Fin 2886) =
    keyMomentRow2483 := by decide +kernel

theorem keyMomentRowsAt2484 : keyMomentRows (2484 : Fin 2886) =
    keyMomentRow2484 := by decide +kernel

theorem keyMomentRowsAt2485 : keyMomentRows (2485 : Fin 2886) =
    keyMomentRow2485 := by decide +kernel

theorem keyMomentRowsAt2486 : keyMomentRows (2486 : Fin 2886) =
    keyMomentRow2486 := by decide +kernel

theorem keyMomentRowsAt2487 : keyMomentRows (2487 : Fin 2886) =
    keyMomentRow2487 := by decide +kernel

theorem keyMomentRowsAt2488 : keyMomentRows (2488 : Fin 2886) =
    keyMomentRow2488 := by decide +kernel

theorem keyMomentRowsAt2489 : keyMomentRows (2489 : Fin 2886) =
    keyMomentRow2489 := by decide +kernel

theorem keyMomentRowsAt2490 : keyMomentRows (2490 : Fin 2886) =
    keyMomentRow2490 := by decide +kernel

theorem keyMomentRowsAt2491 : keyMomentRows (2491 : Fin 2886) =
    keyMomentRow2491 := by decide +kernel

theorem keyMomentRowsAt2492 : keyMomentRows (2492 : Fin 2886) =
    keyMomentRow2492 := by decide +kernel

theorem keyMomentRowsAt2493 : keyMomentRows (2493 : Fin 2886) =
    keyMomentRow2493 := by decide +kernel

theorem keyMomentRowsAt2494 : keyMomentRows (2494 : Fin 2886) =
    keyMomentRow2494 := by decide +kernel

theorem keyMomentRowsAt2495 : keyMomentRows (2495 : Fin 2886) =
    keyMomentRow2495 := by decide +kernel

theorem keyMomentChunkSound77_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 77) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2464 ∨ k.val = 2465 ∨ k.val = 2466 ∨ k.val = 2467 ∨ k.val = 2468 ∨ k.val = 2469 ∨ k.val = 2470 ∨ k.val = 2471 ∨ k.val = 2472 ∨ k.val = 2473 ∨ k.val = 2474 ∨ k.val = 2475 ∨ k.val = 2476 ∨ k.val = 2477 ∨ k.val = 2478 ∨ k.val = 2479 ∨ k.val = 2480 ∨ k.val = 2481 ∨ k.val = 2482 ∨ k.val = 2483 ∨ k.val = 2484 ∨ k.val = 2485 ∨ k.val = 2486 ∨ k.val = 2487 ∨ k.val = 2488 ∨ k.val = 2489 ∨ k.val = 2490 ∨ k.val = 2491 ∨ k.val = 2492 ∨ k.val = 2493 ∨ k.val = 2494 ∨ k.val = 2495 := by omega
  rcases heq with h2464 | h2465 | h2466 | h2467 | h2468 | h2469 | h2470 | h2471 | h2472 | h2473 | h2474 | h2475 | h2476 | h2477 | h2478 | h2479 | h2480 | h2481 | h2482 | h2483 | h2484 | h2485 | h2486 | h2487 | h2488 | h2489 | h2490 | h2491 | h2492 | h2493 | h2494 | h2495
  · have he : k = (2464 : Fin 2886) := Fin.ext h2464
    subst k
    rw [keyMomentRowsAt2464]
    exact keyMoment2464 B hB
  · have he : k = (2465 : Fin 2886) := Fin.ext h2465
    subst k
    rw [keyMomentRowsAt2465]
    exact keyMoment2465 B hB
  · have he : k = (2466 : Fin 2886) := Fin.ext h2466
    subst k
    rw [keyMomentRowsAt2466]
    exact keyMoment2466 B hB
  · have he : k = (2467 : Fin 2886) := Fin.ext h2467
    subst k
    rw [keyMomentRowsAt2467]
    exact keyMoment2467 B hB
  · have he : k = (2468 : Fin 2886) := Fin.ext h2468
    subst k
    rw [keyMomentRowsAt2468]
    exact keyMoment2468 B hB
  · have he : k = (2469 : Fin 2886) := Fin.ext h2469
    subst k
    rw [keyMomentRowsAt2469]
    exact keyMoment2469 B hB
  · have he : k = (2470 : Fin 2886) := Fin.ext h2470
    subst k
    rw [keyMomentRowsAt2470]
    exact keyMoment2470 B hB
  · have he : k = (2471 : Fin 2886) := Fin.ext h2471
    subst k
    rw [keyMomentRowsAt2471]
    exact keyMoment2471 B hB
  · have he : k = (2472 : Fin 2886) := Fin.ext h2472
    subst k
    rw [keyMomentRowsAt2472]
    exact keyMoment2472 B hB
  · have he : k = (2473 : Fin 2886) := Fin.ext h2473
    subst k
    rw [keyMomentRowsAt2473]
    exact keyMoment2473 B hB
  · have he : k = (2474 : Fin 2886) := Fin.ext h2474
    subst k
    rw [keyMomentRowsAt2474]
    exact keyMoment2474 B hB
  · have he : k = (2475 : Fin 2886) := Fin.ext h2475
    subst k
    rw [keyMomentRowsAt2475]
    exact keyMoment2475 B hB
  · have he : k = (2476 : Fin 2886) := Fin.ext h2476
    subst k
    rw [keyMomentRowsAt2476]
    exact keyMoment2476 B hB
  · have he : k = (2477 : Fin 2886) := Fin.ext h2477
    subst k
    rw [keyMomentRowsAt2477]
    exact keyMoment2477 B hB
  · have he : k = (2478 : Fin 2886) := Fin.ext h2478
    subst k
    rw [keyMomentRowsAt2478]
    exact keyMoment2478 B hB
  · have he : k = (2479 : Fin 2886) := Fin.ext h2479
    subst k
    rw [keyMomentRowsAt2479]
    exact keyMoment2479 B hB
  · have he : k = (2480 : Fin 2886) := Fin.ext h2480
    subst k
    rw [keyMomentRowsAt2480]
    exact keyMoment2480 B hB
  · have he : k = (2481 : Fin 2886) := Fin.ext h2481
    subst k
    rw [keyMomentRowsAt2481]
    exact keyMoment2481 B hB
  · have he : k = (2482 : Fin 2886) := Fin.ext h2482
    subst k
    rw [keyMomentRowsAt2482]
    exact keyMoment2482 B hB
  · have he : k = (2483 : Fin 2886) := Fin.ext h2483
    subst k
    rw [keyMomentRowsAt2483]
    exact keyMoment2483 B hB
  · have he : k = (2484 : Fin 2886) := Fin.ext h2484
    subst k
    rw [keyMomentRowsAt2484]
    exact keyMoment2484 B hB
  · have he : k = (2485 : Fin 2886) := Fin.ext h2485
    subst k
    rw [keyMomentRowsAt2485]
    exact keyMoment2485 B hB
  · have he : k = (2486 : Fin 2886) := Fin.ext h2486
    subst k
    rw [keyMomentRowsAt2486]
    exact keyMoment2486 B hB
  · have he : k = (2487 : Fin 2886) := Fin.ext h2487
    subst k
    rw [keyMomentRowsAt2487]
    exact keyMoment2487 B hB
  · have he : k = (2488 : Fin 2886) := Fin.ext h2488
    subst k
    rw [keyMomentRowsAt2488]
    exact keyMoment2488 B hB
  · have he : k = (2489 : Fin 2886) := Fin.ext h2489
    subst k
    rw [keyMomentRowsAt2489]
    exact keyMoment2489 B hB
  · have he : k = (2490 : Fin 2886) := Fin.ext h2490
    subst k
    rw [keyMomentRowsAt2490]
    exact keyMoment2490 B hB
  · have he : k = (2491 : Fin 2886) := Fin.ext h2491
    subst k
    rw [keyMomentRowsAt2491]
    exact keyMoment2491 B hB
  · have he : k = (2492 : Fin 2886) := Fin.ext h2492
    subst k
    rw [keyMomentRowsAt2492]
    exact keyMoment2492 B hB
  · have he : k = (2493 : Fin 2886) := Fin.ext h2493
    subst k
    rw [keyMomentRowsAt2493]
    exact keyMoment2493 B hB
  · have he : k = (2494 : Fin 2886) := Fin.ext h2494
    subst k
    rw [keyMomentRowsAt2494]
    exact keyMoment2494 B hB
  · have he : k = (2495 : Fin 2886) := Fin.ext h2495
    subst k
    rw [keyMomentRowsAt2495]
    exact keyMoment2495 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound77_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound77_e_oai
