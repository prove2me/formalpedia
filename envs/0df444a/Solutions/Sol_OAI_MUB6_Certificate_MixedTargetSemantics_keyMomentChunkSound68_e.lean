-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound68_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:01:47.187379+00:00
-- url     : https://prove2.me/submissions/b43a2918-e949-41ca-bc1b-daa180265ab5

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical325
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41664 raw41664Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw41664 raw41664Labels = mixedMoment B raw41664step0 raw41664step0Labels := by
      have hz : ∀ j, raw41664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41664step0 = (fun i j => raw41664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41664step0 raw41664; decide +kernel
      have hl : raw41664step0Labels = raw41664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41664 raw41664Labels permutation346 hz
    mixedMoment B raw41664step0 raw41664step0Labels = mixedMoment B raw41664step1 raw41664step1Labels := by
      have ha : raw41664step1 = (fun i j => raw41664step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41664step1 raw41664step0; decide +kernel
      have hl : raw41664step1Labels = raw41664step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41664step0 raw41664step0Labels permutation38 permutation2
    mixedMoment B raw41664step1 raw41664step1Labels = mixedMoment B raw41664step2 raw41664step2Labels := by
      have ha : raw41664step2 = raw41664step1 := by apply Matrix.ext; unfold raw41664step2 raw41664step1; decide +kernel
      have hl : raw41664step1Labels = labelEmbedding1 ∘ raw41664step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41664step1 raw41664step1Labels raw41664step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

theorem canonical41665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41665 raw41665Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw41665 raw41665Labels = mixedMoment B raw41665step0 raw41665step0Labels := by
      have hz : ∀ j, raw41665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41665step0 = (fun i j => raw41665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41665step0 raw41665; decide +kernel
      have hl : raw41665step0Labels = raw41665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41665 raw41665Labels permutation346 hz
    mixedMoment B raw41665step0 raw41665step0Labels = mixedMoment B raw41665step1 raw41665step1Labels := by
      have ha : raw41665step1 = (fun i j => raw41665step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41665step1 raw41665step0; decide +kernel
      have hl : raw41665step1Labels = raw41665step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41665step0 raw41665step0Labels permutation139 permutation7
    mixedMoment B raw41665step1 raw41665step1Labels = mixedMoment B raw41665step2 raw41665step2Labels := by
      have ha : raw41665step2 = raw41665step1 := by apply Matrix.ext; unfold raw41665step2 raw41665step1; decide +kernel
      have hl : raw41665step1Labels = labelEmbedding6 ∘ raw41665step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41665step1 raw41665step1Labels raw41665step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5140 node5140Labels := by rfl

theorem canonical41666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41666 raw41666Labels = mixedMoment B node2760 node2760Labels := by
  calc
    mixedMoment B raw41666 raw41666Labels = mixedMoment B raw41666step0 raw41666step0Labels := by
      have hz : ∀ j, raw41666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41666step0 = (fun i j => raw41666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41666step0 raw41666; decide +kernel
      have hl : raw41666step0Labels = raw41666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41666 raw41666Labels permutation346 hz
    mixedMoment B raw41666step0 raw41666step0Labels = mixedMoment B raw41666step1 raw41666step1Labels := by
      have ha : raw41666step1 = (fun i j => raw41666step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41666step1 raw41666step0; decide +kernel
      have hl : raw41666step1Labels = raw41666step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41666step0 raw41666step0Labels permutation37 permutation2
    mixedMoment B raw41666step1 raw41666step1Labels = mixedMoment B raw41666step2 raw41666step2Labels := by
      have ha : raw41666step2 = raw41666step1 := by apply Matrix.ext; unfold raw41666step2 raw41666step1; decide +kernel
      have hl : raw41666step1Labels = labelEmbedding1 ∘ raw41666step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41666step1 raw41666step1Labels raw41666step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2760 node2760Labels := by rfl

theorem canonical41667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41667 raw41667Labels = mixedMoment B node5288 node5288Labels := by
  calc
    mixedMoment B raw41667 raw41667Labels = mixedMoment B raw41667step0 raw41667step0Labels := by
      have hz : ∀ j, raw41667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41667step0 = (fun i j => raw41667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41667step0 raw41667; decide +kernel
      have hl : raw41667step0Labels = raw41667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41667 raw41667Labels permutation346 hz
    mixedMoment B raw41667step0 raw41667step0Labels = mixedMoment B raw41667step1 raw41667step1Labels := by
      have ha : raw41667step1 = (fun i j => raw41667step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41667step1 raw41667step0; decide +kernel
      have hl : raw41667step1Labels = raw41667step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41667step0 raw41667step0Labels permutation37 permutation2
    mixedMoment B raw41667step1 raw41667step1Labels = mixedMoment B raw41667step2 raw41667step2Labels := by
      have ha : raw41667step2 = raw41667step1 := by apply Matrix.ext; unfold raw41667step2 raw41667step1; decide +kernel
      have hl : raw41667step1Labels = labelEmbedding8 ∘ raw41667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41667step1 raw41667step1Labels raw41667step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5288 node5288Labels := by rfl

theorem canonical41668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41668 raw41668Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw41668 raw41668Labels = mixedMoment B raw41668step0 raw41668step0Labels := by
      have hz : ∀ j, raw41668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41668step0 = (fun i j => raw41668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41668step0 raw41668; decide +kernel
      have hl : raw41668step0Labels = raw41668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41668 raw41668Labels permutation346 hz
    mixedMoment B raw41668step0 raw41668step0Labels = mixedMoment B raw41668step1 raw41668step1Labels := by
      have ha : raw41668step1 = (fun i j => raw41668step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41668step1 raw41668step0; decide +kernel
      have hl : raw41668step1Labels = raw41668step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41668step0 raw41668step0Labels permutation37 permutation2
    mixedMoment B raw41668step1 raw41668step1Labels = mixedMoment B raw41668step2 raw41668step2Labels := by
      have ha : raw41668step2 = raw41668step1 := by apply Matrix.ext; unfold raw41668step2 raw41668step1; decide +kernel
      have hl : raw41668step1Labels = labelEmbedding1 ∘ raw41668step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41668step1 raw41668step1Labels raw41668step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

theorem canonical41669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41669 raw41669Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw41669 raw41669Labels = mixedMoment B raw41669step0 raw41669step0Labels := by
      have hz : ∀ j, raw41669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41669step0 = (fun i j => raw41669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41669step0 raw41669; decide +kernel
      have hl : raw41669step0Labels = raw41669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41669 raw41669Labels permutation346 hz
    mixedMoment B raw41669step0 raw41669step0Labels = mixedMoment B raw41669step1 raw41669step1Labels := by
      have ha : raw41669step1 = (fun i j => raw41669step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41669step1 raw41669step0; decide +kernel
      have hl : raw41669step1Labels = raw41669step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41669step0 raw41669step0Labels permutation37 permutation2
    mixedMoment B raw41669step1 raw41669step1Labels = mixedMoment B raw41669step2 raw41669step2Labels := by
      have ha : raw41669step2 = raw41669step1 := by apply Matrix.ext; unfold raw41669step2 raw41669step1; decide +kernel
      have hl : raw41669step1Labels = labelEmbedding8 ∘ raw41669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41669step1 raw41669step1Labels raw41669step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical41670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41670 raw41670Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw41670 raw41670Labels = mixedMoment B raw41670step0 raw41670step0Labels := by
      have ha : raw41670step0 = (fun i j => raw41670 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41670step0 raw41670; decide +kernel
      have hl : raw41670step0Labels = raw41670Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41670 raw41670Labels permutation181 permutation2
    mixedMoment B raw41670step0 raw41670step0Labels = mixedMoment B raw41670step1 raw41670step1Labels := by
      have ha : raw41670step1 = raw41670step0 := by apply Matrix.ext; unfold raw41670step1 raw41670step0; decide +kernel
      have hl : raw41670step0Labels = labelEmbedding1 ∘ raw41670step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41670step0 raw41670step0Labels raw41670step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2718 node2718Labels := by rfl

theorem canonical41671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41671 raw41671Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw41671 raw41671Labels = mixedMoment B raw41671step0 raw41671step0Labels := by
      have ha : raw41671step0 = (fun i j => raw41671 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41671step0 raw41671; decide +kernel
      have hl : raw41671step0Labels = raw41671Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41671 raw41671Labels permutation181 permutation2
    mixedMoment B raw41671step0 raw41671step0Labels = mixedMoment B raw41671step1 raw41671step1Labels := by
      have ha : raw41671step1 = raw41671step0 := by apply Matrix.ext; unfold raw41671step1 raw41671step0; decide +kernel
      have hl : raw41671step0Labels = labelEmbedding8 ∘ raw41671step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41671step0 raw41671step0Labels raw41671step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

theorem canonical41672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41672 raw41672Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw41672 raw41672Labels = mixedMoment B raw41672step0 raw41672step0Labels := by
      have ha : raw41672step0 = (fun i j => raw41672 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41672step0 raw41672; decide +kernel
      have hl : raw41672step0Labels = raw41672Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41672 raw41672Labels permutation181 permutation2
    mixedMoment B raw41672step0 raw41672step0Labels = mixedMoment B raw41672step1 raw41672step1Labels := by
      have ha : raw41672step1 = raw41672step0 := by apply Matrix.ext; unfold raw41672step1 raw41672step0; decide +kernel
      have hl : raw41672step0Labels = labelEmbedding1 ∘ raw41672step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41672step0 raw41672step0Labels raw41672step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical41673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41673 raw41673Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw41673 raw41673Labels = mixedMoment B raw41673step0 raw41673step0Labels := by
      have ha : raw41673step0 = (fun i j => raw41673 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41673step0 raw41673; decide +kernel
      have hl : raw41673step0Labels = raw41673Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41673 raw41673Labels permutation181 permutation2
    mixedMoment B raw41673step0 raw41673step0Labels = mixedMoment B raw41673step1 raw41673step1Labels := by
      have ha : raw41673step1 = raw41673step0 := by apply Matrix.ext; unfold raw41673step1 raw41673step0; decide +kernel
      have hl : raw41673step0Labels = labelEmbedding8 ∘ raw41673step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41673step0 raw41673step0Labels raw41673step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical41674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41674 raw41674Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw41674 raw41674Labels = mixedMoment B raw41674step0 raw41674step0Labels := by
      have hz : ∀ j, raw41674 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41674step0 = (fun i j => raw41674 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41674step0 raw41674; decide +kernel
      have hl : raw41674step0Labels = raw41674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41674 raw41674Labels permutation434 hz
    mixedMoment B raw41674step0 raw41674step0Labels = mixedMoment B raw41674step1 raw41674step1Labels := by
      have hz : ∀ j, raw41674step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41674step1 = (fun i j => raw41674step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41674step1 raw41674step0; decide +kernel
      have hl : raw41674step1Labels = raw41674step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41674step0 raw41674step0Labels permutation80 hz
    mixedMoment B raw41674step1 raw41674step1Labels = mixedMoment B raw41674step2 raw41674step2Labels := by
      have hz : ∀ j, raw41674step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41674step2 = (fun i j => raw41674step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41674step2 raw41674step1; decide +kernel
      have hl : raw41674step2Labels = raw41674step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41674step1 raw41674step1Labels permutation14 hz
    mixedMoment B raw41674step2 raw41674step2Labels = mixedMoment B raw41674step3 raw41674step3Labels := by
      have ha : raw41674step3 = raw41674step2 := by apply Matrix.ext; unfold raw41674step3 raw41674step2; decide +kernel
      have hl : raw41674step2Labels = labelEmbedding1 ∘ raw41674step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41674step2 raw41674step2Labels raw41674step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2789 node2789Labels := by rfl

theorem canonical41675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41675 raw41675Labels = mixedMoment B node5311 node5311Labels := by
  calc
    mixedMoment B raw41675 raw41675Labels = mixedMoment B raw41675step0 raw41675step0Labels := by
      have hz : ∀ j, raw41675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41675step0 = (fun i j => raw41675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41675step0 raw41675; decide +kernel
      have hl : raw41675step0Labels = raw41675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41675 raw41675Labels permutation434 hz
    mixedMoment B raw41675step0 raw41675step0Labels = mixedMoment B raw41675step1 raw41675step1Labels := by
      have hz : ∀ j, raw41675step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41675step1 = (fun i j => raw41675step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41675step1 raw41675step0; decide +kernel
      have hl : raw41675step1Labels = raw41675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41675step0 raw41675step0Labels permutation80 hz
    mixedMoment B raw41675step1 raw41675step1Labels = mixedMoment B raw41675step2 raw41675step2Labels := by
      have hz : ∀ j, raw41675step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41675step2 = (fun i j => raw41675step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41675step2 raw41675step1; decide +kernel
      have hl : raw41675step2Labels = raw41675step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41675step1 raw41675step1Labels permutation14 hz
    mixedMoment B raw41675step2 raw41675step2Labels = mixedMoment B raw41675step3 raw41675step3Labels := by
      have ha : raw41675step3 = raw41675step2 := by apply Matrix.ext; unfold raw41675step3 raw41675step2; decide +kernel
      have hl : raw41675step2Labels = labelEmbedding8 ∘ raw41675step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41675step2 raw41675step2Labels raw41675step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5311 node5311Labels := by rfl

theorem canonical41676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41676 raw41676Labels = mixedMoment B node2780 node2780Labels := by
  calc
    mixedMoment B raw41676 raw41676Labels = mixedMoment B raw41676step0 raw41676step0Labels := by
      have hz : ∀ j, raw41676 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41676step0 = (fun i j => raw41676 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41676step0 raw41676; decide +kernel
      have hl : raw41676step0Labels = raw41676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41676 raw41676Labels permutation434 hz
    mixedMoment B raw41676step0 raw41676step0Labels = mixedMoment B raw41676step1 raw41676step1Labels := by
      have hz : ∀ j, raw41676step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41676step1 = (fun i j => raw41676step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41676step1 raw41676step0; decide +kernel
      have hl : raw41676step1Labels = raw41676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41676step0 raw41676step0Labels permutation80 hz
    mixedMoment B raw41676step1 raw41676step1Labels = mixedMoment B raw41676step2 raw41676step2Labels := by
      have hz : ∀ j, raw41676step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41676step2 = (fun i j => raw41676step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41676step2 raw41676step1; decide +kernel
      have hl : raw41676step2Labels = raw41676step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41676step1 raw41676step1Labels permutation14 hz
    mixedMoment B raw41676step2 raw41676step2Labels = mixedMoment B raw41676step3 raw41676step3Labels := by
      have ha : raw41676step3 = raw41676step2 := by apply Matrix.ext; unfold raw41676step3 raw41676step2; decide +kernel
      have hl : raw41676step2Labels = labelEmbedding1 ∘ raw41676step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41676step2 raw41676step2Labels raw41676step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2780 node2780Labels := by rfl

theorem canonical41677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41677 raw41677Labels = mixedMoment B node4626 node4626Labels := by
  calc
    mixedMoment B raw41677 raw41677Labels = mixedMoment B raw41677step0 raw41677step0Labels := by
      have hz : ∀ j, raw41677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41677step0 = (fun i j => raw41677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41677step0 raw41677; decide +kernel
      have hl : raw41677step0Labels = raw41677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41677 raw41677Labels permutation434 hz
    mixedMoment B raw41677step0 raw41677step0Labels = mixedMoment B raw41677step1 raw41677step1Labels := by
      have hz : ∀ j, raw41677step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41677step1 = (fun i j => raw41677step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41677step1 raw41677step0; decide +kernel
      have hl : raw41677step1Labels = raw41677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41677step0 raw41677step0Labels permutation80 hz
    mixedMoment B raw41677step1 raw41677step1Labels = mixedMoment B raw41677step2 raw41677step2Labels := by
      have hz : ∀ j, raw41677step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41677step2 = (fun i j => raw41677step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41677step2 raw41677step1; decide +kernel
      have hl : raw41677step2Labels = raw41677step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41677step1 raw41677step1Labels permutation14 hz
    mixedMoment B raw41677step2 raw41677step2Labels = mixedMoment B raw41677step3 raw41677step3Labels := by
      have ha : raw41677step3 = (fun i j => raw41677step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41677step3 raw41677step2; decide +kernel
      have hl : raw41677step3Labels = raw41677step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41677step2 raw41677step2Labels permutation6 permutation6
    _ = mixedMoment B node4626 node4626Labels := by rfl

theorem canonical41678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41678 raw41678Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw41678 raw41678Labels = mixedMoment B raw41678step0 raw41678step0Labels := by
      have hz : ∀ j, raw41678 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41678step0 = (fun i j => raw41678 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41678step0 raw41678; decide +kernel
      have hl : raw41678step0Labels = raw41678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41678 raw41678Labels permutation346 hz
    mixedMoment B raw41678step0 raw41678step0Labels = mixedMoment B raw41678step1 raw41678step1Labels := by
      have hz : ∀ j, raw41678step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41678step1 = (fun i j => raw41678step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41678step1 raw41678step0; decide +kernel
      have hl : raw41678step1Labels = raw41678step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41678step0 raw41678step0Labels permutation56 hz
    mixedMoment B raw41678step1 raw41678step1Labels = mixedMoment B raw41678step2 raw41678step2Labels := by
      have ha : raw41678step2 = raw41678step1 := by apply Matrix.ext; unfold raw41678step2 raw41678step1; decide +kernel
      have hl : raw41678step1Labels = labelEmbedding1 ∘ raw41678step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41678step1 raw41678step1Labels raw41678step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

theorem canonical41679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41679 raw41679Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw41679 raw41679Labels = mixedMoment B raw41679step0 raw41679step0Labels := by
      have hz : ∀ j, raw41679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41679step0 = (fun i j => raw41679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41679step0 raw41679; decide +kernel
      have hl : raw41679step0Labels = raw41679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41679 raw41679Labels permutation346 hz
    mixedMoment B raw41679step0 raw41679step0Labels = mixedMoment B raw41679step1 raw41679step1Labels := by
      have hz : ∀ j, raw41679step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41679step1 = (fun i j => raw41679step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41679step1 raw41679step0; decide +kernel
      have hl : raw41679step1Labels = raw41679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41679step0 raw41679step0Labels permutation56 hz
    mixedMoment B raw41679step1 raw41679step1Labels = mixedMoment B raw41679step2 raw41679step2Labels := by
      have ha : raw41679step2 = raw41679step1 := by apply Matrix.ext; unfold raw41679step2 raw41679step1; decide +kernel
      have hl : raw41679step1Labels = labelEmbedding8 ∘ raw41679step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41679step1 raw41679step1Labels raw41679step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

theorem canonical41680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41680 raw41680Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw41680 raw41680Labels = mixedMoment B raw41680step0 raw41680step0Labels := by
      have hz : ∀ j, raw41680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41680step0 = (fun i j => raw41680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41680step0 raw41680; decide +kernel
      have hl : raw41680step0Labels = raw41680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41680 raw41680Labels permutation346 hz
    mixedMoment B raw41680step0 raw41680step0Labels = mixedMoment B raw41680step1 raw41680step1Labels := by
      have hz : ∀ j, raw41680step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41680step1 = (fun i j => raw41680step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41680step1 raw41680step0; decide +kernel
      have hl : raw41680step1Labels = raw41680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41680step0 raw41680step0Labels permutation56 hz
    mixedMoment B raw41680step1 raw41680step1Labels = mixedMoment B raw41680step2 raw41680step2Labels := by
      have ha : raw41680step2 = raw41680step1 := by apply Matrix.ext; unfold raw41680step2 raw41680step1; decide +kernel
      have hl : raw41680step1Labels = labelEmbedding1 ∘ raw41680step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41680step1 raw41680step1Labels raw41680step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical41681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41681 raw41681Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw41681 raw41681Labels = mixedMoment B raw41681step0 raw41681step0Labels := by
      have hz : ∀ j, raw41681 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41681step0 = (fun i j => raw41681 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41681step0 raw41681; decide +kernel
      have hl : raw41681step0Labels = raw41681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41681 raw41681Labels permutation346 hz
    mixedMoment B raw41681step0 raw41681step0Labels = mixedMoment B raw41681step1 raw41681step1Labels := by
      have hz : ∀ j, raw41681step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41681step1 = (fun i j => raw41681step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41681step1 raw41681step0; decide +kernel
      have hl : raw41681step1Labels = raw41681step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41681step0 raw41681step0Labels permutation56 hz
    mixedMoment B raw41681step1 raw41681step1Labels = mixedMoment B raw41681step2 raw41681step2Labels := by
      have ha : raw41681step2 = (fun i j => raw41681step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41681step2 raw41681step1; decide +kernel
      have hl : raw41681step2Labels = raw41681step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41681step1 raw41681step1Labels permutation31 permutation7
    mixedMoment B raw41681step2 raw41681step2Labels = mixedMoment B raw41681step3 raw41681step3Labels := by
      have ha : raw41681step3 = raw41681step2 := by apply Matrix.ext; unfold raw41681step3 raw41681step2; decide +kernel
      have hl : raw41681step2Labels = labelEmbedding6 ∘ raw41681step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41681step2 raw41681step2Labels raw41681step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4617 node4617Labels := by rfl

theorem canonical41682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41682 raw41682Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw41682 raw41682Labels = mixedMoment B raw41682step0 raw41682step0Labels := by
      have hz : ∀ j, raw41682 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41682step0 = (fun i j => raw41682 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41682step0 raw41682; decide +kernel
      have hl : raw41682step0Labels = raw41682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41682 raw41682Labels permutation346 hz
    mixedMoment B raw41682step0 raw41682step0Labels = mixedMoment B raw41682step1 raw41682step1Labels := by
      have hz : ∀ j, raw41682step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41682step1 = (fun i j => raw41682step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41682step1 raw41682step0; decide +kernel
      have hl : raw41682step1Labels = raw41682step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41682step0 raw41682step0Labels permutation56 hz
    mixedMoment B raw41682step1 raw41682step1Labels = mixedMoment B raw41682step2 raw41682step2Labels := by
      have ha : raw41682step2 = raw41682step1 := by apply Matrix.ext; unfold raw41682step2 raw41682step1; decide +kernel
      have hl : raw41682step1Labels = labelEmbedding1 ∘ raw41682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41682step1 raw41682step1Labels raw41682step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

theorem canonical41683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41683 raw41683Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw41683 raw41683Labels = mixedMoment B raw41683step0 raw41683step0Labels := by
      have hz : ∀ j, raw41683 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41683step0 = (fun i j => raw41683 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41683step0 raw41683; decide +kernel
      have hl : raw41683step0Labels = raw41683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41683 raw41683Labels permutation346 hz
    mixedMoment B raw41683step0 raw41683step0Labels = mixedMoment B raw41683step1 raw41683step1Labels := by
      have hz : ∀ j, raw41683step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41683step1 = (fun i j => raw41683step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41683step1 raw41683step0; decide +kernel
      have hl : raw41683step1Labels = raw41683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41683step0 raw41683step0Labels permutation56 hz
    mixedMoment B raw41683step1 raw41683step1Labels = mixedMoment B raw41683step2 raw41683step2Labels := by
      have ha : raw41683step2 = (fun i j => raw41683step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41683step2 raw41683step1; decide +kernel
      have hl : raw41683step2Labels = raw41683step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41683step1 raw41683step1Labels permutation31 permutation7
    mixedMoment B raw41683step2 raw41683step2Labels = mixedMoment B raw41683step3 raw41683step3Labels := by
      have ha : raw41683step3 = raw41683step2 := by apply Matrix.ext; unfold raw41683step3 raw41683step2; decide +kernel
      have hl : raw41683step2Labels = labelEmbedding6 ∘ raw41683step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41683step2 raw41683step2Labels raw41683step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

theorem canonical41684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41684 raw41684Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw41684 raw41684Labels = mixedMoment B raw41684step0 raw41684step0Labels := by
      have hz : ∀ j, raw41684 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41684step0 = (fun i j => raw41684 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41684step0 raw41684; decide +kernel
      have hl : raw41684step0Labels = raw41684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41684 raw41684Labels permutation346 hz
    mixedMoment B raw41684step0 raw41684step0Labels = mixedMoment B raw41684step1 raw41684step1Labels := by
      have hz : ∀ j, raw41684step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41684step1 = (fun i j => raw41684step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41684step1 raw41684step0; decide +kernel
      have hl : raw41684step1Labels = raw41684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41684step0 raw41684step0Labels permutation56 hz
    mixedMoment B raw41684step1 raw41684step1Labels = mixedMoment B raw41684step2 raw41684step2Labels := by
      have ha : raw41684step2 = (fun i j => raw41684step1 (permutation30 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41684step2 raw41684step1; decide +kernel
      have hl : raw41684step2Labels = raw41684step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41684step1 raw41684step1Labels permutation30 permutation4
    mixedMoment B raw41684step2 raw41684step2Labels = mixedMoment B raw41684step3 raw41684step3Labels := by
      have ha : raw41684step3 = raw41684step2 := by apply Matrix.ext; unfold raw41684step3 raw41684step2; decide +kernel
      have hl : raw41684step2Labels = labelEmbedding1 ∘ raw41684step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41684step2 raw41684step2Labels raw41684step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

theorem canonical41685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41685 raw41685Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw41685 raw41685Labels = mixedMoment B raw41685step0 raw41685step0Labels := by
      have hz : ∀ j, raw41685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41685step0 = (fun i j => raw41685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41685step0 raw41685; decide +kernel
      have hl : raw41685step0Labels = raw41685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41685 raw41685Labels permutation346 hz
    mixedMoment B raw41685step0 raw41685step0Labels = mixedMoment B raw41685step1 raw41685step1Labels := by
      have hz : ∀ j, raw41685step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41685step1 = (fun i j => raw41685step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41685step1 raw41685step0; decide +kernel
      have hl : raw41685step1Labels = raw41685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41685step0 raw41685step0Labels permutation56 hz
    mixedMoment B raw41685step1 raw41685step1Labels = mixedMoment B raw41685step2 raw41685step2Labels := by
      have ha : raw41685step2 = (fun i j => raw41685step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41685step2 raw41685step1; decide +kernel
      have hl : raw41685step2Labels = raw41685step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41685step1 raw41685step1Labels permutation16 permutation6
    _ = mixedMoment B node5175 node5175Labels := by rfl

theorem canonical41686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41686 raw41686Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw41686 raw41686Labels = mixedMoment B raw41686step0 raw41686step0Labels := by
      have hz : ∀ j, raw41686 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41686step0 = (fun i j => raw41686 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41686step0 raw41686; decide +kernel
      have hl : raw41686step0Labels = raw41686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41686 raw41686Labels permutation346 hz
    mixedMoment B raw41686step0 raw41686step0Labels = mixedMoment B raw41686step1 raw41686step1Labels := by
      have hz : ∀ j, raw41686step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41686step1 = (fun i j => raw41686step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41686step1 raw41686step0; decide +kernel
      have hl : raw41686step1Labels = raw41686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41686step0 raw41686step0Labels permutation56 hz
    mixedMoment B raw41686step1 raw41686step1Labels = mixedMoment B raw41686step2 raw41686step2Labels := by
      have ha : raw41686step2 = (fun i j => raw41686step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41686step2 raw41686step1; decide +kernel
      have hl : raw41686step2Labels = raw41686step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41686step1 raw41686step1Labels permutation13 permutation2
    mixedMoment B raw41686step2 raw41686step2Labels = mixedMoment B raw41686step3 raw41686step3Labels := by
      have ha : raw41686step3 = raw41686step2 := by apply Matrix.ext; unfold raw41686step3 raw41686step2; decide +kernel
      have hl : raw41686step2Labels = labelEmbedding1 ∘ raw41686step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41686step2 raw41686step2Labels raw41686step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

theorem canonical41687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41687 raw41687Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw41687 raw41687Labels = mixedMoment B raw41687step0 raw41687step0Labels := by
      have hz : ∀ j, raw41687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41687step0 = (fun i j => raw41687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41687step0 raw41687; decide +kernel
      have hl : raw41687step0Labels = raw41687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41687 raw41687Labels permutation346 hz
    mixedMoment B raw41687step0 raw41687step0Labels = mixedMoment B raw41687step1 raw41687step1Labels := by
      have hz : ∀ j, raw41687step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41687step1 = (fun i j => raw41687step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41687step1 raw41687step0; decide +kernel
      have hl : raw41687step1Labels = raw41687step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41687step0 raw41687step0Labels permutation56 hz
    mixedMoment B raw41687step1 raw41687step1Labels = mixedMoment B raw41687step2 raw41687step2Labels := by
      have ha : raw41687step2 = (fun i j => raw41687step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41687step2 raw41687step1; decide +kernel
      have hl : raw41687step2Labels = raw41687step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41687step1 raw41687step1Labels permutation17 permutation6
    _ = mixedMoment B node5295 node5295Labels := by rfl

theorem canonical41688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41688 raw41688Labels = mixedMoment B node2779 node2779Labels := by
  calc
    mixedMoment B raw41688 raw41688Labels = mixedMoment B raw41688step0 raw41688step0Labels := by
      have hz : ∀ j, raw41688 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41688step0 = (fun i j => raw41688 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41688step0 raw41688; decide +kernel
      have hl : raw41688step0Labels = raw41688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41688 raw41688Labels permutation346 hz
    mixedMoment B raw41688step0 raw41688step0Labels = mixedMoment B raw41688step1 raw41688step1Labels := by
      have hz : ∀ j, raw41688step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41688step1 = (fun i j => raw41688step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41688step1 raw41688step0; decide +kernel
      have hl : raw41688step1Labels = raw41688step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41688step0 raw41688step0Labels permutation56 hz
    mixedMoment B raw41688step1 raw41688step1Labels = mixedMoment B raw41688step2 raw41688step2Labels := by
      have ha : raw41688step2 = (fun i j => raw41688step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41688step2 raw41688step1; decide +kernel
      have hl : raw41688step2Labels = raw41688step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41688step1 raw41688step1Labels permutation12 permutation2
    mixedMoment B raw41688step2 raw41688step2Labels = mixedMoment B raw41688step3 raw41688step3Labels := by
      have ha : raw41688step3 = raw41688step2 := by apply Matrix.ext; unfold raw41688step3 raw41688step2; decide +kernel
      have hl : raw41688step2Labels = labelEmbedding1 ∘ raw41688step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41688step2 raw41688step2Labels raw41688step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2779 node2779Labels := by rfl

theorem canonical41689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41689 raw41689Labels = mixedMoment B node5303 node5303Labels := by
  calc
    mixedMoment B raw41689 raw41689Labels = mixedMoment B raw41689step0 raw41689step0Labels := by
      have hz : ∀ j, raw41689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41689step0 = (fun i j => raw41689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41689step0 raw41689; decide +kernel
      have hl : raw41689step0Labels = raw41689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41689 raw41689Labels permutation346 hz
    mixedMoment B raw41689step0 raw41689step0Labels = mixedMoment B raw41689step1 raw41689step1Labels := by
      have hz : ∀ j, raw41689step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41689step1 = (fun i j => raw41689step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41689step1 raw41689step0; decide +kernel
      have hl : raw41689step1Labels = raw41689step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41689step0 raw41689step0Labels permutation56 hz
    mixedMoment B raw41689step1 raw41689step1Labels = mixedMoment B raw41689step2 raw41689step2Labels := by
      have ha : raw41689step2 = (fun i j => raw41689step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41689step2 raw41689step1; decide +kernel
      have hl : raw41689step2Labels = raw41689step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41689step1 raw41689step1Labels permutation12 permutation2
    mixedMoment B raw41689step2 raw41689step2Labels = mixedMoment B raw41689step3 raw41689step3Labels := by
      have ha : raw41689step3 = raw41689step2 := by apply Matrix.ext; unfold raw41689step3 raw41689step2; decide +kernel
      have hl : raw41689step2Labels = labelEmbedding8 ∘ raw41689step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41689step2 raw41689step2Labels raw41689step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5303 node5303Labels := by rfl

theorem canonical41690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41690 raw41690Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw41690 raw41690Labels = mixedMoment B raw41690step0 raw41690step0Labels := by
      have hz : ∀ j, raw41690 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41690step0 = (fun i j => raw41690 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41690step0 raw41690; decide +kernel
      have hl : raw41690step0Labels = raw41690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41690 raw41690Labels permutation265 hz
    mixedMoment B raw41690step0 raw41690step0Labels = mixedMoment B raw41690step1 raw41690step1Labels := by
      have ha : raw41690step1 = raw41690step0 := by apply Matrix.ext; unfold raw41690step1 raw41690step0; decide +kernel
      have hl : raw41690step0Labels = labelEmbedding1 ∘ raw41690step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41690step0 raw41690step0Labels raw41690step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

theorem canonical41691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41691 raw41691Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw41691 raw41691Labels = mixedMoment B raw41691step0 raw41691step0Labels := by
      have hz : ∀ j, raw41691 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41691step0 = (fun i j => raw41691 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41691step0 raw41691; decide +kernel
      have hl : raw41691step0Labels = raw41691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41691 raw41691Labels permutation265 hz
    mixedMoment B raw41691step0 raw41691step0Labels = mixedMoment B raw41691step1 raw41691step1Labels := by
      have ha : raw41691step1 = (fun i j => raw41691step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41691step1 raw41691step0; decide +kernel
      have hl : raw41691step1Labels = raw41691step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41691step0 raw41691step0Labels permutation149 permutation7
    mixedMoment B raw41691step1 raw41691step1Labels = mixedMoment B raw41691step2 raw41691step2Labels := by
      have ha : raw41691step2 = raw41691step1 := by apply Matrix.ext; unfold raw41691step2 raw41691step1; decide +kernel
      have hl : raw41691step1Labels = labelEmbedding6 ∘ raw41691step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41691step1 raw41691step1Labels raw41691step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4600 node4600Labels := by rfl

theorem canonical41692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41692 raw41692Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw41692 raw41692Labels = mixedMoment B raw41692step0 raw41692step0Labels := by
      have hz : ∀ j, raw41692 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41692step0 = (fun i j => raw41692 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41692step0 raw41692; decide +kernel
      have hl : raw41692step0Labels = raw41692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41692 raw41692Labels permutation265 hz
    mixedMoment B raw41692step0 raw41692step0Labels = mixedMoment B raw41692step1 raw41692step1Labels := by
      have ha : raw41692step1 = (fun i j => raw41692step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41692step1 raw41692step0; decide +kernel
      have hl : raw41692step1Labels = raw41692step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41692step0 raw41692step0Labels permutation37 permutation2
    mixedMoment B raw41692step1 raw41692step1Labels = mixedMoment B raw41692step2 raw41692step2Labels := by
      have ha : raw41692step2 = raw41692step1 := by apply Matrix.ext; unfold raw41692step2 raw41692step1; decide +kernel
      have hl : raw41692step1Labels = labelEmbedding1 ∘ raw41692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41692step1 raw41692step1Labels raw41692step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

theorem canonical41693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41693 raw41693Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw41693 raw41693Labels = mixedMoment B raw41693step0 raw41693step0Labels := by
      have hz : ∀ j, raw41693 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41693step0 = (fun i j => raw41693 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41693step0 raw41693; decide +kernel
      have hl : raw41693step0Labels = raw41693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41693 raw41693Labels permutation265 hz
    mixedMoment B raw41693step0 raw41693step0Labels = mixedMoment B raw41693step1 raw41693step1Labels := by
      have ha : raw41693step1 = (fun i j => raw41693step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41693step1 raw41693step0; decide +kernel
      have hl : raw41693step1Labels = raw41693step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41693step0 raw41693step0Labels permutation95 permutation6
    _ = mixedMoment B node5173 node5173Labels := by rfl

theorem canonical41694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41694 raw41694Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw41694 raw41694Labels = mixedMoment B raw41694step0 raw41694step0Labels := by
      have hz : ∀ j, raw41694 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41694step0 = (fun i j => raw41694 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41694step0 raw41694; decide +kernel
      have hl : raw41694step0Labels = raw41694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41694 raw41694Labels permutation265 hz
    mixedMoment B raw41694step0 raw41694step0Labels = mixedMoment B raw41694step1 raw41694step1Labels := by
      have ha : raw41694step1 = (fun i j => raw41694step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41694step1 raw41694step0; decide +kernel
      have hl : raw41694step1Labels = raw41694step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41694step0 raw41694step0Labels permutation35 permutation2
    mixedMoment B raw41694step1 raw41694step1Labels = mixedMoment B raw41694step2 raw41694step2Labels := by
      have ha : raw41694step2 = raw41694step1 := by apply Matrix.ext; unfold raw41694step2 raw41694step1; decide +kernel
      have hl : raw41694step1Labels = labelEmbedding1 ∘ raw41694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41694step1 raw41694step1Labels raw41694step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

theorem canonical41695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41695 raw41695Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw41695 raw41695Labels = mixedMoment B raw41695step0 raw41695step0Labels := by
      have hz : ∀ j, raw41695 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41695step0 = (fun i j => raw41695 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41695step0 raw41695; decide +kernel
      have hl : raw41695step0Labels = raw41695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41695 raw41695Labels permutation265 hz
    mixedMoment B raw41695step0 raw41695step0Labels = mixedMoment B raw41695step1 raw41695step1Labels := by
      have ha : raw41695step1 = (fun i j => raw41695step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41695step1 raw41695step0; decide +kernel
      have hl : raw41695step1Labels = raw41695step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41695step0 raw41695step0Labels permutation35 permutation2
    mixedMoment B raw41695step1 raw41695step1Labels = mixedMoment B raw41695step2 raw41695step2Labels := by
      have ha : raw41695step2 = raw41695step1 := by apply Matrix.ext; unfold raw41695step2 raw41695step1; decide +kernel
      have hl : raw41695step1Labels = labelEmbedding8 ∘ raw41695step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41695step1 raw41695step1Labels raw41695step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

theorem canonical41696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41696 raw41696Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw41696 raw41696Labels = mixedMoment B raw41696step0 raw41696step0Labels := by
      have hz : ∀ j, raw41696 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41696step0 = (fun i j => raw41696 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41696step0 raw41696; decide +kernel
      have hl : raw41696step0Labels = raw41696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41696 raw41696Labels permutation265 hz
    mixedMoment B raw41696step0 raw41696step0Labels = mixedMoment B raw41696step1 raw41696step1Labels := by
      have ha : raw41696step1 = (fun i j => raw41696step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41696step1 raw41696step0; decide +kernel
      have hl : raw41696step1Labels = raw41696step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41696step0 raw41696step0Labels permutation36 permutation2
    mixedMoment B raw41696step1 raw41696step1Labels = mixedMoment B raw41696step2 raw41696step2Labels := by
      have ha : raw41696step2 = raw41696step1 := by apply Matrix.ext; unfold raw41696step2 raw41696step1; decide +kernel
      have hl : raw41696step1Labels = labelEmbedding1 ∘ raw41696step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41696step1 raw41696step1Labels raw41696step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2736 node2736Labels := by rfl

theorem canonical41697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41697 raw41697Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw41697 raw41697Labels = mixedMoment B raw41697step0 raw41697step0Labels := by
      have hz : ∀ j, raw41697 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41697step0 = (fun i j => raw41697 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41697step0 raw41697; decide +kernel
      have hl : raw41697step0Labels = raw41697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41697 raw41697Labels permutation265 hz
    mixedMoment B raw41697step0 raw41697step0Labels = mixedMoment B raw41697step1 raw41697step1Labels := by
      have ha : raw41697step1 = (fun i j => raw41697step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41697step1 raw41697step0; decide +kernel
      have hl : raw41697step1Labels = raw41697step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41697step0 raw41697step0Labels permutation36 permutation2
    mixedMoment B raw41697step1 raw41697step1Labels = mixedMoment B raw41697step2 raw41697step2Labels := by
      have ha : raw41697step2 = raw41697step1 := by apply Matrix.ext; unfold raw41697step2 raw41697step1; decide +kernel
      have hl : raw41697step1Labels = labelEmbedding8 ∘ raw41697step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41697step1 raw41697step1Labels raw41697step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

theorem canonical41698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41698 raw41698Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw41698 raw41698Labels = mixedMoment B raw41698step0 raw41698step0Labels := by
      have hz : ∀ j, raw41698 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41698step0 = (fun i j => raw41698 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41698step0 raw41698; decide +kernel
      have hl : raw41698step0Labels = raw41698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41698 raw41698Labels permutation265 hz
    mixedMoment B raw41698step0 raw41698step0Labels = mixedMoment B raw41698step1 raw41698step1Labels := by
      have ha : raw41698step1 = (fun i j => raw41698step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41698step1 raw41698step0; decide +kernel
      have hl : raw41698step1Labels = raw41698step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41698step0 raw41698step0Labels permutation37 permutation2
    mixedMoment B raw41698step1 raw41698step1Labels = mixedMoment B raw41698step2 raw41698step2Labels := by
      have ha : raw41698step2 = raw41698step1 := by apply Matrix.ext; unfold raw41698step2 raw41698step1; decide +kernel
      have hl : raw41698step1Labels = labelEmbedding1 ∘ raw41698step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41698step1 raw41698step1Labels raw41698step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

theorem canonical41699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41699 raw41699Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw41699 raw41699Labels = mixedMoment B raw41699step0 raw41699step0Labels := by
      have hz : ∀ j, raw41699 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41699step0 = (fun i j => raw41699 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41699step0 raw41699; decide +kernel
      have hl : raw41699step0Labels = raw41699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41699 raw41699Labels permutation265 hz
    mixedMoment B raw41699step0 raw41699step0Labels = mixedMoment B raw41699step1 raw41699step1Labels := by
      have ha : raw41699step1 = (fun i j => raw41699step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41699step1 raw41699step0; decide +kernel
      have hl : raw41699step1Labels = raw41699step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41699step0 raw41699step0Labels permutation96 permutation6
    _ = mixedMoment B node5151 node5151Labels := by rfl

theorem canonical41700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41700 raw41700Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw41700 raw41700Labels = mixedMoment B raw41700step0 raw41700step0Labels := by
      have hz : ∀ j, raw41700 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41700step0 = (fun i j => raw41700 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41700step0 raw41700; decide +kernel
      have hl : raw41700step0Labels = raw41700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41700 raw41700Labels permutation265 hz
    mixedMoment B raw41700step0 raw41700step0Labels = mixedMoment B raw41700step1 raw41700step1Labels := by
      have ha : raw41700step1 = (fun i j => raw41700step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41700step1 raw41700step0; decide +kernel
      have hl : raw41700step1Labels = raw41700step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41700step0 raw41700step0Labels permutation36 permutation2
    mixedMoment B raw41700step1 raw41700step1Labels = mixedMoment B raw41700step2 raw41700step2Labels := by
      have ha : raw41700step2 = raw41700step1 := by apply Matrix.ext; unfold raw41700step2 raw41700step1; decide +kernel
      have hl : raw41700step1Labels = labelEmbedding1 ∘ raw41700step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41700step1 raw41700step1Labels raw41700step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2682 node2682Labels := by rfl

theorem canonical41701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41701 raw41701Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw41701 raw41701Labels = mixedMoment B raw41701step0 raw41701step0Labels := by
      have hz : ∀ j, raw41701 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41701step0 = (fun i j => raw41701 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41701step0 raw41701; decide +kernel
      have hl : raw41701step0Labels = raw41701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41701 raw41701Labels permutation265 hz
    mixedMoment B raw41701step0 raw41701step0Labels = mixedMoment B raw41701step1 raw41701step1Labels := by
      have ha : raw41701step1 = (fun i j => raw41701step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41701step1 raw41701step0; decide +kernel
      have hl : raw41701step1Labels = raw41701step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41701step0 raw41701step0Labels permutation36 permutation2
    mixedMoment B raw41701step1 raw41701step1Labels = mixedMoment B raw41701step2 raw41701step2Labels := by
      have ha : raw41701step2 = raw41701step1 := by apply Matrix.ext; unfold raw41701step2 raw41701step1; decide +kernel
      have hl : raw41701step1Labels = labelEmbedding8 ∘ raw41701step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41701step1 raw41701step1Labels raw41701step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

theorem canonical41702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41702 raw41702Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw41702 raw41702Labels = mixedMoment B raw41702step0 raw41702step0Labels := by
      have ha : raw41702step0 = (fun i j => raw41702 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41702step0 raw41702; decide +kernel
      have hl : raw41702step0Labels = raw41702Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41702 raw41702Labels permutation157 permutation2
    mixedMoment B raw41702step0 raw41702step0Labels = mixedMoment B raw41702step1 raw41702step1Labels := by
      have ha : raw41702step1 = raw41702step0 := by apply Matrix.ext; unfold raw41702step1 raw41702step0; decide +kernel
      have hl : raw41702step0Labels = labelEmbedding1 ∘ raw41702step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41702step0 raw41702step0Labels raw41702step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2700 node2700Labels := by rfl

theorem canonical41703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41703 raw41703Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw41703 raw41703Labels = mixedMoment B raw41703step0 raw41703step0Labels := by
      have ha : raw41703step0 = (fun i j => raw41703 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41703step0 raw41703; decide +kernel
      have hl : raw41703step0Labels = raw41703Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41703 raw41703Labels permutation502 permutation6
    _ = mixedMoment B node5150 node5150Labels := by rfl

theorem canonical41704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41704 raw41704Labels = mixedMoment B node2285 node2285Labels := by
  calc
    mixedMoment B raw41704 raw41704Labels = mixedMoment B raw41704step0 raw41704step0Labels := by
      have hz : ∀ j, raw41704 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41704step0 = (fun i j => raw41704 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41704step0 raw41704; decide +kernel
      have hl : raw41704step0Labels = raw41704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41704 raw41704Labels permutation520 hz
    mixedMoment B raw41704step0 raw41704step0Labels = mixedMoment B raw41704step1 raw41704step1Labels := by
      have hz : ∀ j, raw41704step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41704step1 = (fun i j => raw41704step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41704step1 raw41704step0; decide +kernel
      have hl : raw41704step1Labels = raw41704step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41704step0 raw41704step0Labels permutation104 hz
    mixedMoment B raw41704step1 raw41704step1Labels = mixedMoment B raw41704step2 raw41704step2Labels := by
      have hz : ∀ j, raw41704step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41704step2 = (fun i j => raw41704step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41704step2 raw41704step1; decide +kernel
      have hl : raw41704step2Labels = raw41704step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41704step1 raw41704step1Labels permutation20 hz
    mixedMoment B raw41704step2 raw41704step2Labels = mixedMoment B raw41704step3 raw41704step3Labels := by
      have ha : raw41704step3 = raw41704step2 := by apply Matrix.ext; unfold raw41704step3 raw41704step2; decide +kernel
      have hl : raw41704step2Labels = labelEmbedding1 ∘ raw41704step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41704step2 raw41704step2Labels raw41704step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2285 node2285Labels := by rfl

theorem canonical41705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41705 raw41705Labels = mixedMoment B node4900 node4900Labels := by
  calc
    mixedMoment B raw41705 raw41705Labels = mixedMoment B raw41705step0 raw41705step0Labels := by
      have hz : ∀ j, raw41705 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41705step0 = (fun i j => raw41705 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41705step0 raw41705; decide +kernel
      have hl : raw41705step0Labels = raw41705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41705 raw41705Labels permutation520 hz
    mixedMoment B raw41705step0 raw41705step0Labels = mixedMoment B raw41705step1 raw41705step1Labels := by
      have hz : ∀ j, raw41705step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41705step1 = (fun i j => raw41705step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41705step1 raw41705step0; decide +kernel
      have hl : raw41705step1Labels = raw41705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41705step0 raw41705step0Labels permutation104 hz
    mixedMoment B raw41705step1 raw41705step1Labels = mixedMoment B raw41705step2 raw41705step2Labels := by
      have hz : ∀ j, raw41705step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41705step2 = (fun i j => raw41705step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41705step2 raw41705step1; decide +kernel
      have hl : raw41705step2Labels = raw41705step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41705step1 raw41705step1Labels permutation20 hz
    mixedMoment B raw41705step2 raw41705step2Labels = mixedMoment B raw41705step3 raw41705step3Labels := by
      have ha : raw41705step3 = raw41705step2 := by apply Matrix.ext; unfold raw41705step3 raw41705step2; decide +kernel
      have hl : raw41705step2Labels = labelEmbedding8 ∘ raw41705step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41705step2 raw41705step2Labels raw41705step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4900 node4900Labels := by rfl

theorem canonical41706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41706 raw41706Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw41706 raw41706Labels = mixedMoment B raw41706step0 raw41706step0Labels := by
      have hz : ∀ j, raw41706 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41706step0 = (fun i j => raw41706 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41706step0 raw41706; decide +kernel
      have hl : raw41706step0Labels = raw41706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41706 raw41706Labels permutation434 hz
    mixedMoment B raw41706step0 raw41706step0Labels = mixedMoment B raw41706step1 raw41706step1Labels := by
      have hz : ∀ j, raw41706step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41706step1 = (fun i j => raw41706step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41706step1 raw41706step0; decide +kernel
      have hl : raw41706step1Labels = raw41706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41706step0 raw41706step0Labels permutation80 hz
    mixedMoment B raw41706step1 raw41706step1Labels = mixedMoment B raw41706step2 raw41706step2Labels := by
      have ha : raw41706step2 = (fun i j => raw41706step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41706step2 raw41706step1; decide +kernel
      have hl : raw41706step2Labels = raw41706step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41706step1 raw41706step1Labels permutation16 permutation4
    mixedMoment B raw41706step2 raw41706step2Labels = mixedMoment B raw41706step3 raw41706step3Labels := by
      have ha : raw41706step3 = -raw41706step2 := by apply Matrix.ext; change ∀ i j, raw41706step3 i j = -(raw41706step2 i j); unfold raw41706step3 raw41706step2; decide +kernel
      have hl : raw41706step3Labels = raw41706step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41706step3 raw41706step3Labels = mixedMoment B raw41706step4 raw41706step4Labels := by
      have ha : raw41706step4 = raw41706step3 := by apply Matrix.ext; unfold raw41706step4 raw41706step3; decide +kernel
      have hl : raw41706step3Labels = labelEmbedding1 ∘ raw41706step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41706step3 raw41706step3Labels raw41706step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2222 node2222Labels := by rfl

theorem canonical41707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41707 raw41707Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw41707 raw41707Labels = mixedMoment B raw41707step0 raw41707step0Labels := by
      have hz : ∀ j, raw41707 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41707step0 = (fun i j => raw41707 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41707step0 raw41707; decide +kernel
      have hl : raw41707step0Labels = raw41707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41707 raw41707Labels permutation434 hz
    mixedMoment B raw41707step0 raw41707step0Labels = mixedMoment B raw41707step1 raw41707step1Labels := by
      have hz : ∀ j, raw41707step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41707step1 = (fun i j => raw41707step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41707step1 raw41707step0; decide +kernel
      have hl : raw41707step1Labels = raw41707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41707step0 raw41707step0Labels permutation80 hz
    mixedMoment B raw41707step1 raw41707step1Labels = mixedMoment B raw41707step2 raw41707step2Labels := by
      have ha : raw41707step2 = (fun i j => raw41707step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41707step2 raw41707step1; decide +kernel
      have hl : raw41707step2Labels = raw41707step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41707step1 raw41707step1Labels permutation17 permutation6
    _ = mixedMoment B node4844 node4844Labels := by rfl

theorem canonical41708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41708 raw41708Labels = mixedMoment B node2284 node2284Labels := by
  calc
    mixedMoment B raw41708 raw41708Labels = mixedMoment B raw41708step0 raw41708step0Labels := by
      have hz : ∀ j, raw41708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41708step0 = (fun i j => raw41708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41708step0 raw41708; decide +kernel
      have hl : raw41708step0Labels = raw41708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41708 raw41708Labels permutation434 hz
    mixedMoment B raw41708step0 raw41708step0Labels = mixedMoment B raw41708step1 raw41708step1Labels := by
      have hz : ∀ j, raw41708step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41708step1 = (fun i j => raw41708step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41708step1 raw41708step0; decide +kernel
      have hl : raw41708step1Labels = raw41708step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41708step0 raw41708step0Labels permutation80 hz
    mixedMoment B raw41708step1 raw41708step1Labels = mixedMoment B raw41708step2 raw41708step2Labels := by
      have ha : raw41708step2 = raw41708step1 := by apply Matrix.ext; unfold raw41708step2 raw41708step1; decide +kernel
      have hl : raw41708step1Labels = labelEmbedding1 ∘ raw41708step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41708step1 raw41708step1Labels raw41708step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2284 node2284Labels := by rfl

theorem canonical41709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41709 raw41709Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw41709 raw41709Labels = mixedMoment B raw41709step0 raw41709step0Labels := by
      have hz : ∀ j, raw41709 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41709step0 = (fun i j => raw41709 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41709step0 raw41709; decide +kernel
      have hl : raw41709step0Labels = raw41709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41709 raw41709Labels permutation434 hz
    mixedMoment B raw41709step0 raw41709step0Labels = mixedMoment B raw41709step1 raw41709step1Labels := by
      have hz : ∀ j, raw41709step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41709step1 = (fun i j => raw41709step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41709step1 raw41709step0; decide +kernel
      have hl : raw41709step1Labels = raw41709step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41709step0 raw41709step0Labels permutation80 hz
    mixedMoment B raw41709step1 raw41709step1Labels = mixedMoment B raw41709step2 raw41709step2Labels := by
      have ha : raw41709step2 = (fun i j => raw41709step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41709step2 raw41709step1; decide +kernel
      have hl : raw41709step2Labels = raw41709step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41709step1 raw41709step1Labels permutation17 permutation6
    _ = mixedMoment B node4892 node4892Labels := by rfl

theorem canonical41710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41710 raw41710Labels = mixedMoment B node2282 node2282Labels := by
  calc
    mixedMoment B raw41710 raw41710Labels = mixedMoment B raw41710step0 raw41710step0Labels := by
      have hz : ∀ j, raw41710 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41710step0 = (fun i j => raw41710 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41710step0 raw41710; decide +kernel
      have hl : raw41710step0Labels = raw41710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41710 raw41710Labels permutation434 hz
    mixedMoment B raw41710step0 raw41710step0Labels = mixedMoment B raw41710step1 raw41710step1Labels := by
      have hz : ∀ j, raw41710step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41710step1 = (fun i j => raw41710step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41710step1 raw41710step0; decide +kernel
      have hl : raw41710step1Labels = raw41710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41710step0 raw41710step0Labels permutation80 hz
    mixedMoment B raw41710step1 raw41710step1Labels = mixedMoment B raw41710step2 raw41710step2Labels := by
      have ha : raw41710step2 = raw41710step1 := by apply Matrix.ext; unfold raw41710step2 raw41710step1; decide +kernel
      have hl : raw41710step1Labels = labelEmbedding1 ∘ raw41710step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41710step1 raw41710step1Labels raw41710step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2282 node2282Labels := by rfl

theorem canonical41711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41711 raw41711Labels = mixedMoment B node4872 node4872Labels := by
  calc
    mixedMoment B raw41711 raw41711Labels = mixedMoment B raw41711step0 raw41711step0Labels := by
      have hz : ∀ j, raw41711 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41711step0 = (fun i j => raw41711 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41711step0 raw41711; decide +kernel
      have hl : raw41711step0Labels = raw41711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41711 raw41711Labels permutation434 hz
    mixedMoment B raw41711step0 raw41711step0Labels = mixedMoment B raw41711step1 raw41711step1Labels := by
      have hz : ∀ j, raw41711step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41711step1 = (fun i j => raw41711step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41711step1 raw41711step0; decide +kernel
      have hl : raw41711step1Labels = raw41711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41711step0 raw41711step0Labels permutation80 hz
    mixedMoment B raw41711step1 raw41711step1Labels = mixedMoment B raw41711step2 raw41711step2Labels := by
      have ha : raw41711step2 = (fun i j => raw41711step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41711step2 raw41711step1; decide +kernel
      have hl : raw41711step2Labels = raw41711step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41711step1 raw41711step1Labels permutation19 permutation6
    _ = mixedMoment B node4872 node4872Labels := by rfl

theorem canonical41712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41712 raw41712Labels = mixedMoment B node2163 node2163Labels := by
  calc
    mixedMoment B raw41712 raw41712Labels = mixedMoment B raw41712step0 raw41712step0Labels := by
      have hz : ∀ j, raw41712 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41712step0 = (fun i j => raw41712 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41712step0 raw41712; decide +kernel
      have hl : raw41712step0Labels = raw41712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41712 raw41712Labels permutation434 hz
    mixedMoment B raw41712step0 raw41712step0Labels = mixedMoment B raw41712step1 raw41712step1Labels := by
      have hz : ∀ j, raw41712step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41712step1 = (fun i j => raw41712step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41712step1 raw41712step0; decide +kernel
      have hl : raw41712step1Labels = raw41712step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41712step0 raw41712step0Labels permutation80 hz
    mixedMoment B raw41712step1 raw41712step1Labels = mixedMoment B raw41712step2 raw41712step2Labels := by
      have ha : raw41712step2 = (fun i j => raw41712step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41712step2 raw41712step1; decide +kernel
      have hl : raw41712step2Labels = raw41712step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41712step1 raw41712step1Labels permutation18 permutation4
    mixedMoment B raw41712step2 raw41712step2Labels = mixedMoment B raw41712step3 raw41712step3Labels := by
      have ha : raw41712step3 = -raw41712step2 := by apply Matrix.ext; change ∀ i j, raw41712step3 i j = -(raw41712step2 i j); unfold raw41712step3 raw41712step2; decide +kernel
      have hl : raw41712step3Labels = raw41712step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41712step3 raw41712step3Labels = mixedMoment B raw41712step4 raw41712step4Labels := by
      have ha : raw41712step4 = raw41712step3 := by apply Matrix.ext; unfold raw41712step4 raw41712step3; decide +kernel
      have hl : raw41712step3Labels = labelEmbedding1 ∘ raw41712step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41712step3 raw41712step3Labels raw41712step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2163 node2163Labels := by rfl

theorem canonical41713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41713 raw41713Labels = mixedMoment B node4694 node4694Labels := by
  calc
    mixedMoment B raw41713 raw41713Labels = mixedMoment B raw41713step0 raw41713step0Labels := by
      have hz : ∀ j, raw41713 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41713step0 = (fun i j => raw41713 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41713step0 raw41713; decide +kernel
      have hl : raw41713step0Labels = raw41713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41713 raw41713Labels permutation434 hz
    mixedMoment B raw41713step0 raw41713step0Labels = mixedMoment B raw41713step1 raw41713step1Labels := by
      have hz : ∀ j, raw41713step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41713step1 = (fun i j => raw41713step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41713step1 raw41713step0; decide +kernel
      have hl : raw41713step1Labels = raw41713step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41713step0 raw41713step0Labels permutation80 hz
    mixedMoment B raw41713step1 raw41713step1Labels = mixedMoment B raw41713step2 raw41713step2Labels := by
      have ha : raw41713step2 = (fun i j => raw41713step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41713step2 raw41713step1; decide +kernel
      have hl : raw41713step2Labels = raw41713step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41713step1 raw41713step1Labels permutation19 permutation6
    _ = mixedMoment B node4694 node4694Labels := by rfl

theorem canonical41714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41714 raw41714Labels = mixedMoment B node2221 node2221Labels := by
  calc
    mixedMoment B raw41714 raw41714Labels = mixedMoment B raw41714step0 raw41714step0Labels := by
      have hz : ∀ j, raw41714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41714step0 = (fun i j => raw41714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41714step0 raw41714; decide +kernel
      have hl : raw41714step0Labels = raw41714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41714 raw41714Labels permutation346 hz
    mixedMoment B raw41714step0 raw41714step0Labels = mixedMoment B raw41714step1 raw41714step1Labels := by
      have ha : raw41714step1 = (fun i j => raw41714step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41714step1 raw41714step0; decide +kernel
      have hl : raw41714step1Labels = raw41714step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41714step0 raw41714step0Labels permutation38 permutation2
    mixedMoment B raw41714step1 raw41714step1Labels = mixedMoment B raw41714step2 raw41714step2Labels := by
      have ha : raw41714step2 = raw41714step1 := by apply Matrix.ext; unfold raw41714step2 raw41714step1; decide +kernel
      have hl : raw41714step1Labels = labelEmbedding1 ∘ raw41714step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41714step1 raw41714step1Labels raw41714step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2221 node2221Labels := by rfl

theorem canonical41715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41715 raw41715Labels = mixedMoment B node4819 node4819Labels := by
  calc
    mixedMoment B raw41715 raw41715Labels = mixedMoment B raw41715step0 raw41715step0Labels := by
      have hz : ∀ j, raw41715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41715step0 = (fun i j => raw41715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41715step0 raw41715; decide +kernel
      have hl : raw41715step0Labels = raw41715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41715 raw41715Labels permutation346 hz
    mixedMoment B raw41715step0 raw41715step0Labels = mixedMoment B raw41715step1 raw41715step1Labels := by
      have ha : raw41715step1 = (fun i j => raw41715step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41715step1 raw41715step0; decide +kernel
      have hl : raw41715step1Labels = raw41715step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41715step0 raw41715step0Labels permutation73 permutation6
    _ = mixedMoment B node4819 node4819Labels := by rfl

theorem canonical41716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41716 raw41716Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw41716 raw41716Labels = mixedMoment B raw41716step0 raw41716step0Labels := by
      have hz : ∀ j, raw41716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41716step0 = (fun i j => raw41716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41716step0 raw41716; decide +kernel
      have hl : raw41716step0Labels = raw41716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41716 raw41716Labels permutation346 hz
    mixedMoment B raw41716step0 raw41716step0Labels = mixedMoment B raw41716step1 raw41716step1Labels := by
      have ha : raw41716step1 = (fun i j => raw41716step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41716step1 raw41716step0; decide +kernel
      have hl : raw41716step1Labels = raw41716step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41716step0 raw41716step0Labels permutation38 permutation2
    mixedMoment B raw41716step1 raw41716step1Labels = mixedMoment B raw41716step2 raw41716step2Labels := by
      have ha : raw41716step2 = raw41716step1 := by apply Matrix.ext; unfold raw41716step2 raw41716step1; decide +kernel
      have hl : raw41716step1Labels = labelEmbedding1 ∘ raw41716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41716step1 raw41716step1Labels raw41716step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

theorem canonical41717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41717 raw41717Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw41717 raw41717Labels = mixedMoment B raw41717step0 raw41717step0Labels := by
      have hz : ∀ j, raw41717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41717step0 = (fun i j => raw41717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41717step0 raw41717; decide +kernel
      have hl : raw41717step0Labels = raw41717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41717 raw41717Labels permutation346 hz
    mixedMoment B raw41717step0 raw41717step0Labels = mixedMoment B raw41717step1 raw41717step1Labels := by
      have ha : raw41717step1 = (fun i j => raw41717step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41717step1 raw41717step0; decide +kernel
      have hl : raw41717step1Labels = raw41717step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41717step0 raw41717step0Labels permutation41 permutation7
    mixedMoment B raw41717step1 raw41717step1Labels = mixedMoment B raw41717step2 raw41717step2Labels := by
      have ha : raw41717step2 = -raw41717step1 := by apply Matrix.ext; change ∀ i j, raw41717step2 i j = -(raw41717step1 i j); unfold raw41717step2 raw41717step1; decide +kernel
      have hl : raw41717step2Labels = raw41717step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41717step2 raw41717step2Labels = mixedMoment B raw41717step3 raw41717step3Labels := by
      have ha : raw41717step3 = raw41717step2 := by apply Matrix.ext; unfold raw41717step3 raw41717step2; decide +kernel
      have hl : raw41717step2Labels = labelEmbedding6 ∘ raw41717step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41717step2 raw41717step2Labels raw41717step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

theorem canonical41718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41718 raw41718Labels = mixedMoment B node2162 node2162Labels := by
  calc
    mixedMoment B raw41718 raw41718Labels = mixedMoment B raw41718step0 raw41718step0Labels := by
      have hz : ∀ j, raw41718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41718step0 = (fun i j => raw41718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41718step0 raw41718; decide +kernel
      have hl : raw41718step0Labels = raw41718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41718 raw41718Labels permutation346 hz
    mixedMoment B raw41718step0 raw41718step0Labels = mixedMoment B raw41718step1 raw41718step1Labels := by
      have ha : raw41718step1 = (fun i j => raw41718step0 (permutation74 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41718step1 raw41718step0; decide +kernel
      have hl : raw41718step1Labels = raw41718step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41718step0 raw41718step0Labels permutation74 permutation4
    mixedMoment B raw41718step1 raw41718step1Labels = mixedMoment B raw41718step2 raw41718step2Labels := by
      have ha : raw41718step2 = -raw41718step1 := by apply Matrix.ext; change ∀ i j, raw41718step2 i j = -(raw41718step1 i j); unfold raw41718step2 raw41718step1; decide +kernel
      have hl : raw41718step2Labels = raw41718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41718step2 raw41718step2Labels = mixedMoment B raw41718step3 raw41718step3Labels := by
      have ha : raw41718step3 = raw41718step2 := by apply Matrix.ext; unfold raw41718step3 raw41718step2; decide +kernel
      have hl : raw41718step2Labels = labelEmbedding1 ∘ raw41718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41718step2 raw41718step2Labels raw41718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2162 node2162Labels := by rfl

theorem canonical41719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41719 raw41719Labels = mixedMoment B node4687 node4687Labels := by
  calc
    mixedMoment B raw41719 raw41719Labels = mixedMoment B raw41719step0 raw41719step0Labels := by
      have hz : ∀ j, raw41719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41719step0 = (fun i j => raw41719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41719step0 raw41719; decide +kernel
      have hl : raw41719step0Labels = raw41719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41719 raw41719Labels permutation346 hz
    mixedMoment B raw41719step0 raw41719step0Labels = mixedMoment B raw41719step1 raw41719step1Labels := by
      have ha : raw41719step1 = (fun i j => raw41719step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41719step1 raw41719step0; decide +kernel
      have hl : raw41719step1Labels = raw41719step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41719step0 raw41719step0Labels permutation77 permutation6
    _ = mixedMoment B node4687 node4687Labels := by rfl

theorem canonical41720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41720 raw41720Labels = mixedMoment B node2161 node2161Labels := by
  calc
    mixedMoment B raw41720 raw41720Labels = mixedMoment B raw41720step0 raw41720step0Labels := by
      have hz : ∀ j, raw41720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41720step0 = (fun i j => raw41720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41720step0 raw41720; decide +kernel
      have hl : raw41720step0Labels = raw41720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41720 raw41720Labels permutation346 hz
    mixedMoment B raw41720step0 raw41720step0Labels = mixedMoment B raw41720step1 raw41720step1Labels := by
      have ha : raw41720step1 = (fun i j => raw41720step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41720step1 raw41720step0; decide +kernel
      have hl : raw41720step1Labels = raw41720step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41720step0 raw41720step0Labels permutation38 permutation2
    mixedMoment B raw41720step1 raw41720step1Labels = mixedMoment B raw41720step2 raw41720step2Labels := by
      have ha : raw41720step2 = raw41720step1 := by apply Matrix.ext; unfold raw41720step2 raw41720step1; decide +kernel
      have hl : raw41720step1Labels = labelEmbedding1 ∘ raw41720step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41720step1 raw41720step1Labels raw41720step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2161 node2161Labels := by rfl

theorem canonical41721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41721 raw41721Labels = mixedMoment B node4671 node4671Labels := by
  calc
    mixedMoment B raw41721 raw41721Labels = mixedMoment B raw41721step0 raw41721step0Labels := by
      have hz : ∀ j, raw41721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41721step0 = (fun i j => raw41721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41721step0 raw41721; decide +kernel
      have hl : raw41721step0Labels = raw41721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41721 raw41721Labels permutation346 hz
    mixedMoment B raw41721step0 raw41721step0Labels = mixedMoment B raw41721step1 raw41721step1Labels := by
      have ha : raw41721step1 = (fun i j => raw41721step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41721step1 raw41721step0; decide +kernel
      have hl : raw41721step1Labels = raw41721step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41721step0 raw41721step0Labels permutation79 permutation6
    _ = mixedMoment B node4671 node4671Labels := by rfl

theorem canonical41722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41722 raw41722Labels = mixedMoment B node2180 node2180Labels := by
  calc
    mixedMoment B raw41722 raw41722Labels = mixedMoment B raw41722step0 raw41722step0Labels := by
      have hz : ∀ j, raw41722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41722step0 = (fun i j => raw41722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41722step0 raw41722; decide +kernel
      have hl : raw41722step0Labels = raw41722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41722 raw41722Labels permutation346 hz
    mixedMoment B raw41722step0 raw41722step0Labels = mixedMoment B raw41722step1 raw41722step1Labels := by
      have ha : raw41722step1 = (fun i j => raw41722step0 (permutation64 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41722step1 raw41722step0; decide +kernel
      have hl : raw41722step1Labels = raw41722step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41722step0 raw41722step0Labels permutation64 permutation4
    mixedMoment B raw41722step1 raw41722step1Labels = mixedMoment B raw41722step2 raw41722step2Labels := by
      have ha : raw41722step2 = -raw41722step1 := by apply Matrix.ext; change ∀ i j, raw41722step2 i j = -(raw41722step1 i j); unfold raw41722step2 raw41722step1; decide +kernel
      have hl : raw41722step2Labels = raw41722step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41722step2 raw41722step2Labels = mixedMoment B raw41722step3 raw41722step3Labels := by
      have ha : raw41722step3 = raw41722step2 := by apply Matrix.ext; unfold raw41722step3 raw41722step2; decide +kernel
      have hl : raw41722step2Labels = labelEmbedding1 ∘ raw41722step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41722step2 raw41722step2Labels raw41722step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2180 node2180Labels := by rfl

theorem canonical41723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41723 raw41723Labels = mixedMoment B node4702 node4702Labels := by
  calc
    mixedMoment B raw41723 raw41723Labels = mixedMoment B raw41723step0 raw41723step0Labels := by
      have hz : ∀ j, raw41723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41723step0 = (fun i j => raw41723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41723step0 raw41723; decide +kernel
      have hl : raw41723step0Labels = raw41723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41723 raw41723Labels permutation346 hz
    mixedMoment B raw41723step0 raw41723step0Labels = mixedMoment B raw41723step1 raw41723step1Labels := by
      have ha : raw41723step1 = (fun i j => raw41723step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41723step1 raw41723step0; decide +kernel
      have hl : raw41723step1Labels = raw41723step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41723step0 raw41723step0Labels permutation53 permutation7
    mixedMoment B raw41723step1 raw41723step1Labels = mixedMoment B raw41723step2 raw41723step2Labels := by
      have ha : raw41723step2 = -raw41723step1 := by apply Matrix.ext; change ∀ i j, raw41723step2 i j = -(raw41723step1 i j); unfold raw41723step2 raw41723step1; decide +kernel
      have hl : raw41723step2Labels = raw41723step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41723step2 raw41723step2Labels = mixedMoment B raw41723step3 raw41723step3Labels := by
      have ha : raw41723step3 = raw41723step2 := by apply Matrix.ext; unfold raw41723step3 raw41723step2; decide +kernel
      have hl : raw41723step2Labels = labelEmbedding6 ∘ raw41723step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41723step2 raw41723step2Labels raw41723step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4702 node4702Labels := by rfl

theorem canonical41724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41724 raw41724Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw41724 raw41724Labels = mixedMoment B raw41724step0 raw41724step0Labels := by
      have hz : ∀ j, raw41724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41724step0 = (fun i j => raw41724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41724step0 raw41724; decide +kernel
      have hl : raw41724step0Labels = raw41724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41724 raw41724Labels permutation346 hz
    mixedMoment B raw41724step0 raw41724step0Labels = mixedMoment B raw41724step1 raw41724step1Labels := by
      have ha : raw41724step1 = (fun i j => raw41724step0 (permutation62 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41724step1 raw41724step0; decide +kernel
      have hl : raw41724step1Labels = raw41724step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41724step0 raw41724step0Labels permutation62 permutation4
    mixedMoment B raw41724step1 raw41724step1Labels = mixedMoment B raw41724step2 raw41724step2Labels := by
      have ha : raw41724step2 = -raw41724step1 := by apply Matrix.ext; change ∀ i j, raw41724step2 i j = -(raw41724step1 i j); unfold raw41724step2 raw41724step1; decide +kernel
      have hl : raw41724step2Labels = raw41724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41724step2 raw41724step2Labels = mixedMoment B raw41724step3 raw41724step3Labels := by
      have ha : raw41724step3 = raw41724step2 := by apply Matrix.ext; unfold raw41724step3 raw41724step2; decide +kernel
      have hl : raw41724step2Labels = labelEmbedding1 ∘ raw41724step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41724step2 raw41724step2Labels raw41724step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

theorem canonical41725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41725 raw41725Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw41725 raw41725Labels = mixedMoment B raw41725step0 raw41725step0Labels := by
      have hz : ∀ j, raw41725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41725step0 = (fun i j => raw41725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41725step0 raw41725; decide +kernel
      have hl : raw41725step0Labels = raw41725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41725 raw41725Labels permutation346 hz
    mixedMoment B raw41725step0 raw41725step0Labels = mixedMoment B raw41725step1 raw41725step1Labels := by
      have ha : raw41725step1 = (fun i j => raw41725step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41725step1 raw41725step0; decide +kernel
      have hl : raw41725step1Labels = raw41725step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41725step0 raw41725step0Labels permutation65 permutation6
    _ = mixedMoment B node4808 node4808Labels := by rfl

theorem canonical41726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41726 raw41726Labels = mixedMoment B node2283 node2283Labels := by
  calc
    mixedMoment B raw41726 raw41726Labels = mixedMoment B raw41726step0 raw41726step0Labels := by
      have hz : ∀ j, raw41726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41726step0 = (fun i j => raw41726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41726step0 raw41726; decide +kernel
      have hl : raw41726step0Labels = raw41726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41726 raw41726Labels permutation346 hz
    mixedMoment B raw41726step0 raw41726step0Labels = mixedMoment B raw41726step1 raw41726step1Labels := by
      have ha : raw41726step1 = raw41726step0 := by apply Matrix.ext; unfold raw41726step1 raw41726step0; decide +kernel
      have hl : raw41726step0Labels = labelEmbedding1 ∘ raw41726step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41726step0 raw41726step0Labels raw41726step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2283 node2283Labels := by rfl

theorem canonical41727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41727 raw41727Labels = mixedMoment B node4886 node4886Labels := by
  calc
    mixedMoment B raw41727 raw41727Labels = mixedMoment B raw41727step0 raw41727step0Labels := by
      have hz : ∀ j, raw41727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41727step0 = (fun i j => raw41727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41727step0 raw41727; decide +kernel
      have hl : raw41727step0Labels = raw41727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41727 raw41727Labels permutation346 hz
    mixedMoment B raw41727step0 raw41727step0Labels = mixedMoment B raw41727step1 raw41727step1Labels := by
      have ha : raw41727step1 = (fun i j => raw41727step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41727step1 raw41727step0; decide +kernel
      have hl : raw41727step1Labels = raw41727step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41727step0 raw41727step0Labels permutation65 permutation6
    _ = mixedMoment B node4886 node4886Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2176) =
      Integer.Sparse.eval keyMomentRow2176 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2176).leftCharge (GramAssembly.key 2176).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2670) := by
    have ha : gramCharges (GramAssembly.key 2176).leftCharge (GramAssembly.key 2176).rightCharge = raw41664 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41664Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41664 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2176).leftCharge (GramAssembly.key 2176).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5140) := by
    have ha : gramCharges (GramAssembly.key 2176).leftCharge (GramAssembly.key 2176).rightCharge = raw41665 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41665Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41665 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2176).leftCharge (GramAssembly.key 2176).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2176).leftCharge (GramAssembly.key 2176).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2176, Integer.Sparse.eval]
  ring

theorem keyMoment2177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2177) =
      Integer.Sparse.eval keyMomentRow2177 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2177).leftCharge (GramAssembly.key 2177).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2760) := by
    have ha : gramCharges (GramAssembly.key 2177).leftCharge (GramAssembly.key 2177).rightCharge = raw41666 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41666Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41666 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2177).leftCharge (GramAssembly.key 2177).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5288) := by
    have ha : gramCharges (GramAssembly.key 2177).leftCharge (GramAssembly.key 2177).rightCharge = raw41667 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41667Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41667 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2177).leftCharge (GramAssembly.key 2177).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2177).leftCharge (GramAssembly.key 2177).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2177, Integer.Sparse.eval]
  ring

theorem keyMoment2178 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2178) =
      Integer.Sparse.eval keyMomentRow2178 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2178).leftCharge (GramAssembly.key 2178).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2763) := by
    have ha : gramCharges (GramAssembly.key 2178).leftCharge (GramAssembly.key 2178).rightCharge = raw41668 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41668Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41668 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2178).leftCharge (GramAssembly.key 2178).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5289) := by
    have ha : gramCharges (GramAssembly.key 2178).leftCharge (GramAssembly.key 2178).rightCharge = raw41669 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41669Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41669 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2178).leftCharge (GramAssembly.key 2178).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2178).leftCharge (GramAssembly.key 2178).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2178, Integer.Sparse.eval]
  ring

theorem keyMoment2179 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2179) =
      Integer.Sparse.eval keyMomentRow2179 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2179).leftCharge (GramAssembly.key 2179).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2718) := by
    have ha : gramCharges (GramAssembly.key 2179).leftCharge (GramAssembly.key 2179).rightCharge = raw41670 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41670Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41670 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2179).leftCharge (GramAssembly.key 2179).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5255) := by
    have ha : gramCharges (GramAssembly.key 2179).leftCharge (GramAssembly.key 2179).rightCharge = raw41671 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41671Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41671 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2179).leftCharge (GramAssembly.key 2179).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2179).leftCharge (GramAssembly.key 2179).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2179, Integer.Sparse.eval]
  ring

theorem keyMoment2180 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2180) =
      Integer.Sparse.eval keyMomentRow2180 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2180).leftCharge (GramAssembly.key 2180).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2669) := by
    have ha : gramCharges (GramAssembly.key 2180).leftCharge (GramAssembly.key 2180).rightCharge = raw41672 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41672Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41672 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2180).leftCharge (GramAssembly.key 2180).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5226) := by
    have ha : gramCharges (GramAssembly.key 2180).leftCharge (GramAssembly.key 2180).rightCharge = raw41673 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41673Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41673 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2180).leftCharge (GramAssembly.key 2180).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2180).leftCharge (GramAssembly.key 2180).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2180, Integer.Sparse.eval]
  ring

theorem keyMoment2181 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2181) =
      Integer.Sparse.eval keyMomentRow2181 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2181).leftCharge (GramAssembly.key 2181).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2789) := by
    have ha : gramCharges (GramAssembly.key 2181).leftCharge (GramAssembly.key 2181).rightCharge = raw41674 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41674Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41674 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2181).leftCharge (GramAssembly.key 2181).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5311) := by
    have ha : gramCharges (GramAssembly.key 2181).leftCharge (GramAssembly.key 2181).rightCharge = raw41675 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41675Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41675 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2181).leftCharge (GramAssembly.key 2181).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2181).leftCharge (GramAssembly.key 2181).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2181, Integer.Sparse.eval]
  ring

theorem keyMoment2182 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2182) =
      Integer.Sparse.eval keyMomentRow2182 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2182).leftCharge (GramAssembly.key 2182).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2780) := by
    have ha : gramCharges (GramAssembly.key 2182).leftCharge (GramAssembly.key 2182).rightCharge = raw41676 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41676Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41676 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2182).leftCharge (GramAssembly.key 2182).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4626) := by
    have ha : gramCharges (GramAssembly.key 2182).leftCharge (GramAssembly.key 2182).rightCharge = raw41677 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41677Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41677 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2182).leftCharge (GramAssembly.key 2182).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2182).leftCharge (GramAssembly.key 2182).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2182, Integer.Sparse.eval]
  ring

theorem keyMoment2183 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2183) =
      Integer.Sparse.eval keyMomentRow2183 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2183).leftCharge (GramAssembly.key 2183).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2744) := by
    have ha : gramCharges (GramAssembly.key 2183).leftCharge (GramAssembly.key 2183).rightCharge = raw41678 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41678Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41678 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2183).leftCharge (GramAssembly.key 2183).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5276) := by
    have ha : gramCharges (GramAssembly.key 2183).leftCharge (GramAssembly.key 2183).rightCharge = raw41679 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41679Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41679 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2183).leftCharge (GramAssembly.key 2183).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2183).leftCharge (GramAssembly.key 2183).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2183, Integer.Sparse.eval]
  ring

theorem keyMoment2184 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2184) =
      Integer.Sparse.eval keyMomentRow2184 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2184).leftCharge (GramAssembly.key 2184).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2737) := by
    have ha : gramCharges (GramAssembly.key 2184).leftCharge (GramAssembly.key 2184).rightCharge = raw41680 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41680Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41680 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2184).leftCharge (GramAssembly.key 2184).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4617) := by
    have ha : gramCharges (GramAssembly.key 2184).leftCharge (GramAssembly.key 2184).rightCharge = raw41681 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41681Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41681 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2184).leftCharge (GramAssembly.key 2184).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2184).leftCharge (GramAssembly.key 2184).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2184, Integer.Sparse.eval]
  ring

theorem keyMoment2185 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2185) =
      Integer.Sparse.eval keyMomentRow2185 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2185).leftCharge (GramAssembly.key 2185).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2683) := by
    have ha : gramCharges (GramAssembly.key 2185).leftCharge (GramAssembly.key 2185).rightCharge = raw41682 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41682Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41682 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2185).leftCharge (GramAssembly.key 2185).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4611) := by
    have ha : gramCharges (GramAssembly.key 2185).leftCharge (GramAssembly.key 2185).rightCharge = raw41683 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41683Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41683 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2185).leftCharge (GramAssembly.key 2185).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2185).leftCharge (GramAssembly.key 2185).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2185, Integer.Sparse.eval]
  ring

theorem keyMoment2186 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2186) =
      Integer.Sparse.eval keyMomentRow2186 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2186).leftCharge (GramAssembly.key 2186).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2761) := by
    have ha : gramCharges (GramAssembly.key 2186).leftCharge (GramAssembly.key 2186).rightCharge = raw41684 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41684Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41684 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2186).leftCharge (GramAssembly.key 2186).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5175) := by
    have ha : gramCharges (GramAssembly.key 2186).leftCharge (GramAssembly.key 2186).rightCharge = raw41685 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41685Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41685 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2186).leftCharge (GramAssembly.key 2186).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2186).leftCharge (GramAssembly.key 2186).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2186, Integer.Sparse.eval]
  ring

theorem keyMoment2187 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2187) =
      Integer.Sparse.eval keyMomentRow2187 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2187).leftCharge (GramAssembly.key 2187).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2781) := by
    have ha : gramCharges (GramAssembly.key 2187).leftCharge (GramAssembly.key 2187).rightCharge = raw41686 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41686Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41686 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2187).leftCharge (GramAssembly.key 2187).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5295) := by
    have ha : gramCharges (GramAssembly.key 2187).leftCharge (GramAssembly.key 2187).rightCharge = raw41687 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41687Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41687 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2187).leftCharge (GramAssembly.key 2187).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2187).leftCharge (GramAssembly.key 2187).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2187, Integer.Sparse.eval]
  ring

theorem keyMoment2188 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2188) =
      Integer.Sparse.eval keyMomentRow2188 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2188).leftCharge (GramAssembly.key 2188).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2779) := by
    have ha : gramCharges (GramAssembly.key 2188).leftCharge (GramAssembly.key 2188).rightCharge = raw41688 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41688Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41688 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2188).leftCharge (GramAssembly.key 2188).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5303) := by
    have ha : gramCharges (GramAssembly.key 2188).leftCharge (GramAssembly.key 2188).rightCharge = raw41689 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41689Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41689 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2188).leftCharge (GramAssembly.key 2188).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2188).leftCharge (GramAssembly.key 2188).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2188, Integer.Sparse.eval]
  ring

theorem keyMoment2189 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2189) =
      Integer.Sparse.eval keyMomentRow2189 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2189).leftCharge (GramAssembly.key 2189).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2702) := by
    have ha : gramCharges (GramAssembly.key 2189).leftCharge (GramAssembly.key 2189).rightCharge = raw41690 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41690Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41690 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2189).leftCharge (GramAssembly.key 2189).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4600) := by
    have ha : gramCharges (GramAssembly.key 2189).leftCharge (GramAssembly.key 2189).rightCharge = raw41691 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41691Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41691 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2189).leftCharge (GramAssembly.key 2189).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2189).leftCharge (GramAssembly.key 2189).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2189, Integer.Sparse.eval]
  ring

theorem keyMoment2190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2190) =
      Integer.Sparse.eval keyMomentRow2190 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2190).leftCharge (GramAssembly.key 2190).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2735) := by
    have ha : gramCharges (GramAssembly.key 2190).leftCharge (GramAssembly.key 2190).rightCharge = raw41692 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41692Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41692 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2190).leftCharge (GramAssembly.key 2190).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5173) := by
    have ha : gramCharges (GramAssembly.key 2190).leftCharge (GramAssembly.key 2190).rightCharge = raw41693 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41693Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41693 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2190).leftCharge (GramAssembly.key 2190).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2190).leftCharge (GramAssembly.key 2190).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2190, Integer.Sparse.eval]
  ring

theorem keyMoment2191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2191) =
      Integer.Sparse.eval keyMomentRow2191 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2191).leftCharge (GramAssembly.key 2191).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2738) := by
    have ha : gramCharges (GramAssembly.key 2191).leftCharge (GramAssembly.key 2191).rightCharge = raw41694 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41694Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41694 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2191).leftCharge (GramAssembly.key 2191).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5270) := by
    have ha : gramCharges (GramAssembly.key 2191).leftCharge (GramAssembly.key 2191).rightCharge = raw41695 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41695Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41695 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2191).leftCharge (GramAssembly.key 2191).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2191).leftCharge (GramAssembly.key 2191).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2191, Integer.Sparse.eval]
  ring

theorem keyMoment2192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2192) =
      Integer.Sparse.eval keyMomentRow2192 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2192).leftCharge (GramAssembly.key 2192).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2736) := by
    have ha : gramCharges (GramAssembly.key 2192).leftCharge (GramAssembly.key 2192).rightCharge = raw41696 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41696Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41696 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2192).leftCharge (GramAssembly.key 2192).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5269) := by
    have ha : gramCharges (GramAssembly.key 2192).leftCharge (GramAssembly.key 2192).rightCharge = raw41697 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41697Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41697 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2192).leftCharge (GramAssembly.key 2192).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2192).leftCharge (GramAssembly.key 2192).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2192, Integer.Sparse.eval]
  ring

theorem keyMoment2193 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2193) =
      Integer.Sparse.eval keyMomentRow2193 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2193).leftCharge (GramAssembly.key 2193).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2681) := by
    have ha : gramCharges (GramAssembly.key 2193).leftCharge (GramAssembly.key 2193).rightCharge = raw41698 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41698Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41698 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2193).leftCharge (GramAssembly.key 2193).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5151) := by
    have ha : gramCharges (GramAssembly.key 2193).leftCharge (GramAssembly.key 2193).rightCharge = raw41699 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41699Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41699 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2193).leftCharge (GramAssembly.key 2193).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2193).leftCharge (GramAssembly.key 2193).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2193, Integer.Sparse.eval]
  ring

theorem keyMoment2194 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2194) =
      Integer.Sparse.eval keyMomentRow2194 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2194).leftCharge (GramAssembly.key 2194).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2682) := by
    have ha : gramCharges (GramAssembly.key 2194).leftCharge (GramAssembly.key 2194).rightCharge = raw41700 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41700Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41700 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2194).leftCharge (GramAssembly.key 2194).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5236) := by
    have ha : gramCharges (GramAssembly.key 2194).leftCharge (GramAssembly.key 2194).rightCharge = raw41701 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41701Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41701 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2194).leftCharge (GramAssembly.key 2194).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2194).leftCharge (GramAssembly.key 2194).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2194, Integer.Sparse.eval]
  ring

theorem keyMoment2195 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2195) =
      Integer.Sparse.eval keyMomentRow2195 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2195).leftCharge (GramAssembly.key 2195).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2700) := by
    have ha : gramCharges (GramAssembly.key 2195).leftCharge (GramAssembly.key 2195).rightCharge = raw41702 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41702Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41702 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2195).leftCharge (GramAssembly.key 2195).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5150) := by
    have ha : gramCharges (GramAssembly.key 2195).leftCharge (GramAssembly.key 2195).rightCharge = raw41703 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41703Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41703 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2195).leftCharge (GramAssembly.key 2195).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2195).leftCharge (GramAssembly.key 2195).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2195, Integer.Sparse.eval]
  ring

theorem keyMoment2196 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2196) =
      Integer.Sparse.eval keyMomentRow2196 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2196).leftCharge (GramAssembly.key 2196).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2285) := by
    have ha : gramCharges (GramAssembly.key 2196).leftCharge (GramAssembly.key 2196).rightCharge = raw41704 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41704Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41704 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2196).leftCharge (GramAssembly.key 2196).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4900) := by
    have ha : gramCharges (GramAssembly.key 2196).leftCharge (GramAssembly.key 2196).rightCharge = raw41705 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41705Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41705 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2196).leftCharge (GramAssembly.key 2196).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2196).leftCharge (GramAssembly.key 2196).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2196, Integer.Sparse.eval]
  ring

theorem keyMoment2197 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2197) =
      Integer.Sparse.eval keyMomentRow2197 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2197).leftCharge (GramAssembly.key 2197).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2222) := by
    have ha : gramCharges (GramAssembly.key 2197).leftCharge (GramAssembly.key 2197).rightCharge = raw41706 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41706Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41706 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2197).leftCharge (GramAssembly.key 2197).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4844) := by
    have ha : gramCharges (GramAssembly.key 2197).leftCharge (GramAssembly.key 2197).rightCharge = raw41707 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41707Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41707 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2197).leftCharge (GramAssembly.key 2197).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2197).leftCharge (GramAssembly.key 2197).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2197, Integer.Sparse.eval]
  ring

theorem keyMoment2198 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2198) =
      Integer.Sparse.eval keyMomentRow2198 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2198).leftCharge (GramAssembly.key 2198).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2284) := by
    have ha : gramCharges (GramAssembly.key 2198).leftCharge (GramAssembly.key 2198).rightCharge = raw41708 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41708Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41708 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2198).leftCharge (GramAssembly.key 2198).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4892) := by
    have ha : gramCharges (GramAssembly.key 2198).leftCharge (GramAssembly.key 2198).rightCharge = raw41709 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41709Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41709 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2198).leftCharge (GramAssembly.key 2198).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2198).leftCharge (GramAssembly.key 2198).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2198, Integer.Sparse.eval]
  ring

theorem keyMoment2199 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2199) =
      Integer.Sparse.eval keyMomentRow2199 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2199).leftCharge (GramAssembly.key 2199).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2282) := by
    have ha : gramCharges (GramAssembly.key 2199).leftCharge (GramAssembly.key 2199).rightCharge = raw41710 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41710Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41710 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2199).leftCharge (GramAssembly.key 2199).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4872) := by
    have ha : gramCharges (GramAssembly.key 2199).leftCharge (GramAssembly.key 2199).rightCharge = raw41711 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41711Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41711 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2199).leftCharge (GramAssembly.key 2199).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2199).leftCharge (GramAssembly.key 2199).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2199, Integer.Sparse.eval]
  ring

theorem keyMoment2200 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2200) =
      Integer.Sparse.eval keyMomentRow2200 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2200).leftCharge (GramAssembly.key 2200).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2163) := by
    have ha : gramCharges (GramAssembly.key 2200).leftCharge (GramAssembly.key 2200).rightCharge = raw41712 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41712Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41712 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2200).leftCharge (GramAssembly.key 2200).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4694) := by
    have ha : gramCharges (GramAssembly.key 2200).leftCharge (GramAssembly.key 2200).rightCharge = raw41713 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41713Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41713 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2200).leftCharge (GramAssembly.key 2200).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2200).leftCharge (GramAssembly.key 2200).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2200, Integer.Sparse.eval]
  ring

theorem keyMoment2201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2201) =
      Integer.Sparse.eval keyMomentRow2201 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2201).leftCharge (GramAssembly.key 2201).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2221) := by
    have ha : gramCharges (GramAssembly.key 2201).leftCharge (GramAssembly.key 2201).rightCharge = raw41714 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41714Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41714 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2201).leftCharge (GramAssembly.key 2201).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4819) := by
    have ha : gramCharges (GramAssembly.key 2201).leftCharge (GramAssembly.key 2201).rightCharge = raw41715 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41715Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41715 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2201).leftCharge (GramAssembly.key 2201).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2201).leftCharge (GramAssembly.key 2201).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2201, Integer.Sparse.eval]
  ring

theorem keyMoment2202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2202) =
      Integer.Sparse.eval keyMomentRow2202 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2202).leftCharge (GramAssembly.key 2202).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2220) := by
    have ha : gramCharges (GramAssembly.key 2202).leftCharge (GramAssembly.key 2202).rightCharge = raw41716 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41716Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41716 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2202).leftCharge (GramAssembly.key 2202).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4808) := by
    have ha : gramCharges (GramAssembly.key 2202).leftCharge (GramAssembly.key 2202).rightCharge = raw41717 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41717Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41717 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2202).leftCharge (GramAssembly.key 2202).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2202).leftCharge (GramAssembly.key 2202).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2202, Integer.Sparse.eval]
  ring

theorem keyMoment2203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2203) =
      Integer.Sparse.eval keyMomentRow2203 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2203).leftCharge (GramAssembly.key 2203).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2162) := by
    have ha : gramCharges (GramAssembly.key 2203).leftCharge (GramAssembly.key 2203).rightCharge = raw41718 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41718Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41718 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2203).leftCharge (GramAssembly.key 2203).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4687) := by
    have ha : gramCharges (GramAssembly.key 2203).leftCharge (GramAssembly.key 2203).rightCharge = raw41719 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41719Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41719 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2203).leftCharge (GramAssembly.key 2203).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2203).leftCharge (GramAssembly.key 2203).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2203, Integer.Sparse.eval]
  ring

theorem keyMoment2204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2204) =
      Integer.Sparse.eval keyMomentRow2204 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2204).leftCharge (GramAssembly.key 2204).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2161) := by
    have ha : gramCharges (GramAssembly.key 2204).leftCharge (GramAssembly.key 2204).rightCharge = raw41720 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41720Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41720 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2204).leftCharge (GramAssembly.key 2204).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4671) := by
    have ha : gramCharges (GramAssembly.key 2204).leftCharge (GramAssembly.key 2204).rightCharge = raw41721 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41721Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41721 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2204).leftCharge (GramAssembly.key 2204).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2204).leftCharge (GramAssembly.key 2204).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2204, Integer.Sparse.eval]
  ring

theorem keyMoment2205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2205) =
      Integer.Sparse.eval keyMomentRow2205 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2205).leftCharge (GramAssembly.key 2205).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2180) := by
    have ha : gramCharges (GramAssembly.key 2205).leftCharge (GramAssembly.key 2205).rightCharge = raw41722 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41722Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41722 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2205).leftCharge (GramAssembly.key 2205).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4702) := by
    have ha : gramCharges (GramAssembly.key 2205).leftCharge (GramAssembly.key 2205).rightCharge = raw41723 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41723Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41723 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2205).leftCharge (GramAssembly.key 2205).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2205).leftCharge (GramAssembly.key 2205).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2205, Integer.Sparse.eval]
  ring

theorem keyMoment2206 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2206) =
      Integer.Sparse.eval keyMomentRow2206 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2206).leftCharge (GramAssembly.key 2206).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2220) := by
    have ha : gramCharges (GramAssembly.key 2206).leftCharge (GramAssembly.key 2206).rightCharge = raw41724 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41724Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41724 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2206).leftCharge (GramAssembly.key 2206).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4808) := by
    have ha : gramCharges (GramAssembly.key 2206).leftCharge (GramAssembly.key 2206).rightCharge = raw41725 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41725Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41725 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2206).leftCharge (GramAssembly.key 2206).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2206).leftCharge (GramAssembly.key 2206).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2206, Integer.Sparse.eval]
  ring

theorem keyMoment2207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2207) =
      Integer.Sparse.eval keyMomentRow2207 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2207).leftCharge (GramAssembly.key 2207).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2283) := by
    have ha : gramCharges (GramAssembly.key 2207).leftCharge (GramAssembly.key 2207).rightCharge = raw41726 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41726Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41726 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2207).leftCharge (GramAssembly.key 2207).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4886) := by
    have ha : gramCharges (GramAssembly.key 2207).leftCharge (GramAssembly.key 2207).rightCharge = raw41727 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41727Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41727 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2207).leftCharge (GramAssembly.key 2207).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2207).leftCharge (GramAssembly.key 2207).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2207, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2176 : keyMomentRows (2176 : Fin 2886) =
    keyMomentRow2176 := by decide +kernel

theorem keyMomentRowsAt2177 : keyMomentRows (2177 : Fin 2886) =
    keyMomentRow2177 := by decide +kernel

theorem keyMomentRowsAt2178 : keyMomentRows (2178 : Fin 2886) =
    keyMomentRow2178 := by decide +kernel

theorem keyMomentRowsAt2179 : keyMomentRows (2179 : Fin 2886) =
    keyMomentRow2179 := by decide +kernel

theorem keyMomentRowsAt2180 : keyMomentRows (2180 : Fin 2886) =
    keyMomentRow2180 := by decide +kernel

theorem keyMomentRowsAt2181 : keyMomentRows (2181 : Fin 2886) =
    keyMomentRow2181 := by decide +kernel

theorem keyMomentRowsAt2182 : keyMomentRows (2182 : Fin 2886) =
    keyMomentRow2182 := by decide +kernel

theorem keyMomentRowsAt2183 : keyMomentRows (2183 : Fin 2886) =
    keyMomentRow2183 := by decide +kernel

theorem keyMomentRowsAt2184 : keyMomentRows (2184 : Fin 2886) =
    keyMomentRow2184 := by decide +kernel

theorem keyMomentRowsAt2185 : keyMomentRows (2185 : Fin 2886) =
    keyMomentRow2185 := by decide +kernel

theorem keyMomentRowsAt2186 : keyMomentRows (2186 : Fin 2886) =
    keyMomentRow2186 := by decide +kernel

theorem keyMomentRowsAt2187 : keyMomentRows (2187 : Fin 2886) =
    keyMomentRow2187 := by decide +kernel

theorem keyMomentRowsAt2188 : keyMomentRows (2188 : Fin 2886) =
    keyMomentRow2188 := by decide +kernel

theorem keyMomentRowsAt2189 : keyMomentRows (2189 : Fin 2886) =
    keyMomentRow2189 := by decide +kernel

theorem keyMomentRowsAt2190 : keyMomentRows (2190 : Fin 2886) =
    keyMomentRow2190 := by decide +kernel

theorem keyMomentRowsAt2191 : keyMomentRows (2191 : Fin 2886) =
    keyMomentRow2191 := by decide +kernel

theorem keyMomentRowsAt2192 : keyMomentRows (2192 : Fin 2886) =
    keyMomentRow2192 := by decide +kernel

theorem keyMomentRowsAt2193 : keyMomentRows (2193 : Fin 2886) =
    keyMomentRow2193 := by decide +kernel

theorem keyMomentRowsAt2194 : keyMomentRows (2194 : Fin 2886) =
    keyMomentRow2194 := by decide +kernel

theorem keyMomentRowsAt2195 : keyMomentRows (2195 : Fin 2886) =
    keyMomentRow2195 := by decide +kernel

theorem keyMomentRowsAt2196 : keyMomentRows (2196 : Fin 2886) =
    keyMomentRow2196 := by decide +kernel

theorem keyMomentRowsAt2197 : keyMomentRows (2197 : Fin 2886) =
    keyMomentRow2197 := by decide +kernel

theorem keyMomentRowsAt2198 : keyMomentRows (2198 : Fin 2886) =
    keyMomentRow2198 := by decide +kernel

theorem keyMomentRowsAt2199 : keyMomentRows (2199 : Fin 2886) =
    keyMomentRow2199 := by decide +kernel

theorem keyMomentRowsAt2200 : keyMomentRows (2200 : Fin 2886) =
    keyMomentRow2200 := by decide +kernel

theorem keyMomentRowsAt2201 : keyMomentRows (2201 : Fin 2886) =
    keyMomentRow2201 := by decide +kernel

theorem keyMomentRowsAt2202 : keyMomentRows (2202 : Fin 2886) =
    keyMomentRow2202 := by decide +kernel

theorem keyMomentRowsAt2203 : keyMomentRows (2203 : Fin 2886) =
    keyMomentRow2203 := by decide +kernel

theorem keyMomentRowsAt2204 : keyMomentRows (2204 : Fin 2886) =
    keyMomentRow2204 := by decide +kernel

theorem keyMomentRowsAt2205 : keyMomentRows (2205 : Fin 2886) =
    keyMomentRow2205 := by decide +kernel

theorem keyMomentRowsAt2206 : keyMomentRows (2206 : Fin 2886) =
    keyMomentRow2206 := by decide +kernel

theorem keyMomentRowsAt2207 : keyMomentRows (2207 : Fin 2886) =
    keyMomentRow2207 := by decide +kernel

theorem keyMomentChunkSound68_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 68) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2176 ∨ k.val = 2177 ∨ k.val = 2178 ∨ k.val = 2179 ∨ k.val = 2180 ∨ k.val = 2181 ∨ k.val = 2182 ∨ k.val = 2183 ∨ k.val = 2184 ∨ k.val = 2185 ∨ k.val = 2186 ∨ k.val = 2187 ∨ k.val = 2188 ∨ k.val = 2189 ∨ k.val = 2190 ∨ k.val = 2191 ∨ k.val = 2192 ∨ k.val = 2193 ∨ k.val = 2194 ∨ k.val = 2195 ∨ k.val = 2196 ∨ k.val = 2197 ∨ k.val = 2198 ∨ k.val = 2199 ∨ k.val = 2200 ∨ k.val = 2201 ∨ k.val = 2202 ∨ k.val = 2203 ∨ k.val = 2204 ∨ k.val = 2205 ∨ k.val = 2206 ∨ k.val = 2207 := by omega
  rcases heq with h2176 | h2177 | h2178 | h2179 | h2180 | h2181 | h2182 | h2183 | h2184 | h2185 | h2186 | h2187 | h2188 | h2189 | h2190 | h2191 | h2192 | h2193 | h2194 | h2195 | h2196 | h2197 | h2198 | h2199 | h2200 | h2201 | h2202 | h2203 | h2204 | h2205 | h2206 | h2207
  · have he : k = (2176 : Fin 2886) := Fin.ext h2176
    subst k
    rw [keyMomentRowsAt2176]
    exact keyMoment2176 B hB
  · have he : k = (2177 : Fin 2886) := Fin.ext h2177
    subst k
    rw [keyMomentRowsAt2177]
    exact keyMoment2177 B hB
  · have he : k = (2178 : Fin 2886) := Fin.ext h2178
    subst k
    rw [keyMomentRowsAt2178]
    exact keyMoment2178 B hB
  · have he : k = (2179 : Fin 2886) := Fin.ext h2179
    subst k
    rw [keyMomentRowsAt2179]
    exact keyMoment2179 B hB
  · have he : k = (2180 : Fin 2886) := Fin.ext h2180
    subst k
    rw [keyMomentRowsAt2180]
    exact keyMoment2180 B hB
  · have he : k = (2181 : Fin 2886) := Fin.ext h2181
    subst k
    rw [keyMomentRowsAt2181]
    exact keyMoment2181 B hB
  · have he : k = (2182 : Fin 2886) := Fin.ext h2182
    subst k
    rw [keyMomentRowsAt2182]
    exact keyMoment2182 B hB
  · have he : k = (2183 : Fin 2886) := Fin.ext h2183
    subst k
    rw [keyMomentRowsAt2183]
    exact keyMoment2183 B hB
  · have he : k = (2184 : Fin 2886) := Fin.ext h2184
    subst k
    rw [keyMomentRowsAt2184]
    exact keyMoment2184 B hB
  · have he : k = (2185 : Fin 2886) := Fin.ext h2185
    subst k
    rw [keyMomentRowsAt2185]
    exact keyMoment2185 B hB
  · have he : k = (2186 : Fin 2886) := Fin.ext h2186
    subst k
    rw [keyMomentRowsAt2186]
    exact keyMoment2186 B hB
  · have he : k = (2187 : Fin 2886) := Fin.ext h2187
    subst k
    rw [keyMomentRowsAt2187]
    exact keyMoment2187 B hB
  · have he : k = (2188 : Fin 2886) := Fin.ext h2188
    subst k
    rw [keyMomentRowsAt2188]
    exact keyMoment2188 B hB
  · have he : k = (2189 : Fin 2886) := Fin.ext h2189
    subst k
    rw [keyMomentRowsAt2189]
    exact keyMoment2189 B hB
  · have he : k = (2190 : Fin 2886) := Fin.ext h2190
    subst k
    rw [keyMomentRowsAt2190]
    exact keyMoment2190 B hB
  · have he : k = (2191 : Fin 2886) := Fin.ext h2191
    subst k
    rw [keyMomentRowsAt2191]
    exact keyMoment2191 B hB
  · have he : k = (2192 : Fin 2886) := Fin.ext h2192
    subst k
    rw [keyMomentRowsAt2192]
    exact keyMoment2192 B hB
  · have he : k = (2193 : Fin 2886) := Fin.ext h2193
    subst k
    rw [keyMomentRowsAt2193]
    exact keyMoment2193 B hB
  · have he : k = (2194 : Fin 2886) := Fin.ext h2194
    subst k
    rw [keyMomentRowsAt2194]
    exact keyMoment2194 B hB
  · have he : k = (2195 : Fin 2886) := Fin.ext h2195
    subst k
    rw [keyMomentRowsAt2195]
    exact keyMoment2195 B hB
  · have he : k = (2196 : Fin 2886) := Fin.ext h2196
    subst k
    rw [keyMomentRowsAt2196]
    exact keyMoment2196 B hB
  · have he : k = (2197 : Fin 2886) := Fin.ext h2197
    subst k
    rw [keyMomentRowsAt2197]
    exact keyMoment2197 B hB
  · have he : k = (2198 : Fin 2886) := Fin.ext h2198
    subst k
    rw [keyMomentRowsAt2198]
    exact keyMoment2198 B hB
  · have he : k = (2199 : Fin 2886) := Fin.ext h2199
    subst k
    rw [keyMomentRowsAt2199]
    exact keyMoment2199 B hB
  · have he : k = (2200 : Fin 2886) := Fin.ext h2200
    subst k
    rw [keyMomentRowsAt2200]
    exact keyMoment2200 B hB
  · have he : k = (2201 : Fin 2886) := Fin.ext h2201
    subst k
    rw [keyMomentRowsAt2201]
    exact keyMoment2201 B hB
  · have he : k = (2202 : Fin 2886) := Fin.ext h2202
    subst k
    rw [keyMomentRowsAt2202]
    exact keyMoment2202 B hB
  · have he : k = (2203 : Fin 2886) := Fin.ext h2203
    subst k
    rw [keyMomentRowsAt2203]
    exact keyMoment2203 B hB
  · have he : k = (2204 : Fin 2886) := Fin.ext h2204
    subst k
    rw [keyMomentRowsAt2204]
    exact keyMoment2204 B hB
  · have he : k = (2205 : Fin 2886) := Fin.ext h2205
    subst k
    rw [keyMomentRowsAt2205]
    exact keyMoment2205 B hB
  · have he : k = (2206 : Fin 2886) := Fin.ext h2206
    subst k
    rw [keyMomentRowsAt2206]
    exact keyMoment2206 B hB
  · have he : k = (2207 : Fin 2886) := Fin.ext h2207
    subst k
    rw [keyMomentRowsAt2207]
    exact keyMoment2207 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound68_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound68_e_oai
