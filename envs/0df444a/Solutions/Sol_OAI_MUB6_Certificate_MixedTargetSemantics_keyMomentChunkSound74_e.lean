-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound74_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:02:25.053055+00:00
-- url     : https://prove2.me/submissions/d64e7f8b-45a9-4b1b-9322-4fb43f7e008a

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical328
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical42048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42048 raw42048Labels = mixedMoment B node4038 node4038Labels := by
  calc
    mixedMoment B raw42048 raw42048Labels = mixedMoment B raw42048step0 raw42048step0Labels := by
      have ha : raw42048step0 = (fun i j => raw42048 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42048step0 raw42048; decide +kernel
      have hl : raw42048step0Labels = raw42048Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42048 raw42048Labels permutation155 permutation2
    mixedMoment B raw42048step0 raw42048step0Labels = mixedMoment B raw42048step1 raw42048step1Labels := by
      have ha : raw42048step1 = raw42048step0 := by apply Matrix.ext; unfold raw42048step1 raw42048step0; decide +kernel
      have hl : raw42048step0Labels = labelEmbedding1 ∘ raw42048step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42048step0 raw42048step0Labels raw42048step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4038 node4038Labels := by rfl

theorem canonical42049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42049 raw42049Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw42049 raw42049Labels = mixedMoment B raw42049step0 raw42049step0Labels := by
      have ha : raw42049step0 = (fun i j => raw42049 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42049step0 raw42049; decide +kernel
      have hl : raw42049step0Labels = raw42049Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42049 raw42049Labels permutation152 permutation3
    mixedMoment B raw42049step0 raw42049step0Labels = mixedMoment B raw42049step1 raw42049step1Labels := by
      have ha : raw42049step1 = raw42049step0 := by apply Matrix.ext; unfold raw42049step1 raw42049step0; decide +kernel
      have hl : raw42049step0Labels = labelEmbedding7 ∘ raw42049step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42049step0 raw42049step0Labels raw42049step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5408 node5408Labels := by rfl

theorem canonical42050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42050 raw42050Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw42050 raw42050Labels = mixedMoment B raw42050step0 raw42050step0Labels := by
      have ha : raw42050step0 = (fun i j => raw42050 (permutation427 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42050step0 raw42050; decide +kernel
      have hl : raw42050step0Labels = raw42050Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42050 raw42050Labels permutation427 permutation4
    mixedMoment B raw42050step0 raw42050step0Labels = mixedMoment B raw42050step1 raw42050step1Labels := by
      have ha : raw42050step1 = raw42050step0 := by apply Matrix.ext; unfold raw42050step1 raw42050step0; decide +kernel
      have hl : raw42050step0Labels = labelEmbedding1 ∘ raw42050step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42050step0 raw42050step0Labels raw42050step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

theorem canonical42051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42051 raw42051Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw42051 raw42051Labels = mixedMoment B raw42051step0 raw42051step0Labels := by
      have ha : raw42051step0 = (fun i j => raw42051 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42051step0 raw42051; decide +kernel
      have hl : raw42051step0Labels = raw42051Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42051 raw42051Labels permutation161 permutation5
    mixedMoment B raw42051step0 raw42051step0Labels = mixedMoment B raw42051step1 raw42051step1Labels := by
      have ha : raw42051step1 = -raw42051step0 := by apply Matrix.ext; change ∀ i j, raw42051step1 i j = -(raw42051step0 i j); unfold raw42051step1 raw42051step0; decide +kernel
      have hl : raw42051step1Labels = raw42051step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42051step1 raw42051step1Labels = mixedMoment B raw42051step2 raw42051step2Labels := by
      have ha : raw42051step2 = raw42051step1 := by apply Matrix.ext; unfold raw42051step2 raw42051step1; decide +kernel
      have hl : raw42051step1Labels = labelEmbedding9 ∘ raw42051step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42051step1 raw42051step1Labels raw42051step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical42052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42052 raw42052Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw42052 raw42052Labels = mixedMoment B raw42052step0 raw42052step0Labels := by
      have hz : ∀ j, raw42052 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42052step0 = (fun i j => raw42052 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42052step0 raw42052; decide +kernel
      have hl : raw42052step0Labels = raw42052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42052 raw42052Labels permutation520 hz
    mixedMoment B raw42052step0 raw42052step0Labels = mixedMoment B raw42052step1 raw42052step1Labels := by
      have hz : ∀ j, raw42052step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42052step1 = (fun i j => raw42052step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42052step1 raw42052step0; decide +kernel
      have hl : raw42052step1Labels = raw42052step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42052step0 raw42052step0Labels permutation104 hz
    mixedMoment B raw42052step1 raw42052step1Labels = mixedMoment B raw42052step2 raw42052step2Labels := by
      have ha : raw42052step2 = (fun i j => raw42052step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42052step2 raw42052step1; decide +kernel
      have hl : raw42052step2Labels = raw42052step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42052step1 raw42052step1Labels permutation31 permutation2
    mixedMoment B raw42052step2 raw42052step2Labels = mixedMoment B raw42052step3 raw42052step3Labels := by
      have ha : raw42052step3 = -raw42052step2 := by apply Matrix.ext; change ∀ i j, raw42052step3 i j = -(raw42052step2 i j); unfold raw42052step3 raw42052step2; decide +kernel
      have hl : raw42052step3Labels = raw42052step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42052step3 raw42052step3Labels = mixedMoment B raw42052step4 raw42052step4Labels := by
      have ha : raw42052step4 = raw42052step3 := by apply Matrix.ext; unfold raw42052step4 raw42052step3; decide +kernel
      have hl : raw42052step3Labels = labelEmbedding1 ∘ raw42052step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42052step3 raw42052step3Labels raw42052step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3230 node3230Labels := by rfl

theorem canonical42053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42053 raw42053Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw42053 raw42053Labels = mixedMoment B raw42053step0 raw42053step0Labels := by
      have hz : ∀ j, raw42053 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42053step0 = (fun i j => raw42053 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42053step0 raw42053; decide +kernel
      have hl : raw42053step0Labels = raw42053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42053 raw42053Labels permutation520 hz
    mixedMoment B raw42053step0 raw42053step0Labels = mixedMoment B raw42053step1 raw42053step1Labels := by
      have hz : ∀ j, raw42053step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42053step1 = (fun i j => raw42053step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42053step1 raw42053step0; decide +kernel
      have hl : raw42053step1Labels = raw42053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42053step0 raw42053step0Labels permutation104 hz
    mixedMoment B raw42053step1 raw42053step1Labels = mixedMoment B raw42053step2 raw42053step2Labels := by
      have ha : raw42053step2 = (fun i j => raw42053step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42053step2 raw42053step1; decide +kernel
      have hl : raw42053step2Labels = raw42053step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42053step1 raw42053step1Labels permutation31 permutation3
    mixedMoment B raw42053step2 raw42053step2Labels = mixedMoment B raw42053step3 raw42053step3Labels := by
      have ha : raw42053step3 = -raw42053step2 := by apply Matrix.ext; change ∀ i j, raw42053step3 i j = -(raw42053step2 i j); unfold raw42053step3 raw42053step2; decide +kernel
      have hl : raw42053step3Labels = raw42053step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42053step3 raw42053step3Labels = mixedMoment B raw42053step4 raw42053step4Labels := by
      have ha : raw42053step4 = raw42053step3 := by apply Matrix.ext; unfold raw42053step4 raw42053step3; decide +kernel
      have hl : raw42053step3Labels = labelEmbedding7 ∘ raw42053step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42053step3 raw42053step3Labels raw42053step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4894 node4894Labels := by rfl

theorem canonical42054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42054 raw42054Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw42054 raw42054Labels = mixedMoment B raw42054step0 raw42054step0Labels := by
      have hz : ∀ j, raw42054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42054step0 = (fun i j => raw42054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42054step0 raw42054; decide +kernel
      have hl : raw42054step0Labels = raw42054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42054 raw42054Labels permutation434 hz
    mixedMoment B raw42054step0 raw42054step0Labels = mixedMoment B raw42054step1 raw42054step1Labels := by
      have ha : raw42054step1 = (fun i j => raw42054step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42054step1 raw42054step0; decide +kernel
      have hl : raw42054step1Labels = raw42054step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42054step0 raw42054step0Labels permutation139 permutation4
    mixedMoment B raw42054step1 raw42054step1Labels = mixedMoment B raw42054step2 raw42054step2Labels := by
      have ha : raw42054step2 = raw42054step1 := by apply Matrix.ext; unfold raw42054step2 raw42054step1; decide +kernel
      have hl : raw42054step1Labels = labelEmbedding1 ∘ raw42054step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42054step1 raw42054step1Labels raw42054step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3089 node3089Labels := by rfl

theorem canonical42055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42055 raw42055Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw42055 raw42055Labels = mixedMoment B raw42055step0 raw42055step0Labels := by
      have hz : ∀ j, raw42055 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42055step0 = (fun i j => raw42055 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42055step0 raw42055; decide +kernel
      have hl : raw42055step0Labels = raw42055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42055 raw42055Labels permutation434 hz
    mixedMoment B raw42055step0 raw42055step0Labels = mixedMoment B raw42055step1 raw42055step1Labels := by
      have ha : raw42055step1 = (fun i j => raw42055step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42055step1 raw42055step0; decide +kernel
      have hl : raw42055step1Labels = raw42055step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42055step0 raw42055step0Labels permutation149 permutation5
    mixedMoment B raw42055step1 raw42055step1Labels = mixedMoment B raw42055step2 raw42055step2Labels := by
      have ha : raw42055step2 = raw42055step1 := by apply Matrix.ext; unfold raw42055step2 raw42055step1; decide +kernel
      have hl : raw42055step1Labels = labelEmbedding9 ∘ raw42055step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42055step1 raw42055step1Labels raw42055step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical42056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42056 raw42056Labels = mixedMoment B node4035 node4035Labels := by
  calc
    mixedMoment B raw42056 raw42056Labels = mixedMoment B raw42056step0 raw42056step0Labels := by
      have hz : ∀ j, raw42056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42056step0 = (fun i j => raw42056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42056step0 raw42056; decide +kernel
      have hl : raw42056step0Labels = raw42056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42056 raw42056Labels permutation434 hz
    mixedMoment B raw42056step0 raw42056step0Labels = mixedMoment B raw42056step1 raw42056step1Labels := by
      have ha : raw42056step1 = raw42056step0 := by apply Matrix.ext; unfold raw42056step1 raw42056step0; decide +kernel
      have hl : raw42056step0Labels = labelEmbedding1 ∘ raw42056step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42056step0 raw42056step0Labels raw42056step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4035 node4035Labels := by rfl

theorem canonical42057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42057 raw42057Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw42057 raw42057Labels = mixedMoment B raw42057step0 raw42057step0Labels := by
      have hz : ∀ j, raw42057 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42057step0 = (fun i j => raw42057 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42057step0 raw42057; decide +kernel
      have hl : raw42057step0Labels = raw42057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42057 raw42057Labels permutation434 hz
    mixedMoment B raw42057step0 raw42057step0Labels = mixedMoment B raw42057step1 raw42057step1Labels := by
      have ha : raw42057step1 = (fun i j => raw42057step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42057step1 raw42057step0; decide +kernel
      have hl : raw42057step1Labels = raw42057step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42057step0 raw42057step0Labels permutation151 permutation3
    mixedMoment B raw42057step1 raw42057step1Labels = mixedMoment B raw42057step2 raw42057step2Labels := by
      have ha : raw42057step2 = -raw42057step1 := by apply Matrix.ext; change ∀ i j, raw42057step2 i j = -(raw42057step1 i j); unfold raw42057step2 raw42057step1; decide +kernel
      have hl : raw42057step2Labels = raw42057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42057step2 raw42057step2Labels = mixedMoment B raw42057step3 raw42057step3Labels := by
      have ha : raw42057step3 = raw42057step2 := by apply Matrix.ext; unfold raw42057step3 raw42057step2; decide +kernel
      have hl : raw42057step2Labels = labelEmbedding7 ∘ raw42057step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42057step2 raw42057step2Labels raw42057step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5409 node5409Labels := by rfl

theorem canonical42058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42058 raw42058Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw42058 raw42058Labels = mixedMoment B raw42058step0 raw42058step0Labels := by
      have hz : ∀ j, raw42058 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42058step0 = (fun i j => raw42058 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42058step0 raw42058; decide +kernel
      have hl : raw42058step0Labels = raw42058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42058 raw42058Labels permutation434 hz
    mixedMoment B raw42058step0 raw42058step0Labels = mixedMoment B raw42058step1 raw42058step1Labels := by
      have ha : raw42058step1 = (fun i j => raw42058step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42058step1 raw42058step0; decide +kernel
      have hl : raw42058step1Labels = raw42058step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42058step0 raw42058step0Labels permutation151 permutation2
    mixedMoment B raw42058step1 raw42058step1Labels = mixedMoment B raw42058step2 raw42058step2Labels := by
      have ha : raw42058step2 = -raw42058step1 := by apply Matrix.ext; change ∀ i j, raw42058step2 i j = -(raw42058step1 i j); unfold raw42058step2 raw42058step1; decide +kernel
      have hl : raw42058step2Labels = raw42058step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42058step2 raw42058step2Labels = mixedMoment B raw42058step3 raw42058step3Labels := by
      have ha : raw42058step3 = raw42058step2 := by apply Matrix.ext; unfold raw42058step3 raw42058step2; decide +kernel
      have hl : raw42058step2Labels = labelEmbedding1 ∘ raw42058step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42058step2 raw42058step2Labels raw42058step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4003 node4003Labels := by rfl

theorem canonical42059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42059 raw42059Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw42059 raw42059Labels = mixedMoment B raw42059step0 raw42059step0Labels := by
      have hz : ∀ j, raw42059 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42059step0 = (fun i j => raw42059 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42059step0 raw42059; decide +kernel
      have hl : raw42059step0Labels = raw42059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42059 raw42059Labels permutation434 hz
    mixedMoment B raw42059step0 raw42059step0Labels = mixedMoment B raw42059step1 raw42059step1Labels := by
      have ha : raw42059step1 = (fun i j => raw42059step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42059step1 raw42059step0; decide +kernel
      have hl : raw42059step1Labels = raw42059step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42059step0 raw42059step0Labels permutation32 permutation3
    mixedMoment B raw42059step1 raw42059step1Labels = mixedMoment B raw42059step2 raw42059step2Labels := by
      have ha : raw42059step2 = raw42059step1 := by apply Matrix.ext; unfold raw42059step2 raw42059step1; decide +kernel
      have hl : raw42059step1Labels = labelEmbedding7 ∘ raw42059step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42059step1 raw42059step1Labels raw42059step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical42060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42060 raw42060Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw42060 raw42060Labels = mixedMoment B raw42060step0 raw42060step0Labels := by
      have hz : ∀ j, raw42060 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42060step0 = (fun i j => raw42060 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42060step0 raw42060; decide +kernel
      have hl : raw42060step0Labels = raw42060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42060 raw42060Labels permutation434 hz
    mixedMoment B raw42060step0 raw42060step0Labels = mixedMoment B raw42060step1 raw42060step1Labels := by
      have ha : raw42060step1 = (fun i j => raw42060step0 (permutation115 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42060step1 raw42060step0; decide +kernel
      have hl : raw42060step1Labels = raw42060step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42060step0 raw42060step0Labels permutation115 permutation4
    mixedMoment B raw42060step1 raw42060step1Labels = mixedMoment B raw42060step2 raw42060step2Labels := by
      have ha : raw42060step2 = raw42060step1 := by apply Matrix.ext; unfold raw42060step2 raw42060step1; decide +kernel
      have hl : raw42060step1Labels = labelEmbedding1 ∘ raw42060step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42060step1 raw42060step1Labels raw42060step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2732 node2732Labels := by rfl

theorem canonical42061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42061 raw42061Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw42061 raw42061Labels = mixedMoment B raw42061step0 raw42061step0Labels := by
      have hz : ∀ j, raw42061 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42061step0 = (fun i j => raw42061 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42061step0 raw42061; decide +kernel
      have hl : raw42061step0Labels = raw42061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42061 raw42061Labels permutation434 hz
    mixedMoment B raw42061step0 raw42061step0Labels = mixedMoment B raw42061step1 raw42061step1Labels := by
      have ha : raw42061step1 = (fun i j => raw42061step0 (permutation115 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42061step1 raw42061step0; decide +kernel
      have hl : raw42061step1Labels = raw42061step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42061step0 raw42061step0Labels permutation115 permutation4
    mixedMoment B raw42061step1 raw42061step1Labels = mixedMoment B raw42061step2 raw42061step2Labels := by
      have ha : raw42061step2 = raw42061step1 := by apply Matrix.ext; unfold raw42061step2 raw42061step1; decide +kernel
      have hl : raw42061step1Labels = labelEmbedding10 ∘ raw42061step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42061step1 raw42061step1Labels raw42061step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

theorem canonical42062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42062 raw42062Labels = mixedMoment B node4032 node4032Labels := by
  calc
    mixedMoment B raw42062 raw42062Labels = mixedMoment B raw42062step0 raw42062step0Labels := by
      have ha : raw42062step0 = (fun i j => raw42062 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42062step0 raw42062; decide +kernel
      have hl : raw42062step0Labels = raw42062Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42062 raw42062Labels permutation158 permutation2
    mixedMoment B raw42062step0 raw42062step0Labels = mixedMoment B raw42062step1 raw42062step1Labels := by
      have ha : raw42062step1 = raw42062step0 := by apply Matrix.ext; unfold raw42062step1 raw42062step0; decide +kernel
      have hl : raw42062step0Labels = labelEmbedding1 ∘ raw42062step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42062step0 raw42062step0Labels raw42062step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4032 node4032Labels := by rfl

theorem canonical42063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42063 raw42063Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw42063 raw42063Labels = mixedMoment B raw42063step0 raw42063step0Labels := by
      have ha : raw42063step0 = (fun i j => raw42063 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42063step0 raw42063; decide +kernel
      have hl : raw42063step0Labels = raw42063Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42063 raw42063Labels permutation152 permutation3
    mixedMoment B raw42063step0 raw42063step0Labels = mixedMoment B raw42063step1 raw42063step1Labels := by
      have ha : raw42063step1 = raw42063step0 := by apply Matrix.ext; unfold raw42063step1 raw42063step0; decide +kernel
      have hl : raw42063step0Labels = labelEmbedding7 ∘ raw42063step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42063step0 raw42063step0Labels raw42063step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

theorem canonical42064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42064 raw42064Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw42064 raw42064Labels = mixedMoment B raw42064step0 raw42064step0Labels := by
      have ha : raw42064step0 = (fun i j => raw42064 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42064step0 raw42064; decide +kernel
      have hl : raw42064step0Labels = raw42064Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42064 raw42064Labels permutation682 permutation2
    mixedMoment B raw42064step0 raw42064step0Labels = mixedMoment B raw42064step1 raw42064step1Labels := by
      have ha : raw42064step1 = -raw42064step0 := by apply Matrix.ext; change ∀ i j, raw42064step1 i j = -(raw42064step0 i j); unfold raw42064step1 raw42064step0; decide +kernel
      have hl : raw42064step1Labels = raw42064step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42064step1 raw42064step1Labels = mixedMoment B raw42064step2 raw42064step2Labels := by
      have ha : raw42064step2 = raw42064step1 := by apply Matrix.ext; unfold raw42064step2 raw42064step1; decide +kernel
      have hl : raw42064step1Labels = labelEmbedding1 ∘ raw42064step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42064step1 raw42064step1Labels raw42064step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3990 node3990Labels := by rfl

theorem canonical42065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42065 raw42065Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw42065 raw42065Labels = mixedMoment B raw42065step0 raw42065step0Labels := by
      have ha : raw42065step0 = (fun i j => raw42065 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42065step0 raw42065; decide +kernel
      have hl : raw42065step0Labels = raw42065Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42065 raw42065Labels permutation152 permutation3
    mixedMoment B raw42065step0 raw42065step0Labels = mixedMoment B raw42065step1 raw42065step1Labels := by
      have ha : raw42065step1 = raw42065step0 := by apply Matrix.ext; unfold raw42065step1 raw42065step0; decide +kernel
      have hl : raw42065step0Labels = labelEmbedding7 ∘ raw42065step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42065step0 raw42065step0Labels raw42065step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical42066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42066 raw42066Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw42066 raw42066Labels = mixedMoment B raw42066step0 raw42066step0Labels := by
      have ha : raw42066step0 = (fun i j => raw42066 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42066step0 raw42066; decide +kernel
      have hl : raw42066step0Labels = raw42066Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42066 raw42066Labels permutation682 permutation2
    mixedMoment B raw42066step0 raw42066step0Labels = mixedMoment B raw42066step1 raw42066step1Labels := by
      have ha : raw42066step1 = -raw42066step0 := by apply Matrix.ext; change ∀ i j, raw42066step1 i j = -(raw42066step0 i j); unfold raw42066step1 raw42066step0; decide +kernel
      have hl : raw42066step1Labels = raw42066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42066step1 raw42066step1Labels = mixedMoment B raw42066step2 raw42066step2Labels := by
      have ha : raw42066step2 = raw42066step1 := by apply Matrix.ext; unfold raw42066step2 raw42066step1; decide +kernel
      have hl : raw42066step1Labels = labelEmbedding1 ∘ raw42066step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42066step1 raw42066step1Labels raw42066step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3872 node3872Labels := by rfl

theorem canonical42067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42067 raw42067Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42067 raw42067Labels = mixedMoment B raw42067step0 raw42067step0Labels := by
      have ha : raw42067step0 = (fun i j => raw42067 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42067step0 raw42067; decide +kernel
      have hl : raw42067step0Labels = raw42067Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42067 raw42067Labels permutation152 permutation3
    mixedMoment B raw42067step0 raw42067step0Labels = mixedMoment B raw42067step1 raw42067step1Labels := by
      have ha : raw42067step1 = raw42067step0 := by apply Matrix.ext; unfold raw42067step1 raw42067step0; decide +kernel
      have hl : raw42067step0Labels = labelEmbedding7 ∘ raw42067step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42067step0 raw42067step0Labels raw42067step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical42068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42068 raw42068Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw42068 raw42068Labels = mixedMoment B raw42068step0 raw42068step0Labels := by
      have ha : raw42068step0 = (fun i j => raw42068 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42068step0 raw42068; decide +kernel
      have hl : raw42068step0Labels = raw42068Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42068 raw42068Labels permutation682 permutation2
    mixedMoment B raw42068step0 raw42068step0Labels = mixedMoment B raw42068step1 raw42068step1Labels := by
      have ha : raw42068step1 = -raw42068step0 := by apply Matrix.ext; change ∀ i j, raw42068step1 i j = -(raw42068step0 i j); unfold raw42068step1 raw42068step0; decide +kernel
      have hl : raw42068step1Labels = raw42068step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42068step1 raw42068step1Labels = mixedMoment B raw42068step2 raw42068step2Labels := by
      have ha : raw42068step2 = raw42068step1 := by apply Matrix.ext; unfold raw42068step2 raw42068step1; decide +kernel
      have hl : raw42068step1Labels = labelEmbedding1 ∘ raw42068step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42068step1 raw42068step1Labels raw42068step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3841 node3841Labels := by rfl

theorem canonical42069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42069 raw42069Labels = mixedMoment B node5426 node5426Labels := by
  calc
    mixedMoment B raw42069 raw42069Labels = mixedMoment B raw42069step0 raw42069step0Labels := by
      have ha : raw42069step0 = (fun i j => raw42069 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42069step0 raw42069; decide +kernel
      have hl : raw42069step0Labels = raw42069Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42069 raw42069Labels permutation682 permutation2
    mixedMoment B raw42069step0 raw42069step0Labels = mixedMoment B raw42069step1 raw42069step1Labels := by
      have ha : raw42069step1 = -raw42069step0 := by apply Matrix.ext; change ∀ i j, raw42069step1 i j = -(raw42069step0 i j); unfold raw42069step1 raw42069step0; decide +kernel
      have hl : raw42069step1Labels = raw42069step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42069step1 raw42069step1Labels = mixedMoment B raw42069step2 raw42069step2Labels := by
      have ha : raw42069step2 = raw42069step1 := by apply Matrix.ext; unfold raw42069step2 raw42069step1; decide +kernel
      have hl : raw42069step1Labels = labelEmbedding8 ∘ raw42069step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42069step1 raw42069step1Labels raw42069step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5426 node5426Labels := by rfl

theorem canonical42070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42070 raw42070Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw42070 raw42070Labels = mixedMoment B raw42070step0 raw42070step0Labels := by
      have ha : raw42070step0 = (fun i j => raw42070 (permutation616 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42070step0 raw42070; decide +kernel
      have hl : raw42070step0Labels = raw42070Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42070 raw42070Labels permutation616 permutation4
    mixedMoment B raw42070step0 raw42070step0Labels = mixedMoment B raw42070step1 raw42070step1Labels := by
      have ha : raw42070step1 = raw42070step0 := by apply Matrix.ext; unfold raw42070step1 raw42070step0; decide +kernel
      have hl : raw42070step0Labels = labelEmbedding1 ∘ raw42070step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42070step0 raw42070step0Labels raw42070step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2710 node2710Labels := by rfl

theorem canonical42071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42071 raw42071Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw42071 raw42071Labels = mixedMoment B raw42071step0 raw42071step0Labels := by
      have ha : raw42071step0 = (fun i j => raw42071 (permutation616 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42071step0 raw42071; decide +kernel
      have hl : raw42071step0Labels = raw42071Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42071 raw42071Labels permutation616 permutation4
    mixedMoment B raw42071step0 raw42071step0Labels = mixedMoment B raw42071step1 raw42071step1Labels := by
      have ha : raw42071step1 = raw42071step0 := by apply Matrix.ext; unfold raw42071step1 raw42071step0; decide +kernel
      have hl : raw42071step0Labels = labelEmbedding10 ∘ raw42071step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42071step0 raw42071step0Labels raw42071step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical42072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42072 raw42072Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw42072 raw42072Labels = mixedMoment B raw42072step0 raw42072step0Labels := by
      have ha : raw42072step0 = (fun i j => raw42072 (permutation676 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42072step0 raw42072; decide +kernel
      have hl : raw42072step0Labels = raw42072Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42072 raw42072Labels permutation676 permutation4
    mixedMoment B raw42072step0 raw42072step0Labels = mixedMoment B raw42072step1 raw42072step1Labels := by
      have ha : raw42072step1 = raw42072step0 := by apply Matrix.ext; unfold raw42072step1 raw42072step0; decide +kernel
      have hl : raw42072step0Labels = labelEmbedding1 ∘ raw42072step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42072step0 raw42072step0Labels raw42072step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3990 node3990Labels := by rfl

theorem canonical42073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42073 raw42073Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw42073 raw42073Labels = mixedMoment B raw42073step0 raw42073step0Labels := by
      have ha : raw42073step0 = (fun i j => raw42073 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42073step0 raw42073; decide +kernel
      have hl : raw42073step0Labels = raw42073Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42073 raw42073Labels permutation176 permutation5
    mixedMoment B raw42073step0 raw42073step0Labels = mixedMoment B raw42073step1 raw42073step1Labels := by
      have ha : raw42073step1 = -raw42073step0 := by apply Matrix.ext; change ∀ i j, raw42073step1 i j = -(raw42073step0 i j); unfold raw42073step1 raw42073step0; decide +kernel
      have hl : raw42073step1Labels = raw42073step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42073step1 raw42073step1Labels = mixedMoment B raw42073step2 raw42073step2Labels := by
      have ha : raw42073step2 = raw42073step1 := by apply Matrix.ext; unfold raw42073step2 raw42073step1; decide +kernel
      have hl : raw42073step1Labels = labelEmbedding9 ∘ raw42073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42073step1 raw42073step1Labels raw42073step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical42074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42074 raw42074Labels = mixedMoment B node4034 node4034Labels := by
  calc
    mixedMoment B raw42074 raw42074Labels = mixedMoment B raw42074step0 raw42074step0Labels := by
      have ha : raw42074step0 = raw42074 := by apply Matrix.ext; unfold raw42074step0 raw42074; decide +kernel
      have hl : raw42074Labels = labelEmbedding1 ∘ raw42074step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42074 raw42074Labels raw42074step0Labels labelEmbedding1 hl
    _ = mixedMoment B node4034 node4034Labels := by rfl

theorem canonical42075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42075 raw42075Labels = mixedMoment B node5427 node5427Labels := by
  calc
    mixedMoment B raw42075 raw42075Labels = mixedMoment B raw42075step0 raw42075step0Labels := by
      have ha : raw42075step0 = (fun i j => raw42075 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42075step0 raw42075; decide +kernel
      have hl : raw42075step0Labels = raw42075Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42075 raw42075Labels permutation152 permutation3
    mixedMoment B raw42075step0 raw42075step0Labels = mixedMoment B raw42075step1 raw42075step1Labels := by
      have ha : raw42075step1 = raw42075step0 := by apply Matrix.ext; unfold raw42075step1 raw42075step0; decide +kernel
      have hl : raw42075step0Labels = labelEmbedding7 ∘ raw42075step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42075step0 raw42075step0Labels raw42075step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5427 node5427Labels := by rfl

theorem canonical42076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42076 raw42076Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw42076 raw42076Labels = mixedMoment B raw42076step0 raw42076step0Labels := by
      have hz : ∀ j, raw42076 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42076step0 = (fun i j => raw42076 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42076step0 raw42076; decide +kernel
      have hl : raw42076step0Labels = raw42076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42076 raw42076Labels permutation434 hz
    mixedMoment B raw42076step0 raw42076step0Labels = mixedMoment B raw42076step1 raw42076step1Labels := by
      have hz : ∀ j, raw42076step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42076step1 = (fun i j => raw42076step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42076step1 raw42076step0; decide +kernel
      have hl : raw42076step1Labels = raw42076step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42076step0 raw42076step0Labels permutation80 hz
    mixedMoment B raw42076step1 raw42076step1Labels = mixedMoment B raw42076step2 raw42076step2Labels := by
      have ha : raw42076step2 = (fun i j => raw42076step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42076step2 raw42076step1; decide +kernel
      have hl : raw42076step2Labels = raw42076step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42076step1 raw42076step1Labels permutation29 permutation4
    mixedMoment B raw42076step2 raw42076step2Labels = mixedMoment B raw42076step3 raw42076step3Labels := by
      have ha : raw42076step3 = raw42076step2 := by apply Matrix.ext; unfold raw42076step3 raw42076step2; decide +kernel
      have hl : raw42076step2Labels = labelEmbedding1 ∘ raw42076step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42076step2 raw42076step2Labels raw42076step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3103 node3103Labels := by rfl

theorem canonical42077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42077 raw42077Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw42077 raw42077Labels = mixedMoment B raw42077step0 raw42077step0Labels := by
      have hz : ∀ j, raw42077 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42077step0 = (fun i j => raw42077 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42077step0 raw42077; decide +kernel
      have hl : raw42077step0Labels = raw42077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42077 raw42077Labels permutation434 hz
    mixedMoment B raw42077step0 raw42077step0Labels = mixedMoment B raw42077step1 raw42077step1Labels := by
      have hz : ∀ j, raw42077step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42077step1 = (fun i j => raw42077step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42077step1 raw42077step0; decide +kernel
      have hl : raw42077step1Labels = raw42077step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42077step0 raw42077step0Labels permutation80 hz
    mixedMoment B raw42077step1 raw42077step1Labels = mixedMoment B raw42077step2 raw42077step2Labels := by
      have ha : raw42077step2 = (fun i j => raw42077step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42077step2 raw42077step1; decide +kernel
      have hl : raw42077step2Labels = raw42077step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42077step1 raw42077step1Labels permutation29 permutation5
    mixedMoment B raw42077step2 raw42077step2Labels = mixedMoment B raw42077step3 raw42077step3Labels := by
      have ha : raw42077step3 = raw42077step2 := by apply Matrix.ext; unfold raw42077step3 raw42077step2; decide +kernel
      have hl : raw42077step2Labels = labelEmbedding9 ∘ raw42077step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42077step2 raw42077step2Labels raw42077step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical42078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42078 raw42078Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw42078 raw42078Labels = mixedMoment B raw42078step0 raw42078step0Labels := by
      have hz : ∀ j, raw42078 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42078step0 = (fun i j => raw42078 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42078step0 raw42078; decide +kernel
      have hl : raw42078step0Labels = raw42078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42078 raw42078Labels permutation434 hz
    mixedMoment B raw42078step0 raw42078step0Labels = mixedMoment B raw42078step1 raw42078step1Labels := by
      have hz : ∀ j, raw42078step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42078step1 = (fun i j => raw42078step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42078step1 raw42078step0; decide +kernel
      have hl : raw42078step1Labels = raw42078step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42078step0 raw42078step0Labels permutation80 hz
    mixedMoment B raw42078step1 raw42078step1Labels = mixedMoment B raw42078step2 raw42078step2Labels := by
      have ha : raw42078step2 = (fun i j => raw42078step1 (permutation23 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42078step2 raw42078step1; decide +kernel
      have hl : raw42078step2Labels = raw42078step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42078step1 raw42078step1Labels permutation23 permutation4
    mixedMoment B raw42078step2 raw42078step2Labels = mixedMoment B raw42078step3 raw42078step3Labels := by
      have ha : raw42078step3 = raw42078step2 := by apply Matrix.ext; unfold raw42078step3 raw42078step2; decide +kernel
      have hl : raw42078step2Labels = labelEmbedding1 ∘ raw42078step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42078step2 raw42078step2Labels raw42078step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

theorem canonical42079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42079 raw42079Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw42079 raw42079Labels = mixedMoment B raw42079step0 raw42079step0Labels := by
      have hz : ∀ j, raw42079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42079step0 = (fun i j => raw42079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42079step0 raw42079; decide +kernel
      have hl : raw42079step0Labels = raw42079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42079 raw42079Labels permutation434 hz
    mixedMoment B raw42079step0 raw42079step0Labels = mixedMoment B raw42079step1 raw42079step1Labels := by
      have hz : ∀ j, raw42079step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42079step1 = (fun i j => raw42079step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42079step1 raw42079step0; decide +kernel
      have hl : raw42079step1Labels = raw42079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42079step0 raw42079step0Labels permutation80 hz
    mixedMoment B raw42079step1 raw42079step1Labels = mixedMoment B raw42079step2 raw42079step2Labels := by
      have ha : raw42079step2 = (fun i j => raw42079step1 (permutation23 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42079step2 raw42079step1; decide +kernel
      have hl : raw42079step2Labels = raw42079step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42079step1 raw42079step1Labels permutation23 permutation4
    mixedMoment B raw42079step2 raw42079step2Labels = mixedMoment B raw42079step3 raw42079step3Labels := by
      have ha : raw42079step3 = raw42079step2 := by apply Matrix.ext; unfold raw42079step3 raw42079step2; decide +kernel
      have hl : raw42079step2Labels = labelEmbedding10 ∘ raw42079step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42079step2 raw42079step2Labels raw42079step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

theorem canonical42080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42080 raw42080Labels = mixedMoment B node4027 node4027Labels := by
  calc
    mixedMoment B raw42080 raw42080Labels = mixedMoment B raw42080step0 raw42080step0Labels := by
      have hz : ∀ j, raw42080 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42080step0 = (fun i j => raw42080 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42080step0 raw42080; decide +kernel
      have hl : raw42080step0Labels = raw42080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42080 raw42080Labels permutation346 hz
    mixedMoment B raw42080step0 raw42080step0Labels = mixedMoment B raw42080step1 raw42080step1Labels := by
      have ha : raw42080step1 = (fun i j => raw42080step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42080step1 raw42080step0; decide +kernel
      have hl : raw42080step1Labels = raw42080step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42080step0 raw42080step0Labels permutation151 permutation2
    mixedMoment B raw42080step1 raw42080step1Labels = mixedMoment B raw42080step2 raw42080step2Labels := by
      have ha : raw42080step2 = -raw42080step1 := by apply Matrix.ext; change ∀ i j, raw42080step2 i j = -(raw42080step1 i j); unfold raw42080step2 raw42080step1; decide +kernel
      have hl : raw42080step2Labels = raw42080step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42080step2 raw42080step2Labels = mixedMoment B raw42080step3 raw42080step3Labels := by
      have ha : raw42080step3 = raw42080step2 := by apply Matrix.ext; unfold raw42080step3 raw42080step2; decide +kernel
      have hl : raw42080step2Labels = labelEmbedding1 ∘ raw42080step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42080step2 raw42080step2Labels raw42080step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4027 node4027Labels := by rfl

theorem canonical42081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42081 raw42081Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw42081 raw42081Labels = mixedMoment B raw42081step0 raw42081step0Labels := by
      have hz : ∀ j, raw42081 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42081step0 = (fun i j => raw42081 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42081step0 raw42081; decide +kernel
      have hl : raw42081step0Labels = raw42081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42081 raw42081Labels permutation346 hz
    mixedMoment B raw42081step0 raw42081step0Labels = mixedMoment B raw42081step1 raw42081step1Labels := by
      have ha : raw42081step1 = (fun i j => raw42081step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42081step1 raw42081step0; decide +kernel
      have hl : raw42081step1Labels = raw42081step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42081step0 raw42081step0Labels permutation32 permutation3
    mixedMoment B raw42081step1 raw42081step1Labels = mixedMoment B raw42081step2 raw42081step2Labels := by
      have ha : raw42081step2 = raw42081step1 := by apply Matrix.ext; unfold raw42081step2 raw42081step1; decide +kernel
      have hl : raw42081step1Labels = labelEmbedding7 ∘ raw42081step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42081step1 raw42081step1Labels raw42081step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical42082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42082 raw42082Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw42082 raw42082Labels = mixedMoment B raw42082step0 raw42082step0Labels := by
      have hz : ∀ j, raw42082 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42082step0 = (fun i j => raw42082 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42082step0 raw42082; decide +kernel
      have hl : raw42082step0Labels = raw42082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42082 raw42082Labels permutation346 hz
    mixedMoment B raw42082step0 raw42082step0Labels = mixedMoment B raw42082step1 raw42082step1Labels := by
      have ha : raw42082step1 = (fun i j => raw42082step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42082step1 raw42082step0; decide +kernel
      have hl : raw42082step1Labels = raw42082step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42082step0 raw42082step0Labels permutation151 permutation2
    mixedMoment B raw42082step1 raw42082step1Labels = mixedMoment B raw42082step2 raw42082step2Labels := by
      have ha : raw42082step2 = -raw42082step1 := by apply Matrix.ext; change ∀ i j, raw42082step2 i j = -(raw42082step1 i j); unfold raw42082step2 raw42082step1; decide +kernel
      have hl : raw42082step2Labels = raw42082step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42082step2 raw42082step2Labels = mixedMoment B raw42082step3 raw42082step3Labels := by
      have ha : raw42082step3 = raw42082step2 := by apply Matrix.ext; unfold raw42082step3 raw42082step2; decide +kernel
      have hl : raw42082step2Labels = labelEmbedding1 ∘ raw42082step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42082step2 raw42082step2Labels raw42082step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical42083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42083 raw42083Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw42083 raw42083Labels = mixedMoment B raw42083step0 raw42083step0Labels := by
      have hz : ∀ j, raw42083 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42083step0 = (fun i j => raw42083 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42083step0 raw42083; decide +kernel
      have hl : raw42083step0Labels = raw42083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42083 raw42083Labels permutation346 hz
    mixedMoment B raw42083step0 raw42083step0Labels = mixedMoment B raw42083step1 raw42083step1Labels := by
      have ha : raw42083step1 = (fun i j => raw42083step0 (permutation133 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42083step1 raw42083step0; decide +kernel
      have hl : raw42083step1Labels = raw42083step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42083step0 raw42083step0Labels permutation133 permutation7
    mixedMoment B raw42083step1 raw42083step1Labels = mixedMoment B raw42083step2 raw42083step2Labels := by
      have ha : raw42083step2 = raw42083step1 := by apply Matrix.ext; unfold raw42083step2 raw42083step1; decide +kernel
      have hl : raw42083step1Labels = labelEmbedding6 ∘ raw42083step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42083step1 raw42083step1Labels raw42083step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical42084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42084 raw42084Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw42084 raw42084Labels = mixedMoment B raw42084step0 raw42084step0Labels := by
      have hz : ∀ j, raw42084 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42084step0 = (fun i j => raw42084 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42084step0 raw42084; decide +kernel
      have hl : raw42084step0Labels = raw42084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42084 raw42084Labels permutation346 hz
    mixedMoment B raw42084step0 raw42084step0Labels = mixedMoment B raw42084step1 raw42084step1Labels := by
      have ha : raw42084step1 = (fun i j => raw42084step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42084step1 raw42084step0; decide +kernel
      have hl : raw42084step1Labels = raw42084step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42084step0 raw42084step0Labels permutation151 permutation2
    mixedMoment B raw42084step1 raw42084step1Labels = mixedMoment B raw42084step2 raw42084step2Labels := by
      have ha : raw42084step2 = -raw42084step1 := by apply Matrix.ext; change ∀ i j, raw42084step2 i j = -(raw42084step1 i j); unfold raw42084step2 raw42084step1; decide +kernel
      have hl : raw42084step2Labels = raw42084step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42084step2 raw42084step2Labels = mixedMoment B raw42084step3 raw42084step3Labels := by
      have ha : raw42084step3 = raw42084step2 := by apply Matrix.ext; unfold raw42084step3 raw42084step2; decide +kernel
      have hl : raw42084step2Labels = labelEmbedding1 ∘ raw42084step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42084step2 raw42084step2Labels raw42084step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical42085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42085 raw42085Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw42085 raw42085Labels = mixedMoment B raw42085step0 raw42085step0Labels := by
      have hz : ∀ j, raw42085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42085step0 = (fun i j => raw42085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42085step0 raw42085; decide +kernel
      have hl : raw42085step0Labels = raw42085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42085 raw42085Labels permutation346 hz
    mixedMoment B raw42085step0 raw42085step0Labels = mixedMoment B raw42085step1 raw42085step1Labels := by
      have ha : raw42085step1 = (fun i j => raw42085step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42085step1 raw42085step0; decide +kernel
      have hl : raw42085step1Labels = raw42085step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42085step0 raw42085step0Labels permutation146 permutation7
    mixedMoment B raw42085step1 raw42085step1Labels = mixedMoment B raw42085step2 raw42085step2Labels := by
      have ha : raw42085step2 = raw42085step1 := by apply Matrix.ext; unfold raw42085step2 raw42085step1; decide +kernel
      have hl : raw42085step1Labels = labelEmbedding6 ∘ raw42085step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42085step1 raw42085step1Labels raw42085step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

theorem canonical42086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42086 raw42086Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw42086 raw42086Labels = mixedMoment B raw42086step0 raw42086step0Labels := by
      have hz : ∀ j, raw42086 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42086step0 = (fun i j => raw42086 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42086step0 raw42086; decide +kernel
      have hl : raw42086step0Labels = raw42086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42086 raw42086Labels permutation346 hz
    mixedMoment B raw42086step0 raw42086step0Labels = mixedMoment B raw42086step1 raw42086step1Labels := by
      have ha : raw42086step1 = (fun i j => raw42086step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42086step1 raw42086step0; decide +kernel
      have hl : raw42086step1Labels = raw42086step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42086step0 raw42086step0Labels permutation139 permutation4
    mixedMoment B raw42086step1 raw42086step1Labels = mixedMoment B raw42086step2 raw42086step2Labels := by
      have ha : raw42086step2 = raw42086step1 := by apply Matrix.ext; unfold raw42086step2 raw42086step1; decide +kernel
      have hl : raw42086step1Labels = labelEmbedding1 ∘ raw42086step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42086step1 raw42086step1Labels raw42086step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2724 node2724Labels := by rfl

theorem canonical42087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42087 raw42087Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw42087 raw42087Labels = mixedMoment B raw42087step0 raw42087step0Labels := by
      have hz : ∀ j, raw42087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42087step0 = (fun i j => raw42087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42087step0 raw42087; decide +kernel
      have hl : raw42087step0Labels = raw42087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42087 raw42087Labels permutation346 hz
    mixedMoment B raw42087step0 raw42087step0Labels = mixedMoment B raw42087step1 raw42087step1Labels := by
      have ha : raw42087step1 = (fun i j => raw42087step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42087step1 raw42087step0; decide +kernel
      have hl : raw42087step1Labels = raw42087step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42087step0 raw42087step0Labels permutation139 permutation4
    mixedMoment B raw42087step1 raw42087step1Labels = mixedMoment B raw42087step2 raw42087step2Labels := by
      have ha : raw42087step2 = raw42087step1 := by apply Matrix.ext; unfold raw42087step2 raw42087step1; decide +kernel
      have hl : raw42087step1Labels = labelEmbedding10 ∘ raw42087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42087step1 raw42087step1Labels raw42087step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

theorem canonical42088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42088 raw42088Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw42088 raw42088Labels = mixedMoment B raw42088step0 raw42088step0Labels := by
      have hz : ∀ j, raw42088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42088step0 = (fun i j => raw42088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42088step0 raw42088; decide +kernel
      have hl : raw42088step0Labels = raw42088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42088 raw42088Labels permutation346 hz
    mixedMoment B raw42088step0 raw42088step0Labels = mixedMoment B raw42088step1 raw42088step1Labels := by
      have ha : raw42088step1 = (fun i j => raw42088step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42088step1 raw42088step0; decide +kernel
      have hl : raw42088step1Labels = raw42088step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42088step0 raw42088step0Labels permutation149 permutation4
    mixedMoment B raw42088step1 raw42088step1Labels = mixedMoment B raw42088step2 raw42088step2Labels := by
      have ha : raw42088step2 = raw42088step1 := by apply Matrix.ext; unfold raw42088step2 raw42088step1; decide +kernel
      have hl : raw42088step1Labels = labelEmbedding1 ∘ raw42088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42088step1 raw42088step1Labels raw42088step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

theorem canonical42089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42089 raw42089Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw42089 raw42089Labels = mixedMoment B raw42089step0 raw42089step0Labels := by
      have hz : ∀ j, raw42089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42089step0 = (fun i j => raw42089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42089step0 raw42089; decide +kernel
      have hl : raw42089step0Labels = raw42089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42089 raw42089Labels permutation346 hz
    mixedMoment B raw42089step0 raw42089step0Labels = mixedMoment B raw42089step1 raw42089step1Labels := by
      have ha : raw42089step1 = (fun i j => raw42089step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42089step1 raw42089step0; decide +kernel
      have hl : raw42089step1Labels = raw42089step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42089step0 raw42089step0Labels permutation32 permutation3
    mixedMoment B raw42089step1 raw42089step1Labels = mixedMoment B raw42089step2 raw42089step2Labels := by
      have ha : raw42089step2 = raw42089step1 := by apply Matrix.ext; unfold raw42089step2 raw42089step1; decide +kernel
      have hl : raw42089step1Labels = labelEmbedding7 ∘ raw42089step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42089step1 raw42089step1Labels raw42089step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical42090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42090 raw42090Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw42090 raw42090Labels = mixedMoment B raw42090step0 raw42090step0Labels := by
      have ha : raw42090step0 = (fun i j => raw42090 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42090step0 raw42090; decide +kernel
      have hl : raw42090step0Labels = raw42090Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42090 raw42090Labels permutation682 permutation2
    mixedMoment B raw42090step0 raw42090step0Labels = mixedMoment B raw42090step1 raw42090step1Labels := by
      have ha : raw42090step1 = -raw42090step0 := by apply Matrix.ext; change ∀ i j, raw42090step1 i j = -(raw42090step0 i j); unfold raw42090step1 raw42090step0; decide +kernel
      have hl : raw42090step1Labels = raw42090step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42090step1 raw42090step1Labels = mixedMoment B raw42090step2 raw42090step2Labels := by
      have ha : raw42090step2 = raw42090step1 := by apply Matrix.ext; unfold raw42090step2 raw42090step1; decide +kernel
      have hl : raw42090step1Labels = labelEmbedding1 ∘ raw42090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42090step1 raw42090step1Labels raw42090step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

theorem canonical42091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42091 raw42091Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw42091 raw42091Labels = mixedMoment B raw42091step0 raw42091step0Labels := by
      have ha : raw42091step0 = (fun i j => raw42091 (permutation668 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42091step0 raw42091; decide +kernel
      have hl : raw42091step0Labels = raw42091Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42091 raw42091Labels permutation668 permutation7
    mixedMoment B raw42091step0 raw42091step0Labels = mixedMoment B raw42091step1 raw42091step1Labels := by
      have ha : raw42091step1 = raw42091step0 := by apply Matrix.ext; unfold raw42091step1 raw42091step0; decide +kernel
      have hl : raw42091step0Labels = labelEmbedding6 ∘ raw42091step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42091step0 raw42091step0Labels raw42091step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical42092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42092 raw42092Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw42092 raw42092Labels = mixedMoment B raw42092step0 raw42092step0Labels := by
      have ha : raw42092step0 = (fun i j => raw42092 (permutation634 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42092step0 raw42092; decide +kernel
      have hl : raw42092step0Labels = raw42092Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42092 raw42092Labels permutation634 permutation4
    mixedMoment B raw42092step0 raw42092step0Labels = mixedMoment B raw42092step1 raw42092step1Labels := by
      have ha : raw42092step1 = raw42092step0 := by apply Matrix.ext; unfold raw42092step1 raw42092step0; decide +kernel
      have hl : raw42092step0Labels = labelEmbedding1 ∘ raw42092step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42092step0 raw42092step0Labels raw42092step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3972 node3972Labels := by rfl

theorem canonical42093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42093 raw42093Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42093 raw42093Labels = mixedMoment B raw42093step0 raw42093step0Labels := by
      have ha : raw42093step0 = (fun i j => raw42093 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42093step0 raw42093; decide +kernel
      have hl : raw42093step0Labels = raw42093Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42093 raw42093Labels permutation152 permutation3
    mixedMoment B raw42093step0 raw42093step0Labels = mixedMoment B raw42093step1 raw42093step1Labels := by
      have ha : raw42093step1 = raw42093step0 := by apply Matrix.ext; unfold raw42093step1 raw42093step0; decide +kernel
      have hl : raw42093step0Labels = labelEmbedding7 ∘ raw42093step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42093step0 raw42093step0Labels raw42093step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical42094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42094 raw42094Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw42094 raw42094Labels = mixedMoment B raw42094step0 raw42094step0Labels := by
      have ha : raw42094step0 = (fun i j => raw42094 (permutation203 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42094step0 raw42094; decide +kernel
      have hl : raw42094step0Labels = raw42094Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42094 raw42094Labels permutation203 permutation4
    mixedMoment B raw42094step0 raw42094step0Labels = mixedMoment B raw42094step1 raw42094step1Labels := by
      have ha : raw42094step1 = -raw42094step0 := by apply Matrix.ext; change ∀ i j, raw42094step1 i j = -(raw42094step0 i j); unfold raw42094step1 raw42094step0; decide +kernel
      have hl : raw42094step1Labels = raw42094step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42094step1 raw42094step1Labels = mixedMoment B raw42094step2 raw42094step2Labels := by
      have ha : raw42094step2 = raw42094step1 := by apply Matrix.ext; unfold raw42094step2 raw42094step1; decide +kernel
      have hl : raw42094step1Labels = labelEmbedding1 ∘ raw42094step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42094step1 raw42094step1Labels raw42094step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

theorem canonical42095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42095 raw42095Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw42095 raw42095Labels = mixedMoment B raw42095step0 raw42095step0Labels := by
      have ha : raw42095step0 = (fun i j => raw42095 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42095step0 raw42095; decide +kernel
      have hl : raw42095step0Labels = raw42095Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42095 raw42095Labels permutation152 permutation3
    mixedMoment B raw42095step0 raw42095step0Labels = mixedMoment B raw42095step1 raw42095step1Labels := by
      have ha : raw42095step1 = raw42095step0 := by apply Matrix.ext; unfold raw42095step1 raw42095step0; decide +kernel
      have hl : raw42095step0Labels = labelEmbedding7 ∘ raw42095step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42095step0 raw42095step0Labels raw42095step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical42096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42096 raw42096Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw42096 raw42096Labels = mixedMoment B raw42096step0 raw42096step0Labels := by
      have ha : raw42096step0 = (fun i j => raw42096 (permutation423 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42096step0 raw42096; decide +kernel
      have hl : raw42096step0Labels = raw42096Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42096 raw42096Labels permutation423 permutation4
    mixedMoment B raw42096step0 raw42096step0Labels = mixedMoment B raw42096step1 raw42096step1Labels := by
      have ha : raw42096step1 = raw42096step0 := by apply Matrix.ext; unfold raw42096step1 raw42096step0; decide +kernel
      have hl : raw42096step0Labels = labelEmbedding1 ∘ raw42096step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42096step0 raw42096step0Labels raw42096step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3839 node3839Labels := by rfl

theorem canonical42097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42097 raw42097Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42097 raw42097Labels = mixedMoment B raw42097step0 raw42097step0Labels := by
      have ha : raw42097step0 = (fun i j => raw42097 (permutation423 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42097step0 raw42097; decide +kernel
      have hl : raw42097step0Labels = raw42097Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42097 raw42097Labels permutation423 permutation4
    mixedMoment B raw42097step0 raw42097step0Labels = mixedMoment B raw42097step1 raw42097step1Labels := by
      have ha : raw42097step1 = raw42097step0 := by apply Matrix.ext; unfold raw42097step1 raw42097step0; decide +kernel
      have hl : raw42097step0Labels = labelEmbedding10 ∘ raw42097step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42097step0 raw42097step0Labels raw42097step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical42098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42098 raw42098Labels = mixedMoment B node4027 node4027Labels := by
  calc
    mixedMoment B raw42098 raw42098Labels = mixedMoment B raw42098step0 raw42098step0Labels := by
      have hz : ∀ j, raw42098 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42098step0 = (fun i j => raw42098 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42098step0 raw42098; decide +kernel
      have hl : raw42098step0Labels = raw42098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42098 raw42098Labels permutation434 hz
    mixedMoment B raw42098step0 raw42098step0Labels = mixedMoment B raw42098step1 raw42098step1Labels := by
      have ha : raw42098step1 = raw42098step0 := by apply Matrix.ext; unfold raw42098step1 raw42098step0; decide +kernel
      have hl : raw42098step0Labels = labelEmbedding1 ∘ raw42098step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42098step0 raw42098step0Labels raw42098step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4027 node4027Labels := by rfl

theorem canonical42099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42099 raw42099Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw42099 raw42099Labels = mixedMoment B raw42099step0 raw42099step0Labels := by
      have hz : ∀ j, raw42099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42099step0 = (fun i j => raw42099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42099step0 raw42099; decide +kernel
      have hl : raw42099step0Labels = raw42099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42099 raw42099Labels permutation434 hz
    mixedMoment B raw42099step0 raw42099step0Labels = mixedMoment B raw42099step1 raw42099step1Labels := by
      have ha : raw42099step1 = (fun i j => raw42099step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42099step1 raw42099step0; decide +kernel
      have hl : raw42099step1Labels = raw42099step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42099step0 raw42099step0Labels permutation151 permutation3
    mixedMoment B raw42099step1 raw42099step1Labels = mixedMoment B raw42099step2 raw42099step2Labels := by
      have ha : raw42099step2 = -raw42099step1 := by apply Matrix.ext; change ∀ i j, raw42099step2 i j = -(raw42099step1 i j); unfold raw42099step2 raw42099step1; decide +kernel
      have hl : raw42099step2Labels = raw42099step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42099step2 raw42099step2Labels = mixedMoment B raw42099step3 raw42099step3Labels := by
      have ha : raw42099step3 = raw42099step2 := by apply Matrix.ext; unfold raw42099step3 raw42099step2; decide +kernel
      have hl : raw42099step2Labels = labelEmbedding7 ∘ raw42099step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42099step2 raw42099step2Labels raw42099step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical42100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42100 raw42100Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw42100 raw42100Labels = mixedMoment B raw42100step0 raw42100step0Labels := by
      have hz : ∀ j, raw42100 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42100step0 = (fun i j => raw42100 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42100step0 raw42100; decide +kernel
      have hl : raw42100step0Labels = raw42100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42100 raw42100Labels permutation434 hz
    mixedMoment B raw42100step0 raw42100step0Labels = mixedMoment B raw42100step1 raw42100step1Labels := by
      have ha : raw42100step1 = (fun i j => raw42100step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42100step1 raw42100step0; decide +kernel
      have hl : raw42100step1Labels = raw42100step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42100step0 raw42100step0Labels permutation151 permutation2
    mixedMoment B raw42100step1 raw42100step1Labels = mixedMoment B raw42100step2 raw42100step2Labels := by
      have ha : raw42100step2 = -raw42100step1 := by apply Matrix.ext; change ∀ i j, raw42100step2 i j = -(raw42100step1 i j); unfold raw42100step2 raw42100step1; decide +kernel
      have hl : raw42100step2Labels = raw42100step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42100step2 raw42100step2Labels = mixedMoment B raw42100step3 raw42100step3Labels := by
      have ha : raw42100step3 = raw42100step2 := by apply Matrix.ext; unfold raw42100step3 raw42100step2; decide +kernel
      have hl : raw42100step2Labels = labelEmbedding1 ∘ raw42100step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42100step2 raw42100step2Labels raw42100step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

theorem canonical42101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42101 raw42101Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw42101 raw42101Labels = mixedMoment B raw42101step0 raw42101step0Labels := by
      have hz : ∀ j, raw42101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42101step0 = (fun i j => raw42101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42101step0 raw42101; decide +kernel
      have hl : raw42101step0Labels = raw42101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42101 raw42101Labels permutation434 hz
    mixedMoment B raw42101step0 raw42101step0Labels = mixedMoment B raw42101step1 raw42101step1Labels := by
      have ha : raw42101step1 = (fun i j => raw42101step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42101step1 raw42101step0; decide +kernel
      have hl : raw42101step1Labels = raw42101step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42101step0 raw42101step0Labels permutation38 permutation5
    mixedMoment B raw42101step1 raw42101step1Labels = mixedMoment B raw42101step2 raw42101step2Labels := by
      have ha : raw42101step2 = -raw42101step1 := by apply Matrix.ext; change ∀ i j, raw42101step2 i j = -(raw42101step1 i j); unfold raw42101step2 raw42101step1; decide +kernel
      have hl : raw42101step2Labels = raw42101step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42101step2 raw42101step2Labels = mixedMoment B raw42101step3 raw42101step3Labels := by
      have ha : raw42101step3 = raw42101step2 := by apply Matrix.ext; unfold raw42101step3 raw42101step2; decide +kernel
      have hl : raw42101step2Labels = labelEmbedding9 ∘ raw42101step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42101step2 raw42101step2Labels raw42101step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical42102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42102 raw42102Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw42102 raw42102Labels = mixedMoment B raw42102step0 raw42102step0Labels := by
      have hz : ∀ j, raw42102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42102step0 = (fun i j => raw42102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42102step0 raw42102; decide +kernel
      have hl : raw42102step0Labels = raw42102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42102 raw42102Labels permutation434 hz
    mixedMoment B raw42102step0 raw42102step0Labels = mixedMoment B raw42102step1 raw42102step1Labels := by
      have ha : raw42102step1 = (fun i j => raw42102step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42102step1 raw42102step0; decide +kernel
      have hl : raw42102step1Labels = raw42102step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42102step0 raw42102step0Labels permutation151 permutation2
    mixedMoment B raw42102step1 raw42102step1Labels = mixedMoment B raw42102step2 raw42102step2Labels := by
      have ha : raw42102step2 = -raw42102step1 := by apply Matrix.ext; change ∀ i j, raw42102step2 i j = -(raw42102step1 i j); unfold raw42102step2 raw42102step1; decide +kernel
      have hl : raw42102step2Labels = raw42102step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42102step2 raw42102step2Labels = mixedMoment B raw42102step3 raw42102step3Labels := by
      have ha : raw42102step3 = raw42102step2 := by apply Matrix.ext; unfold raw42102step3 raw42102step2; decide +kernel
      have hl : raw42102step2Labels = labelEmbedding1 ∘ raw42102step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42102step2 raw42102step2Labels raw42102step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

theorem canonical42103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42103 raw42103Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw42103 raw42103Labels = mixedMoment B raw42103step0 raw42103step0Labels := by
      have hz : ∀ j, raw42103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42103step0 = (fun i j => raw42103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42103step0 raw42103; decide +kernel
      have hl : raw42103step0Labels = raw42103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42103 raw42103Labels permutation434 hz
    mixedMoment B raw42103step0 raw42103step0Labels = mixedMoment B raw42103step1 raw42103step1Labels := by
      have ha : raw42103step1 = (fun i j => raw42103step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42103step1 raw42103step0; decide +kernel
      have hl : raw42103step1Labels = raw42103step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42103step0 raw42103step0Labels permutation42 permutation5
    mixedMoment B raw42103step1 raw42103step1Labels = mixedMoment B raw42103step2 raw42103step2Labels := by
      have ha : raw42103step2 = -raw42103step1 := by apply Matrix.ext; change ∀ i j, raw42103step2 i j = -(raw42103step1 i j); unfold raw42103step2 raw42103step1; decide +kernel
      have hl : raw42103step2Labels = raw42103step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42103step2 raw42103step2Labels = mixedMoment B raw42103step3 raw42103step3Labels := by
      have ha : raw42103step3 = raw42103step2 := by apply Matrix.ext; unfold raw42103step3 raw42103step2; decide +kernel
      have hl : raw42103step2Labels = labelEmbedding9 ∘ raw42103step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42103step2 raw42103step2Labels raw42103step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

theorem canonical42104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42104 raw42104Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw42104 raw42104Labels = mixedMoment B raw42104step0 raw42104step0Labels := by
      have ha : raw42104step0 = (fun i j => raw42104 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42104step0 raw42104; decide +kernel
      have hl : raw42104step0Labels = raw42104Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42104 raw42104Labels permutation682 permutation2
    mixedMoment B raw42104step0 raw42104step0Labels = mixedMoment B raw42104step1 raw42104step1Labels := by
      have ha : raw42104step1 = -raw42104step0 := by apply Matrix.ext; change ∀ i j, raw42104step1 i j = -(raw42104step0 i j); unfold raw42104step1 raw42104step0; decide +kernel
      have hl : raw42104step1Labels = raw42104step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42104step1 raw42104step1Labels = mixedMoment B raw42104step2 raw42104step2Labels := by
      have ha : raw42104step2 = raw42104step1 := by apply Matrix.ext; unfold raw42104step2 raw42104step1; decide +kernel
      have hl : raw42104step1Labels = labelEmbedding1 ∘ raw42104step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42104step1 raw42104step1Labels raw42104step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3839 node3839Labels := by rfl

theorem canonical42105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42105 raw42105Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42105 raw42105Labels = mixedMoment B raw42105step0 raw42105step0Labels := by
      have ha : raw42105step0 = (fun i j => raw42105 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42105step0 raw42105; decide +kernel
      have hl : raw42105step0Labels = raw42105Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42105 raw42105Labels permutation682 permutation2
    mixedMoment B raw42105step0 raw42105step0Labels = mixedMoment B raw42105step1 raw42105step1Labels := by
      have ha : raw42105step1 = -raw42105step0 := by apply Matrix.ext; change ∀ i j, raw42105step1 i j = -(raw42105step0 i j); unfold raw42105step1 raw42105step0; decide +kernel
      have hl : raw42105step1Labels = raw42105step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42105step1 raw42105step1Labels = mixedMoment B raw42105step2 raw42105step2Labels := by
      have ha : raw42105step2 = raw42105step1 := by apply Matrix.ext; unfold raw42105step2 raw42105step1; decide +kernel
      have hl : raw42105step1Labels = labelEmbedding8 ∘ raw42105step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42105step1 raw42105step1Labels raw42105step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical42106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42106 raw42106Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw42106 raw42106Labels = mixedMoment B raw42106step0 raw42106step0Labels := by
      have ha : raw42106step0 = (fun i j => raw42106 (permutation616 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42106step0 raw42106; decide +kernel
      have hl : raw42106step0Labels = raw42106Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42106 raw42106Labels permutation616 permutation4
    mixedMoment B raw42106step0 raw42106step0Labels = mixedMoment B raw42106step1 raw42106step1Labels := by
      have ha : raw42106step1 = raw42106step0 := by apply Matrix.ext; unfold raw42106step1 raw42106step0; decide +kernel
      have hl : raw42106step0Labels = labelEmbedding1 ∘ raw42106step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42106step0 raw42106step0Labels raw42106step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3954 node3954Labels := by rfl

theorem canonical42107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42107 raw42107Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42107 raw42107Labels = mixedMoment B raw42107step0 raw42107step0Labels := by
      have ha : raw42107step0 = (fun i j => raw42107 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42107step0 raw42107; decide +kernel
      have hl : raw42107step0Labels = raw42107Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42107 raw42107Labels permutation184 permutation5
    mixedMoment B raw42107step0 raw42107step0Labels = mixedMoment B raw42107step1 raw42107step1Labels := by
      have ha : raw42107step1 = -raw42107step0 := by apply Matrix.ext; change ∀ i j, raw42107step1 i j = -(raw42107step0 i j); unfold raw42107step1 raw42107step0; decide +kernel
      have hl : raw42107step1Labels = raw42107step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42107step1 raw42107step1Labels = mixedMoment B raw42107step2 raw42107step2Labels := by
      have ha : raw42107step2 = raw42107step1 := by apply Matrix.ext; unfold raw42107step2 raw42107step1; decide +kernel
      have hl : raw42107step1Labels = labelEmbedding9 ∘ raw42107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42107step1 raw42107step1Labels raw42107step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical42108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42108 raw42108Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw42108 raw42108Labels = mixedMoment B raw42108step0 raw42108step0Labels := by
      have ha : raw42108step0 = (fun i j => raw42108 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42108step0 raw42108; decide +kernel
      have hl : raw42108step0Labels = raw42108Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42108 raw42108Labels permutation155 permutation2
    mixedMoment B raw42108step0 raw42108step0Labels = mixedMoment B raw42108step1 raw42108step1Labels := by
      have ha : raw42108step1 = raw42108step0 := by apply Matrix.ext; unfold raw42108step1 raw42108step0; decide +kernel
      have hl : raw42108step0Labels = labelEmbedding1 ∘ raw42108step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42108step0 raw42108step0Labels raw42108step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

theorem canonical42109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42109 raw42109Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw42109 raw42109Labels = mixedMoment B raw42109step0 raw42109step0Labels := by
      have ha : raw42109step0 = (fun i j => raw42109 (permutation182 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42109step0 raw42109; decide +kernel
      have hl : raw42109step0Labels = raw42109Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42109 raw42109Labels permutation182 permutation5
    mixedMoment B raw42109step0 raw42109step0Labels = mixedMoment B raw42109step1 raw42109step1Labels := by
      have ha : raw42109step1 = -raw42109step0 := by apply Matrix.ext; change ∀ i j, raw42109step1 i j = -(raw42109step0 i j); unfold raw42109step1 raw42109step0; decide +kernel
      have hl : raw42109step1Labels = raw42109step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42109step1 raw42109step1Labels = mixedMoment B raw42109step2 raw42109step2Labels := by
      have ha : raw42109step2 = raw42109step1 := by apply Matrix.ext; unfold raw42109step2 raw42109step1; decide +kernel
      have hl : raw42109step1Labels = labelEmbedding9 ∘ raw42109step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42109step1 raw42109step1Labels raw42109step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical42110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42110 raw42110Labels = mixedMoment B node4030 node4030Labels := by
  calc
    mixedMoment B raw42110 raw42110Labels = mixedMoment B raw42110step0 raw42110step0Labels := by
      have hz : ∀ j, raw42110 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42110step0 = (fun i j => raw42110 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42110step0 raw42110; decide +kernel
      have hl : raw42110step0Labels = raw42110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42110 raw42110Labels permutation434 hz
    mixedMoment B raw42110step0 raw42110step0Labels = mixedMoment B raw42110step1 raw42110step1Labels := by
      have hz : ∀ j, raw42110step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42110step1 = (fun i j => raw42110step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42110step1 raw42110step0; decide +kernel
      have hl : raw42110step1Labels = raw42110step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42110step0 raw42110step0Labels permutation80 hz
    mixedMoment B raw42110step1 raw42110step1Labels = mixedMoment B raw42110step2 raw42110step2Labels := by
      have ha : raw42110step2 = raw42110step1 := by apply Matrix.ext; unfold raw42110step2 raw42110step1; decide +kernel
      have hl : raw42110step1Labels = labelEmbedding1 ∘ raw42110step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42110step1 raw42110step1Labels raw42110step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4030 node4030Labels := by rfl

theorem canonical42111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42111 raw42111Labels = mixedMoment B node5449 node5449Labels := by
  calc
    mixedMoment B raw42111 raw42111Labels = mixedMoment B raw42111step0 raw42111step0Labels := by
      have hz : ∀ j, raw42111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42111step0 = (fun i j => raw42111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42111step0 raw42111; decide +kernel
      have hl : raw42111step0Labels = raw42111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42111 raw42111Labels permutation434 hz
    mixedMoment B raw42111step0 raw42111step0Labels = mixedMoment B raw42111step1 raw42111step1Labels := by
      have hz : ∀ j, raw42111step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42111step1 = (fun i j => raw42111step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42111step1 raw42111step0; decide +kernel
      have hl : raw42111step1Labels = raw42111step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42111step0 raw42111step0Labels permutation80 hz
    mixedMoment B raw42111step1 raw42111step1Labels = mixedMoment B raw42111step2 raw42111step2Labels := by
      have ha : raw42111step2 = (fun i j => raw42111step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42111step2 raw42111step1; decide +kernel
      have hl : raw42111step2Labels = raw42111step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42111step1 raw42111step1Labels permutation8 permutation3
    mixedMoment B raw42111step2 raw42111step2Labels = mixedMoment B raw42111step3 raw42111step3Labels := by
      have ha : raw42111step3 = raw42111step2 := by apply Matrix.ext; unfold raw42111step3 raw42111step2; decide +kernel
      have hl : raw42111step2Labels = labelEmbedding7 ∘ raw42111step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42111step2 raw42111step2Labels raw42111step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5449 node5449Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2368) =
      Integer.Sparse.eval keyMomentRow2368 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2368).leftCharge (GramAssembly.key 2368).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4038) := by
    have ha : gramCharges (GramAssembly.key 2368).leftCharge (GramAssembly.key 2368).rightCharge = raw42048 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42048Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42048 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2368).leftCharge (GramAssembly.key 2368).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5408) := by
    have ha : gramCharges (GramAssembly.key 2368).leftCharge (GramAssembly.key 2368).rightCharge = raw42049 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42049Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42049 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2368).leftCharge (GramAssembly.key 2368).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2368).leftCharge (GramAssembly.key 2368).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2368, Integer.Sparse.eval] <;> ring

theorem keyMoment2369 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2369) =
      Integer.Sparse.eval keyMomentRow2369 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2369).leftCharge (GramAssembly.key 2369).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3847) := by
    have ha : gramCharges (GramAssembly.key 2369).leftCharge (GramAssembly.key 2369).rightCharge = raw42050 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42050Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42050 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2369).leftCharge (GramAssembly.key 2369).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5406) := by
    have ha : gramCharges (GramAssembly.key 2369).leftCharge (GramAssembly.key 2369).rightCharge = raw42051 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42051Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42051 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2369).leftCharge (GramAssembly.key 2369).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2369).leftCharge (GramAssembly.key 2369).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2369, Integer.Sparse.eval] <;> ring

theorem keyMoment2370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2370) =
      Integer.Sparse.eval keyMomentRow2370 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2370).leftCharge (GramAssembly.key 2370).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3230) := by
    have ha : gramCharges (GramAssembly.key 2370).leftCharge (GramAssembly.key 2370).rightCharge = raw42052 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42052Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42052 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2370).leftCharge (GramAssembly.key 2370).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4894) := by
    have ha : gramCharges (GramAssembly.key 2370).leftCharge (GramAssembly.key 2370).rightCharge = raw42053 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42053Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42053 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2370).leftCharge (GramAssembly.key 2370).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2370).leftCharge (GramAssembly.key 2370).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2370, Integer.Sparse.eval] <;> ring

theorem keyMoment2371 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2371) =
      Integer.Sparse.eval keyMomentRow2371 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2371).leftCharge (GramAssembly.key 2371).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3089) := by
    have ha : gramCharges (GramAssembly.key 2371).leftCharge (GramAssembly.key 2371).rightCharge = raw42054 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42054Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42054 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2371).leftCharge (GramAssembly.key 2371).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5258) := by
    have ha : gramCharges (GramAssembly.key 2371).leftCharge (GramAssembly.key 2371).rightCharge = raw42055 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42055Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42055 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2371).leftCharge (GramAssembly.key 2371).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2371).leftCharge (GramAssembly.key 2371).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2371, Integer.Sparse.eval] <;> ring

theorem keyMoment2372 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2372) =
      Integer.Sparse.eval keyMomentRow2372 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2372).leftCharge (GramAssembly.key 2372).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4035) := by
    have ha : gramCharges (GramAssembly.key 2372).leftCharge (GramAssembly.key 2372).rightCharge = raw42056 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42056Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42056 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2372).leftCharge (GramAssembly.key 2372).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5409) := by
    have ha : gramCharges (GramAssembly.key 2372).leftCharge (GramAssembly.key 2372).rightCharge = raw42057 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42057Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42057 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2372).leftCharge (GramAssembly.key 2372).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2372).leftCharge (GramAssembly.key 2372).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2372, Integer.Sparse.eval] <;> ring

theorem keyMoment2373 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2373) =
      Integer.Sparse.eval keyMomentRow2373 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2373).leftCharge (GramAssembly.key 2373).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4003) := by
    have ha : gramCharges (GramAssembly.key 2373).leftCharge (GramAssembly.key 2373).rightCharge = raw42058 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42058Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42058 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2373).leftCharge (GramAssembly.key 2373).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5428) := by
    have ha : gramCharges (GramAssembly.key 2373).leftCharge (GramAssembly.key 2373).rightCharge = raw42059 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42059Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42059 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2373).leftCharge (GramAssembly.key 2373).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2373).leftCharge (GramAssembly.key 2373).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2373, Integer.Sparse.eval] <;> ring

theorem keyMoment2374 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2374) =
      Integer.Sparse.eval keyMomentRow2374 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2374).leftCharge (GramAssembly.key 2374).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2732) := by
    have ha : gramCharges (GramAssembly.key 2374).leftCharge (GramAssembly.key 2374).rightCharge = raw42060 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42060Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42060 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2374).leftCharge (GramAssembly.key 2374).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2374).leftCharge (GramAssembly.key 2374).rightCharge = raw42061 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42061Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42061 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2374).leftCharge (GramAssembly.key 2374).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2374).leftCharge (GramAssembly.key 2374).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2374, Integer.Sparse.eval] <;> ring

theorem keyMoment2375 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2375) =
      Integer.Sparse.eval keyMomentRow2375 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2375).leftCharge (GramAssembly.key 2375).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4032) := by
    have ha : gramCharges (GramAssembly.key 2375).leftCharge (GramAssembly.key 2375).rightCharge = raw42062 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42062Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42062 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2375).leftCharge (GramAssembly.key 2375).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5423) := by
    have ha : gramCharges (GramAssembly.key 2375).leftCharge (GramAssembly.key 2375).rightCharge = raw42063 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42063Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42063 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2375).leftCharge (GramAssembly.key 2375).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2375).leftCharge (GramAssembly.key 2375).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2375, Integer.Sparse.eval] <;> ring

theorem keyMoment2376 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2376) =
      Integer.Sparse.eval keyMomentRow2376 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2376).leftCharge (GramAssembly.key 2376).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3990) := by
    have ha : gramCharges (GramAssembly.key 2376).leftCharge (GramAssembly.key 2376).rightCharge = raw42064 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42064Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42064 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2376).leftCharge (GramAssembly.key 2376).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5424) := by
    have ha : gramCharges (GramAssembly.key 2376).leftCharge (GramAssembly.key 2376).rightCharge = raw42065 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42065Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42065 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2376).leftCharge (GramAssembly.key 2376).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2376).leftCharge (GramAssembly.key 2376).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2376, Integer.Sparse.eval] <;> ring

theorem keyMoment2377 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2377) =
      Integer.Sparse.eval keyMomentRow2377 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2377).leftCharge (GramAssembly.key 2377).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3872) := by
    have ha : gramCharges (GramAssembly.key 2377).leftCharge (GramAssembly.key 2377).rightCharge = raw42066 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42066Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42066 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2377).leftCharge (GramAssembly.key 2377).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2377).leftCharge (GramAssembly.key 2377).rightCharge = raw42067 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42067Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42067 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2377).leftCharge (GramAssembly.key 2377).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2377).leftCharge (GramAssembly.key 2377).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2377, Integer.Sparse.eval] <;> ring

theorem keyMoment2378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2378) =
      Integer.Sparse.eval keyMomentRow2378 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2378).leftCharge (GramAssembly.key 2378).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3841) := by
    have ha : gramCharges (GramAssembly.key 2378).leftCharge (GramAssembly.key 2378).rightCharge = raw42068 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42068Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42068 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2378).leftCharge (GramAssembly.key 2378).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5426) := by
    have ha : gramCharges (GramAssembly.key 2378).leftCharge (GramAssembly.key 2378).rightCharge = raw42069 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42069Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42069 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2378).leftCharge (GramAssembly.key 2378).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2378).leftCharge (GramAssembly.key 2378).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2378, Integer.Sparse.eval] <;> ring

theorem keyMoment2379 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2379) =
      Integer.Sparse.eval keyMomentRow2379 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2379).leftCharge (GramAssembly.key 2379).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2710) := by
    have ha : gramCharges (GramAssembly.key 2379).leftCharge (GramAssembly.key 2379).rightCharge = raw42070 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42070Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42070 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2379).leftCharge (GramAssembly.key 2379).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2379).leftCharge (GramAssembly.key 2379).rightCharge = raw42071 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42071Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42071 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2379).leftCharge (GramAssembly.key 2379).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2379).leftCharge (GramAssembly.key 2379).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2379, Integer.Sparse.eval] <;> ring

theorem keyMoment2380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2380) =
      Integer.Sparse.eval keyMomentRow2380 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2380).leftCharge (GramAssembly.key 2380).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3990) := by
    have ha : gramCharges (GramAssembly.key 2380).leftCharge (GramAssembly.key 2380).rightCharge = raw42072 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42072Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42072 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2380).leftCharge (GramAssembly.key 2380).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5424) := by
    have ha : gramCharges (GramAssembly.key 2380).leftCharge (GramAssembly.key 2380).rightCharge = raw42073 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42073Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42073 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2380).leftCharge (GramAssembly.key 2380).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2380).leftCharge (GramAssembly.key 2380).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2380, Integer.Sparse.eval] <;> ring

theorem keyMoment2381 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2381) =
      Integer.Sparse.eval keyMomentRow2381 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2381).leftCharge (GramAssembly.key 2381).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4034) := by
    have ha : gramCharges (GramAssembly.key 2381).leftCharge (GramAssembly.key 2381).rightCharge = raw42074 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42074Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42074 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2381).leftCharge (GramAssembly.key 2381).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5427) := by
    have ha : gramCharges (GramAssembly.key 2381).leftCharge (GramAssembly.key 2381).rightCharge = raw42075 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42075Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42075 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2381).leftCharge (GramAssembly.key 2381).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2381).leftCharge (GramAssembly.key 2381).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2381, Integer.Sparse.eval] <;> ring

theorem keyMoment2382 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2382) =
      Integer.Sparse.eval keyMomentRow2382 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2382).leftCharge (GramAssembly.key 2382).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3103) := by
    have ha : gramCharges (GramAssembly.key 2382).leftCharge (GramAssembly.key 2382).rightCharge = raw42076 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42076Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42076 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2382).leftCharge (GramAssembly.key 2382).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5291) := by
    have ha : gramCharges (GramAssembly.key 2382).leftCharge (GramAssembly.key 2382).rightCharge = raw42077 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42077Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42077 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2382).leftCharge (GramAssembly.key 2382).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2382).leftCharge (GramAssembly.key 2382).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2382, Integer.Sparse.eval] <;> ring

theorem keyMoment2383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2383) =
      Integer.Sparse.eval keyMomentRow2383 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2383).leftCharge (GramAssembly.key 2383).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2744) := by
    have ha : gramCharges (GramAssembly.key 2383).leftCharge (GramAssembly.key 2383).rightCharge = raw42078 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42078Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42078 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2383).leftCharge (GramAssembly.key 2383).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5276) := by
    have ha : gramCharges (GramAssembly.key 2383).leftCharge (GramAssembly.key 2383).rightCharge = raw42079 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42079Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42079 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2383).leftCharge (GramAssembly.key 2383).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2383).leftCharge (GramAssembly.key 2383).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2383, Integer.Sparse.eval] <;> ring

theorem keyMoment2384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2384) =
      Integer.Sparse.eval keyMomentRow2384 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2384).leftCharge (GramAssembly.key 2384).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4027) := by
    have ha : gramCharges (GramAssembly.key 2384).leftCharge (GramAssembly.key 2384).rightCharge = raw42080 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42080Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42080 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2384).leftCharge (GramAssembly.key 2384).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5432) := by
    have ha : gramCharges (GramAssembly.key 2384).leftCharge (GramAssembly.key 2384).rightCharge = raw42081 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42081Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42081 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2384).leftCharge (GramAssembly.key 2384).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2384).leftCharge (GramAssembly.key 2384).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2384, Integer.Sparse.eval] <;> ring

theorem keyMoment2385 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2385) =
      Integer.Sparse.eval keyMomentRow2385 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2385).leftCharge (GramAssembly.key 2385).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3573) := by
    have ha : gramCharges (GramAssembly.key 2385).leftCharge (GramAssembly.key 2385).rightCharge = raw42082 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42082Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42082 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2385).leftCharge (GramAssembly.key 2385).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2385).leftCharge (GramAssembly.key 2385).rightCharge = raw42083 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42083Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42083 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2385).leftCharge (GramAssembly.key 2385).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2385).leftCharge (GramAssembly.key 2385).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2385, Integer.Sparse.eval] <;> ring

theorem keyMoment2386 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2386) =
      Integer.Sparse.eval keyMomentRow2386 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2386).leftCharge (GramAssembly.key 2386).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3541) := by
    have ha : gramCharges (GramAssembly.key 2386).leftCharge (GramAssembly.key 2386).rightCharge = raw42084 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42084Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42084 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2386).leftCharge (GramAssembly.key 2386).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2386).leftCharge (GramAssembly.key 2386).rightCharge = raw42085 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42085Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42085 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2386).leftCharge (GramAssembly.key 2386).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2386).leftCharge (GramAssembly.key 2386).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2386, Integer.Sparse.eval] <;> ring

theorem keyMoment2387 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2387) =
      Integer.Sparse.eval keyMomentRow2387 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2387).leftCharge (GramAssembly.key 2387).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2724) := by
    have ha : gramCharges (GramAssembly.key 2387).leftCharge (GramAssembly.key 2387).rightCharge = raw42086 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42086Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42086 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2387).leftCharge (GramAssembly.key 2387).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2387).leftCharge (GramAssembly.key 2387).rightCharge = raw42087 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42087Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42087 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2387).leftCharge (GramAssembly.key 2387).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2387).leftCharge (GramAssembly.key 2387).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2387, Integer.Sparse.eval] <;> ring

theorem keyMoment2388 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2388) =
      Integer.Sparse.eval keyMomentRow2388 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2388).leftCharge (GramAssembly.key 2388).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3993) := by
    have ha : gramCharges (GramAssembly.key 2388).leftCharge (GramAssembly.key 2388).rightCharge = raw42088 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42088Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42088 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2388).leftCharge (GramAssembly.key 2388).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5438) := by
    have ha : gramCharges (GramAssembly.key 2388).leftCharge (GramAssembly.key 2388).rightCharge = raw42089 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42089Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42089 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2388).leftCharge (GramAssembly.key 2388).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2388).leftCharge (GramAssembly.key 2388).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2388, Integer.Sparse.eval] <;> ring

theorem keyMoment2389 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2389) =
      Integer.Sparse.eval keyMomentRow2389 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2389).leftCharge (GramAssembly.key 2389).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3526) := by
    have ha : gramCharges (GramAssembly.key 2389).leftCharge (GramAssembly.key 2389).rightCharge = raw42090 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42090Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42090 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2389).leftCharge (GramAssembly.key 2389).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2389).leftCharge (GramAssembly.key 2389).rightCharge = raw42091 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42091Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42091 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2389).leftCharge (GramAssembly.key 2389).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2389).leftCharge (GramAssembly.key 2389).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2389, Integer.Sparse.eval] <;> ring

theorem keyMoment2390 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2390) =
      Integer.Sparse.eval keyMomentRow2390 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2390).leftCharge (GramAssembly.key 2390).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3972) := by
    have ha : gramCharges (GramAssembly.key 2390).leftCharge (GramAssembly.key 2390).rightCharge = raw42092 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42092Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42092 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2390).leftCharge (GramAssembly.key 2390).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2390).leftCharge (GramAssembly.key 2390).rightCharge = raw42093 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42093Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42093 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2390).leftCharge (GramAssembly.key 2390).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2390).leftCharge (GramAssembly.key 2390).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2390, Integer.Sparse.eval] <;> ring

theorem keyMoment2391 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2391) =
      Integer.Sparse.eval keyMomentRow2391 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2391).leftCharge (GramAssembly.key 2391).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4026) := by
    have ha : gramCharges (GramAssembly.key 2391).leftCharge (GramAssembly.key 2391).rightCharge = raw42094 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42094Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42094 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2391).leftCharge (GramAssembly.key 2391).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5431) := by
    have ha : gramCharges (GramAssembly.key 2391).leftCharge (GramAssembly.key 2391).rightCharge = raw42095 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42095Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42095 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2391).leftCharge (GramAssembly.key 2391).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2391).leftCharge (GramAssembly.key 2391).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2391, Integer.Sparse.eval] <;> ring

theorem keyMoment2392 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2392) =
      Integer.Sparse.eval keyMomentRow2392 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2392).leftCharge (GramAssembly.key 2392).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3839) := by
    have ha : gramCharges (GramAssembly.key 2392).leftCharge (GramAssembly.key 2392).rightCharge = raw42096 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42096Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42096 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2392).leftCharge (GramAssembly.key 2392).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2392).leftCharge (GramAssembly.key 2392).rightCharge = raw42097 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42097Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42097 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2392).leftCharge (GramAssembly.key 2392).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2392).leftCharge (GramAssembly.key 2392).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2392, Integer.Sparse.eval] <;> ring

theorem keyMoment2393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2393) =
      Integer.Sparse.eval keyMomentRow2393 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2393).leftCharge (GramAssembly.key 2393).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4027) := by
    have ha : gramCharges (GramAssembly.key 2393).leftCharge (GramAssembly.key 2393).rightCharge = raw42098 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42098Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42098 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2393).leftCharge (GramAssembly.key 2393).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5432) := by
    have ha : gramCharges (GramAssembly.key 2393).leftCharge (GramAssembly.key 2393).rightCharge = raw42099 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42099Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42099 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2393).leftCharge (GramAssembly.key 2393).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2393).leftCharge (GramAssembly.key 2393).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2393, Integer.Sparse.eval] <;> ring

theorem keyMoment2394 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2394) =
      Integer.Sparse.eval keyMomentRow2394 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2394).leftCharge (GramAssembly.key 2394).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3993) := by
    have ha : gramCharges (GramAssembly.key 2394).leftCharge (GramAssembly.key 2394).rightCharge = raw42100 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42100Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42100 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2394).leftCharge (GramAssembly.key 2394).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5438) := by
    have ha : gramCharges (GramAssembly.key 2394).leftCharge (GramAssembly.key 2394).rightCharge = raw42101 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42101Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42101 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2394).leftCharge (GramAssembly.key 2394).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2394).leftCharge (GramAssembly.key 2394).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2394, Integer.Sparse.eval] <;> ring

theorem keyMoment2395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2395) =
      Integer.Sparse.eval keyMomentRow2395 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2395).leftCharge (GramAssembly.key 2395).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3877) := by
    have ha : gramCharges (GramAssembly.key 2395).leftCharge (GramAssembly.key 2395).rightCharge = raw42102 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42102Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42102 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2395).leftCharge (GramAssembly.key 2395).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5436) := by
    have ha : gramCharges (GramAssembly.key 2395).leftCharge (GramAssembly.key 2395).rightCharge = raw42103 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42103Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42103 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2395).leftCharge (GramAssembly.key 2395).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2395).leftCharge (GramAssembly.key 2395).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2395, Integer.Sparse.eval] <;> ring

theorem keyMoment2396 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2396) =
      Integer.Sparse.eval keyMomentRow2396 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2396).leftCharge (GramAssembly.key 2396).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3839) := by
    have ha : gramCharges (GramAssembly.key 2396).leftCharge (GramAssembly.key 2396).rightCharge = raw42104 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42104Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42104 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2396).leftCharge (GramAssembly.key 2396).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2396).leftCharge (GramAssembly.key 2396).rightCharge = raw42105 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42105Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42105 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2396).leftCharge (GramAssembly.key 2396).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2396).leftCharge (GramAssembly.key 2396).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2396, Integer.Sparse.eval] <;> ring

theorem keyMoment2397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2397) =
      Integer.Sparse.eval keyMomentRow2397 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2397).leftCharge (GramAssembly.key 2397).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3954) := by
    have ha : gramCharges (GramAssembly.key 2397).leftCharge (GramAssembly.key 2397).rightCharge = raw42106 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42106Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42106 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2397).leftCharge (GramAssembly.key 2397).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2397).leftCharge (GramAssembly.key 2397).rightCharge = raw42107 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42107Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42107 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2397).leftCharge (GramAssembly.key 2397).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2397).leftCharge (GramAssembly.key 2397).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2397, Integer.Sparse.eval] <;> ring

theorem keyMoment2398 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2398) =
      Integer.Sparse.eval keyMomentRow2398 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2398).leftCharge (GramAssembly.key 2398).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4026) := by
    have ha : gramCharges (GramAssembly.key 2398).leftCharge (GramAssembly.key 2398).rightCharge = raw42108 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42108Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42108 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2398).leftCharge (GramAssembly.key 2398).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5431) := by
    have ha : gramCharges (GramAssembly.key 2398).leftCharge (GramAssembly.key 2398).rightCharge = raw42109 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42109Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42109 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2398).leftCharge (GramAssembly.key 2398).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2398).leftCharge (GramAssembly.key 2398).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2398, Integer.Sparse.eval] <;> ring

theorem keyMoment2399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2399) =
      Integer.Sparse.eval keyMomentRow2399 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2399).leftCharge (GramAssembly.key 2399).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4030) := by
    have ha : gramCharges (GramAssembly.key 2399).leftCharge (GramAssembly.key 2399).rightCharge = raw42110 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42110Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42110 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2399).leftCharge (GramAssembly.key 2399).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5449) := by
    have ha : gramCharges (GramAssembly.key 2399).leftCharge (GramAssembly.key 2399).rightCharge = raw42111 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42111Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42111 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2399).leftCharge (GramAssembly.key 2399).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2399).leftCharge (GramAssembly.key 2399).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2399, Integer.Sparse.eval] <;> ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2368 : keyMomentRows (2368 : Fin 2886) =
    keyMomentRow2368 := by decide +kernel

theorem keyMomentRowsAt2369 : keyMomentRows (2369 : Fin 2886) =
    keyMomentRow2369 := by decide +kernel

theorem keyMomentRowsAt2370 : keyMomentRows (2370 : Fin 2886) =
    keyMomentRow2370 := by decide +kernel

theorem keyMomentRowsAt2371 : keyMomentRows (2371 : Fin 2886) =
    keyMomentRow2371 := by decide +kernel

theorem keyMomentRowsAt2372 : keyMomentRows (2372 : Fin 2886) =
    keyMomentRow2372 := by decide +kernel

theorem keyMomentRowsAt2373 : keyMomentRows (2373 : Fin 2886) =
    keyMomentRow2373 := by decide +kernel

theorem keyMomentRowsAt2374 : keyMomentRows (2374 : Fin 2886) =
    keyMomentRow2374 := by decide +kernel

theorem keyMomentRowsAt2375 : keyMomentRows (2375 : Fin 2886) =
    keyMomentRow2375 := by decide +kernel

theorem keyMomentRowsAt2376 : keyMomentRows (2376 : Fin 2886) =
    keyMomentRow2376 := by decide +kernel

theorem keyMomentRowsAt2377 : keyMomentRows (2377 : Fin 2886) =
    keyMomentRow2377 := by decide +kernel

theorem keyMomentRowsAt2378 : keyMomentRows (2378 : Fin 2886) =
    keyMomentRow2378 := by decide +kernel

theorem keyMomentRowsAt2379 : keyMomentRows (2379 : Fin 2886) =
    keyMomentRow2379 := by decide +kernel

theorem keyMomentRowsAt2380 : keyMomentRows (2380 : Fin 2886) =
    keyMomentRow2380 := by decide +kernel

theorem keyMomentRowsAt2381 : keyMomentRows (2381 : Fin 2886) =
    keyMomentRow2381 := by decide +kernel

theorem keyMomentRowsAt2382 : keyMomentRows (2382 : Fin 2886) =
    keyMomentRow2382 := by decide +kernel

theorem keyMomentRowsAt2383 : keyMomentRows (2383 : Fin 2886) =
    keyMomentRow2383 := by decide +kernel

theorem keyMomentRowsAt2384 : keyMomentRows (2384 : Fin 2886) =
    keyMomentRow2384 := by decide +kernel

theorem keyMomentRowsAt2385 : keyMomentRows (2385 : Fin 2886) =
    keyMomentRow2385 := by decide +kernel

theorem keyMomentRowsAt2386 : keyMomentRows (2386 : Fin 2886) =
    keyMomentRow2386 := by decide +kernel

theorem keyMomentRowsAt2387 : keyMomentRows (2387 : Fin 2886) =
    keyMomentRow2387 := by decide +kernel

theorem keyMomentRowsAt2388 : keyMomentRows (2388 : Fin 2886) =
    keyMomentRow2388 := by decide +kernel

theorem keyMomentRowsAt2389 : keyMomentRows (2389 : Fin 2886) =
    keyMomentRow2389 := by decide +kernel

theorem keyMomentRowsAt2390 : keyMomentRows (2390 : Fin 2886) =
    keyMomentRow2390 := by decide +kernel

theorem keyMomentRowsAt2391 : keyMomentRows (2391 : Fin 2886) =
    keyMomentRow2391 := by decide +kernel

theorem keyMomentRowsAt2392 : keyMomentRows (2392 : Fin 2886) =
    keyMomentRow2392 := by decide +kernel

theorem keyMomentRowsAt2393 : keyMomentRows (2393 : Fin 2886) =
    keyMomentRow2393 := by decide +kernel

theorem keyMomentRowsAt2394 : keyMomentRows (2394 : Fin 2886) =
    keyMomentRow2394 := by decide +kernel

theorem keyMomentRowsAt2395 : keyMomentRows (2395 : Fin 2886) =
    keyMomentRow2395 := by decide +kernel

theorem keyMomentRowsAt2396 : keyMomentRows (2396 : Fin 2886) =
    keyMomentRow2396 := by decide +kernel

theorem keyMomentRowsAt2397 : keyMomentRows (2397 : Fin 2886) =
    keyMomentRow2397 := by decide +kernel

theorem keyMomentRowsAt2398 : keyMomentRows (2398 : Fin 2886) =
    keyMomentRow2398 := by decide +kernel

theorem keyMomentRowsAt2399 : keyMomentRows (2399 : Fin 2886) =
    keyMomentRow2399 := by decide +kernel

theorem keyMomentChunkSound74_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 74) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2368 ∨ k.val = 2369 ∨ k.val = 2370 ∨ k.val = 2371 ∨ k.val = 2372 ∨ k.val = 2373 ∨ k.val = 2374 ∨ k.val = 2375 ∨ k.val = 2376 ∨ k.val = 2377 ∨ k.val = 2378 ∨ k.val = 2379 ∨ k.val = 2380 ∨ k.val = 2381 ∨ k.val = 2382 ∨ k.val = 2383 ∨ k.val = 2384 ∨ k.val = 2385 ∨ k.val = 2386 ∨ k.val = 2387 ∨ k.val = 2388 ∨ k.val = 2389 ∨ k.val = 2390 ∨ k.val = 2391 ∨ k.val = 2392 ∨ k.val = 2393 ∨ k.val = 2394 ∨ k.val = 2395 ∨ k.val = 2396 ∨ k.val = 2397 ∨ k.val = 2398 ∨ k.val = 2399 := by omega
  rcases heq with h2368 | h2369 | h2370 | h2371 | h2372 | h2373 | h2374 | h2375 | h2376 | h2377 | h2378 | h2379 | h2380 | h2381 | h2382 | h2383 | h2384 | h2385 | h2386 | h2387 | h2388 | h2389 | h2390 | h2391 | h2392 | h2393 | h2394 | h2395 | h2396 | h2397 | h2398 | h2399
  · have he : k = (2368 : Fin 2886) := Fin.ext h2368
    subst k
    rw [keyMomentRowsAt2368]
    exact keyMoment2368 B hB
  · have he : k = (2369 : Fin 2886) := Fin.ext h2369
    subst k
    rw [keyMomentRowsAt2369]
    exact keyMoment2369 B hB
  · have he : k = (2370 : Fin 2886) := Fin.ext h2370
    subst k
    rw [keyMomentRowsAt2370]
    exact keyMoment2370 B hB
  · have he : k = (2371 : Fin 2886) := Fin.ext h2371
    subst k
    rw [keyMomentRowsAt2371]
    exact keyMoment2371 B hB
  · have he : k = (2372 : Fin 2886) := Fin.ext h2372
    subst k
    rw [keyMomentRowsAt2372]
    exact keyMoment2372 B hB
  · have he : k = (2373 : Fin 2886) := Fin.ext h2373
    subst k
    rw [keyMomentRowsAt2373]
    exact keyMoment2373 B hB
  · have he : k = (2374 : Fin 2886) := Fin.ext h2374
    subst k
    rw [keyMomentRowsAt2374]
    exact keyMoment2374 B hB
  · have he : k = (2375 : Fin 2886) := Fin.ext h2375
    subst k
    rw [keyMomentRowsAt2375]
    exact keyMoment2375 B hB
  · have he : k = (2376 : Fin 2886) := Fin.ext h2376
    subst k
    rw [keyMomentRowsAt2376]
    exact keyMoment2376 B hB
  · have he : k = (2377 : Fin 2886) := Fin.ext h2377
    subst k
    rw [keyMomentRowsAt2377]
    exact keyMoment2377 B hB
  · have he : k = (2378 : Fin 2886) := Fin.ext h2378
    subst k
    rw [keyMomentRowsAt2378]
    exact keyMoment2378 B hB
  · have he : k = (2379 : Fin 2886) := Fin.ext h2379
    subst k
    rw [keyMomentRowsAt2379]
    exact keyMoment2379 B hB
  · have he : k = (2380 : Fin 2886) := Fin.ext h2380
    subst k
    rw [keyMomentRowsAt2380]
    exact keyMoment2380 B hB
  · have he : k = (2381 : Fin 2886) := Fin.ext h2381
    subst k
    rw [keyMomentRowsAt2381]
    exact keyMoment2381 B hB
  · have he : k = (2382 : Fin 2886) := Fin.ext h2382
    subst k
    rw [keyMomentRowsAt2382]
    exact keyMoment2382 B hB
  · have he : k = (2383 : Fin 2886) := Fin.ext h2383
    subst k
    rw [keyMomentRowsAt2383]
    exact keyMoment2383 B hB
  · have he : k = (2384 : Fin 2886) := Fin.ext h2384
    subst k
    rw [keyMomentRowsAt2384]
    exact keyMoment2384 B hB
  · have he : k = (2385 : Fin 2886) := Fin.ext h2385
    subst k
    rw [keyMomentRowsAt2385]
    exact keyMoment2385 B hB
  · have he : k = (2386 : Fin 2886) := Fin.ext h2386
    subst k
    rw [keyMomentRowsAt2386]
    exact keyMoment2386 B hB
  · have he : k = (2387 : Fin 2886) := Fin.ext h2387
    subst k
    rw [keyMomentRowsAt2387]
    exact keyMoment2387 B hB
  · have he : k = (2388 : Fin 2886) := Fin.ext h2388
    subst k
    rw [keyMomentRowsAt2388]
    exact keyMoment2388 B hB
  · have he : k = (2389 : Fin 2886) := Fin.ext h2389
    subst k
    rw [keyMomentRowsAt2389]
    exact keyMoment2389 B hB
  · have he : k = (2390 : Fin 2886) := Fin.ext h2390
    subst k
    rw [keyMomentRowsAt2390]
    exact keyMoment2390 B hB
  · have he : k = (2391 : Fin 2886) := Fin.ext h2391
    subst k
    rw [keyMomentRowsAt2391]
    exact keyMoment2391 B hB
  · have he : k = (2392 : Fin 2886) := Fin.ext h2392
    subst k
    rw [keyMomentRowsAt2392]
    exact keyMoment2392 B hB
  · have he : k = (2393 : Fin 2886) := Fin.ext h2393
    subst k
    rw [keyMomentRowsAt2393]
    exact keyMoment2393 B hB
  · have he : k = (2394 : Fin 2886) := Fin.ext h2394
    subst k
    rw [keyMomentRowsAt2394]
    exact keyMoment2394 B hB
  · have he : k = (2395 : Fin 2886) := Fin.ext h2395
    subst k
    rw [keyMomentRowsAt2395]
    exact keyMoment2395 B hB
  · have he : k = (2396 : Fin 2886) := Fin.ext h2396
    subst k
    rw [keyMomentRowsAt2396]
    exact keyMoment2396 B hB
  · have he : k = (2397 : Fin 2886) := Fin.ext h2397
    subst k
    rw [keyMomentRowsAt2397]
    exact keyMoment2397 B hB
  · have he : k = (2398 : Fin 2886) := Fin.ext h2398
    subst k
    rw [keyMomentRowsAt2398]
    exact keyMoment2398 B hB
  · have he : k = (2399 : Fin 2886) := Fin.ext h2399
    subst k
    rw [keyMomentRowsAt2399]
    exact keyMoment2399 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound74_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound74_e_oai
