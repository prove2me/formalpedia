-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound85_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:06:25.624572+00:00
-- url     : https://prove2.me/submissions/b308fcd4-2719-450e-a986-9b44bc624dcc

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical334
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical42752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42752 raw42752Labels = mixedMoment B node3475 node3475Labels := by
  calc
    mixedMoment B raw42752 raw42752Labels = mixedMoment B raw42752step0 raw42752step0Labels := by
      have hz : ∀ j, raw42752 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42752step0 = (fun i j => raw42752 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42752step0 raw42752; decide +kernel
      have hl : raw42752step0Labels = raw42752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42752 raw42752Labels permutation434 hz
    mixedMoment B raw42752step0 raw42752step0Labels = mixedMoment B raw42752step1 raw42752step1Labels := by
      have ha : raw42752step1 = raw42752step0 := by apply Matrix.ext; unfold raw42752step1 raw42752step0; decide +kernel
      have hl : raw42752step0Labels = labelEmbedding1 ∘ raw42752step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42752step0 raw42752step0Labels raw42752step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3475 node3475Labels := by rfl

theorem canonical42753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42753 raw42753Labels = mixedMoment B node4965 node4965Labels := by
  calc
    mixedMoment B raw42753 raw42753Labels = mixedMoment B raw42753step0 raw42753step0Labels := by
      have hz : ∀ j, raw42753 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42753step0 = (fun i j => raw42753 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42753step0 raw42753; decide +kernel
      have hl : raw42753step0Labels = raw42753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42753 raw42753Labels permutation434 hz
    mixedMoment B raw42753step0 raw42753step0Labels = mixedMoment B raw42753step1 raw42753step1Labels := by
      have ha : raw42753step1 = (fun i j => raw42753step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42753step1 raw42753step0; decide +kernel
      have hl : raw42753step1Labels = raw42753step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42753step0 raw42753step0Labels permutation145 permutation7
    mixedMoment B raw42753step1 raw42753step1Labels = mixedMoment B raw42753step2 raw42753step2Labels := by
      have ha : raw42753step2 = raw42753step1 := by apply Matrix.ext; unfold raw42753step2 raw42753step1; decide +kernel
      have hl : raw42753step1Labels = labelEmbedding6 ∘ raw42753step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42753step1 raw42753step1Labels raw42753step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4965 node4965Labels := by rfl

theorem canonical42754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42754 raw42754Labels = mixedMoment B node3452 node3452Labels := by
  calc
    mixedMoment B raw42754 raw42754Labels = mixedMoment B raw42754step0 raw42754step0Labels := by
      have ha : raw42754step0 = (fun i j => raw42754 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42754step0 raw42754; decide +kernel
      have hl : raw42754step0Labels = raw42754Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42754 raw42754Labels permutation158 permutation2
    mixedMoment B raw42754step0 raw42754step0Labels = mixedMoment B raw42754step1 raw42754step1Labels := by
      have ha : raw42754step1 = raw42754step0 := by apply Matrix.ext; unfold raw42754step1 raw42754step0; decide +kernel
      have hl : raw42754step0Labels = labelEmbedding1 ∘ raw42754step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42754step0 raw42754step0Labels raw42754step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3452 node3452Labels := by rfl

theorem canonical42755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42755 raw42755Labels = mixedMoment B node4954 node4954Labels := by
  calc
    mixedMoment B raw42755 raw42755Labels = mixedMoment B raw42755step0 raw42755step0Labels := by
      have ha : raw42755step0 = (fun i j => raw42755 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42755step0 raw42755; decide +kernel
      have hl : raw42755step0Labels = raw42755Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42755 raw42755Labels permutation646 permutation7
    mixedMoment B raw42755step0 raw42755step0Labels = mixedMoment B raw42755step1 raw42755step1Labels := by
      have ha : raw42755step1 = raw42755step0 := by apply Matrix.ext; unfold raw42755step1 raw42755step0; decide +kernel
      have hl : raw42755step0Labels = labelEmbedding6 ∘ raw42755step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42755step0 raw42755step0Labels raw42755step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4954 node4954Labels := by rfl

theorem canonical42756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42756 raw42756Labels = mixedMoment B node3474 node3474Labels := by
  calc
    mixedMoment B raw42756 raw42756Labels = mixedMoment B raw42756step0 raw42756step0Labels := by
      have ha : raw42756step0 = (fun i j => raw42756 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42756step0 raw42756; decide +kernel
      have hl : raw42756step0Labels = raw42756Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42756 raw42756Labels permutation157 permutation2
    mixedMoment B raw42756step0 raw42756step0Labels = mixedMoment B raw42756step1 raw42756step1Labels := by
      have ha : raw42756step1 = raw42756step0 := by apply Matrix.ext; unfold raw42756step1 raw42756step0; decide +kernel
      have hl : raw42756step0Labels = labelEmbedding1 ∘ raw42756step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42756step0 raw42756step0Labels raw42756step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3474 node3474Labels := by rfl

theorem canonical42757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42757 raw42757Labels = mixedMoment B node5044 node5044Labels := by
  calc
    mixedMoment B raw42757 raw42757Labels = mixedMoment B raw42757step0 raw42757step0Labels := by
      have ha : raw42757step0 = (fun i j => raw42757 (permutation174 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42757step0 raw42757; decide +kernel
      have hl : raw42757step0Labels = raw42757Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42757 raw42757Labels permutation174 permutation7
    mixedMoment B raw42757step0 raw42757step0Labels = mixedMoment B raw42757step1 raw42757step1Labels := by
      have ha : raw42757step1 = -raw42757step0 := by apply Matrix.ext; change ∀ i j, raw42757step1 i j = -(raw42757step0 i j); unfold raw42757step1 raw42757step0; decide +kernel
      have hl : raw42757step1Labels = raw42757step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42757step1 raw42757step1Labels = mixedMoment B raw42757step2 raw42757step2Labels := by
      have ha : raw42757step2 = raw42757step1 := by apply Matrix.ext; unfold raw42757step2 raw42757step1; decide +kernel
      have hl : raw42757step1Labels = labelEmbedding6 ∘ raw42757step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42757step1 raw42757step1Labels raw42757step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5044 node5044Labels := by rfl

theorem canonical42758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42758 raw42758Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw42758 raw42758Labels = mixedMoment B raw42758step0 raw42758step0Labels := by
      have ha : raw42758step0 = (fun i j => raw42758 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42758step0 raw42758; decide +kernel
      have hl : raw42758step0Labels = raw42758Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42758 raw42758Labels permutation155 permutation2
    mixedMoment B raw42758step0 raw42758step0Labels = mixedMoment B raw42758step1 raw42758step1Labels := by
      have ha : raw42758step1 = raw42758step0 := by apply Matrix.ext; unfold raw42758step1 raw42758step0; decide +kernel
      have hl : raw42758step0Labels = labelEmbedding1 ∘ raw42758step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42758step0 raw42758step0Labels raw42758step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3476 node3476Labels := by rfl

theorem canonical42759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42759 raw42759Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw42759 raw42759Labels = mixedMoment B raw42759step0 raw42759step0Labels := by
      have ha : raw42759step0 = (fun i j => raw42759 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42759step0 raw42759; decide +kernel
      have hl : raw42759step0Labels = raw42759Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42759 raw42759Labels permutation168 permutation7
    mixedMoment B raw42759step0 raw42759step0Labels = mixedMoment B raw42759step1 raw42759step1Labels := by
      have ha : raw42759step1 = -raw42759step0 := by apply Matrix.ext; change ∀ i j, raw42759step1 i j = -(raw42759step0 i j); unfold raw42759step1 raw42759step0; decide +kernel
      have hl : raw42759step1Labels = raw42759step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42759step1 raw42759step1Labels = mixedMoment B raw42759step2 raw42759step2Labels := by
      have ha : raw42759step2 = raw42759step1 := by apply Matrix.ext; unfold raw42759step2 raw42759step1; decide +kernel
      have hl : raw42759step1Labels = labelEmbedding6 ∘ raw42759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42759step1 raw42759step1Labels raw42759step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5067 node5067Labels := by rfl

theorem canonical42760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42760 raw42760Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw42760 raw42760Labels = mixedMoment B raw42760step0 raw42760step0Labels := by
      have ha : raw42760step0 = raw42760 := by apply Matrix.ext; unfold raw42760step0 raw42760; decide +kernel
      have hl : raw42760Labels = labelEmbedding1 ∘ raw42760step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42760 raw42760Labels raw42760step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

theorem canonical42761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42761 raw42761Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw42761 raw42761Labels = mixedMoment B raw42761step0 raw42761step0Labels := by
      have ha : raw42761step0 = (fun i j => raw42761 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42761step0 raw42761; decide +kernel
      have hl : raw42761step0Labels = raw42761Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42761 raw42761Labels permutation170 permutation7
    mixedMoment B raw42761step0 raw42761step0Labels = mixedMoment B raw42761step1 raw42761step1Labels := by
      have ha : raw42761step1 = -raw42761step0 := by apply Matrix.ext; change ∀ i j, raw42761step1 i j = -(raw42761step0 i j); unfold raw42761step1 raw42761step0; decide +kernel
      have hl : raw42761step1Labels = raw42761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42761step1 raw42761step1Labels = mixedMoment B raw42761step2 raw42761step2Labels := by
      have ha : raw42761step2 = raw42761step1 := by apply Matrix.ext; unfold raw42761step2 raw42761step1; decide +kernel
      have hl : raw42761step1Labels = labelEmbedding6 ∘ raw42761step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42761step1 raw42761step1Labels raw42761step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

theorem canonical42762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42762 raw42762Labels = mixedMoment B node3458 node3458Labels := by
  calc
    mixedMoment B raw42762 raw42762Labels = mixedMoment B raw42762step0 raw42762step0Labels := by
      have ha : raw42762step0 = raw42762 := by apply Matrix.ext; unfold raw42762step0 raw42762; decide +kernel
      have hl : raw42762Labels = labelEmbedding1 ∘ raw42762step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42762 raw42762Labels raw42762step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3458 node3458Labels := by rfl

theorem canonical42763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42763 raw42763Labels = mixedMoment B node5041 node5041Labels := by
  calc
    mixedMoment B raw42763 raw42763Labels = mixedMoment B raw42763step0 raw42763step0Labels := by
      have ha : raw42763step0 = (fun i j => raw42763 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42763step0 raw42763; decide +kernel
      have hl : raw42763step0Labels = raw42763Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42763 raw42763Labels permutation164 permutation7
    mixedMoment B raw42763step0 raw42763step0Labels = mixedMoment B raw42763step1 raw42763step1Labels := by
      have ha : raw42763step1 = -raw42763step0 := by apply Matrix.ext; change ∀ i j, raw42763step1 i j = -(raw42763step0 i j); unfold raw42763step1 raw42763step0; decide +kernel
      have hl : raw42763step1Labels = raw42763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42763step1 raw42763step1Labels = mixedMoment B raw42763step2 raw42763step2Labels := by
      have ha : raw42763step2 = raw42763step1 := by apply Matrix.ext; unfold raw42763step2 raw42763step1; decide +kernel
      have hl : raw42763step1Labels = labelEmbedding6 ∘ raw42763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42763step1 raw42763step1Labels raw42763step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5041 node5041Labels := by rfl

theorem canonical42764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42764 raw42764Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw42764 raw42764Labels = mixedMoment B raw42764step0 raw42764step0Labels := by
      have hz : ∀ j, raw42764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42764step0 = (fun i j => raw42764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42764step0 raw42764; decide +kernel
      have hl : raw42764step0Labels = raw42764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42764 raw42764Labels permutation434 hz
    mixedMoment B raw42764step0 raw42764step0Labels = mixedMoment B raw42764step1 raw42764step1Labels := by
      have ha : raw42764step1 = raw42764step0 := by apply Matrix.ext; unfold raw42764step1 raw42764step0; decide +kernel
      have hl : raw42764step0Labels = labelEmbedding1 ∘ raw42764step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42764step0 raw42764step0Labels raw42764step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3472 node3472Labels := by rfl

theorem canonical42765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42765 raw42765Labels = mixedMoment B node5087 node5087Labels := by
  calc
    mixedMoment B raw42765 raw42765Labels = mixedMoment B raw42765step0 raw42765step0Labels := by
      have hz : ∀ j, raw42765 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42765step0 = (fun i j => raw42765 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42765step0 raw42765; decide +kernel
      have hl : raw42765step0Labels = raw42765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42765 raw42765Labels permutation434 hz
    mixedMoment B raw42765step0 raw42765step0Labels = mixedMoment B raw42765step1 raw42765step1Labels := by
      have ha : raw42765step1 = (fun i j => raw42765step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42765step1 raw42765step0; decide +kernel
      have hl : raw42765step1Labels = raw42765step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42765step0 raw42765step0Labels permutation121 permutation6
    _ = mixedMoment B node5087 node5087Labels := by rfl

theorem canonical42766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42766 raw42766Labels = mixedMoment B node3266 node3266Labels := by
  calc
    mixedMoment B raw42766 raw42766Labels = mixedMoment B raw42766step0 raw42766step0Labels := by
      have hz : ∀ j, raw42766 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42766step0 = (fun i j => raw42766 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42766step0 raw42766; decide +kernel
      have hl : raw42766step0Labels = raw42766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42766 raw42766Labels permutation434 hz
    mixedMoment B raw42766step0 raw42766step0Labels = mixedMoment B raw42766step1 raw42766step1Labels := by
      have ha : raw42766step1 = (fun i j => raw42766step0 (permutation142 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42766step1 raw42766step0; decide +kernel
      have hl : raw42766step1Labels = raw42766step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42766step0 raw42766step0Labels permutation142 permutation4
    mixedMoment B raw42766step1 raw42766step1Labels = mixedMoment B raw42766step2 raw42766step2Labels := by
      have ha : raw42766step2 = -raw42766step1 := by apply Matrix.ext; change ∀ i j, raw42766step2 i j = -(raw42766step1 i j); unfold raw42766step2 raw42766step1; decide +kernel
      have hl : raw42766step2Labels = raw42766step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42766step2 raw42766step2Labels = mixedMoment B raw42766step3 raw42766step3Labels := by
      have ha : raw42766step3 = raw42766step2 := by apply Matrix.ext; unfold raw42766step3 raw42766step2; decide +kernel
      have hl : raw42766step2Labels = labelEmbedding1 ∘ raw42766step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42766step2 raw42766step2Labels raw42766step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3266 node3266Labels := by rfl

theorem canonical42767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42767 raw42767Labels = mixedMoment B node4547 node4547Labels := by
  calc
    mixedMoment B raw42767 raw42767Labels = mixedMoment B raw42767step0 raw42767step0Labels := by
      have hz : ∀ j, raw42767 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42767step0 = (fun i j => raw42767 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42767step0 raw42767; decide +kernel
      have hl : raw42767step0Labels = raw42767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42767 raw42767Labels permutation434 hz
    mixedMoment B raw42767step0 raw42767step0Labels = mixedMoment B raw42767step1 raw42767step1Labels := by
      have ha : raw42767step1 = (fun i j => raw42767step0 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42767step1 raw42767step0; decide +kernel
      have hl : raw42767step1Labels = raw42767step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42767step0 raw42767step0Labels permutation143 permutation6
    _ = mixedMoment B node4547 node4547Labels := by rfl

theorem canonical42768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42768 raw42768Labels = mixedMoment B node3260 node3260Labels := by
  calc
    mixedMoment B raw42768 raw42768Labels = mixedMoment B raw42768step0 raw42768step0Labels := by
      have ha : raw42768step0 = (fun i j => raw42768 (permutation634 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42768step0 raw42768; decide +kernel
      have hl : raw42768step0Labels = raw42768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42768 raw42768Labels permutation634 permutation4
    mixedMoment B raw42768step0 raw42768step0Labels = mixedMoment B raw42768step1 raw42768step1Labels := by
      have ha : raw42768step1 = -raw42768step0 := by apply Matrix.ext; change ∀ i j, raw42768step1 i j = -(raw42768step0 i j); unfold raw42768step1 raw42768step0; decide +kernel
      have hl : raw42768step1Labels = raw42768step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42768step1 raw42768step1Labels = mixedMoment B raw42768step2 raw42768step2Labels := by
      have ha : raw42768step2 = raw42768step1 := by apply Matrix.ext; unfold raw42768step2 raw42768step1; decide +kernel
      have hl : raw42768step1Labels = labelEmbedding1 ∘ raw42768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42768step1 raw42768step1Labels raw42768step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3260 node3260Labels := by rfl

theorem canonical42769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42769 raw42769Labels = mixedMoment B node4528 node4528Labels := by
  calc
    mixedMoment B raw42769 raw42769Labels = mixedMoment B raw42769step0 raw42769step0Labels := by
      have ha : raw42769step0 = (fun i j => raw42769 (permutation644 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42769step0 raw42769; decide +kernel
      have hl : raw42769step0Labels = raw42769Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42769 raw42769Labels permutation644 permutation6
    _ = mixedMoment B node4528 node4528Labels := by rfl

theorem canonical42770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42770 raw42770Labels = mixedMoment B node3451 node3451Labels := by
  calc
    mixedMoment B raw42770 raw42770Labels = mixedMoment B raw42770step0 raw42770step0Labels := by
      have ha : raw42770step0 = (fun i j => raw42770 (permutation477 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42770step0 raw42770; decide +kernel
      have hl : raw42770step0Labels = raw42770Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42770 raw42770Labels permutation477 permutation4
    mixedMoment B raw42770step0 raw42770step0Labels = mixedMoment B raw42770step1 raw42770step1Labels := by
      have ha : raw42770step1 = -raw42770step0 := by apply Matrix.ext; change ∀ i j, raw42770step1 i j = -(raw42770step0 i j); unfold raw42770step1 raw42770step0; decide +kernel
      have hl : raw42770step1Labels = raw42770step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42770step1 raw42770step1Labels = mixedMoment B raw42770step2 raw42770step2Labels := by
      have ha : raw42770step2 = raw42770step1 := by apply Matrix.ext; unfold raw42770step2 raw42770step1; decide +kernel
      have hl : raw42770step1Labels = labelEmbedding1 ∘ raw42770step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42770step1 raw42770step1Labels raw42770step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3451 node3451Labels := by rfl

theorem canonical42771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42771 raw42771Labels = mixedMoment B node5034 node5034Labels := by
  calc
    mixedMoment B raw42771 raw42771Labels = mixedMoment B raw42771step0 raw42771step0Labels := by
      have ha : raw42771step0 = (fun i j => raw42771 (permutation478 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42771step0 raw42771; decide +kernel
      have hl : raw42771step0Labels = raw42771Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42771 raw42771Labels permutation478 permutation6
    _ = mixedMoment B node5034 node5034Labels := by rfl

theorem canonical42772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42772 raw42772Labels = mixedMoment B node3466 node3466Labels := by
  calc
    mixedMoment B raw42772 raw42772Labels = mixedMoment B raw42772step0 raw42772step0Labels := by
      have ha : raw42772step0 = (fun i j => raw42772 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42772step0 raw42772; decide +kernel
      have hl : raw42772step0Labels = raw42772Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42772 raw42772Labels permutation155 permutation2
    mixedMoment B raw42772step0 raw42772step0Labels = mixedMoment B raw42772step1 raw42772step1Labels := by
      have ha : raw42772step1 = raw42772step0 := by apply Matrix.ext; unfold raw42772step1 raw42772step0; decide +kernel
      have hl : raw42772step0Labels = labelEmbedding1 ∘ raw42772step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42772step0 raw42772step0Labels raw42772step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3466 node3466Labels := by rfl

theorem canonical42773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42773 raw42773Labels = mixedMoment B node5065 node5065Labels := by
  calc
    mixedMoment B raw42773 raw42773Labels = mixedMoment B raw42773step0 raw42773step0Labels := by
      have ha : raw42773step0 = (fun i j => raw42773 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42773step0 raw42773; decide +kernel
      have hl : raw42773step0Labels = raw42773Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42773 raw42773Labels permutation480 permutation6
    _ = mixedMoment B node5065 node5065Labels := by rfl

theorem canonical42774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42774 raw42774Labels = mixedMoment B node3465 node3465Labels := by
  calc
    mixedMoment B raw42774 raw42774Labels = mixedMoment B raw42774step0 raw42774step0Labels := by
      have ha : raw42774step0 = (fun i j => raw42774 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42774step0 raw42774; decide +kernel
      have hl : raw42774step0Labels = raw42774Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42774 raw42774Labels permutation156 permutation2
    mixedMoment B raw42774step0 raw42774step0Labels = mixedMoment B raw42774step1 raw42774step1Labels := by
      have ha : raw42774step1 = raw42774step0 := by apply Matrix.ext; unfold raw42774step1 raw42774step0; decide +kernel
      have hl : raw42774step0Labels = labelEmbedding1 ∘ raw42774step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42774step0 raw42774step0Labels raw42774step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3465 node3465Labels := by rfl

theorem canonical42775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42775 raw42775Labels = mixedMoment B node5043 node5043Labels := by
  calc
    mixedMoment B raw42775 raw42775Labels = mixedMoment B raw42775step0 raw42775step0Labels := by
      have ha : raw42775step0 = (fun i j => raw42775 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42775step0 raw42775; decide +kernel
      have hl : raw42775step0Labels = raw42775Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42775 raw42775Labels permutation170 permutation7
    mixedMoment B raw42775step0 raw42775step0Labels = mixedMoment B raw42775step1 raw42775step1Labels := by
      have ha : raw42775step1 = -raw42775step0 := by apply Matrix.ext; change ∀ i j, raw42775step1 i j = -(raw42775step0 i j); unfold raw42775step1 raw42775step0; decide +kernel
      have hl : raw42775step1Labels = raw42775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42775step1 raw42775step1Labels = mixedMoment B raw42775step2 raw42775step2Labels := by
      have ha : raw42775step2 = raw42775step1 := by apply Matrix.ext; unfold raw42775step2 raw42775step1; decide +kernel
      have hl : raw42775step1Labels = labelEmbedding6 ∘ raw42775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42775step1 raw42775step1Labels raw42775step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5043 node5043Labels := by rfl

theorem canonical42776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42776 raw42776Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw42776 raw42776Labels = mixedMoment B raw42776step0 raw42776step0Labels := by
      have hz : ∀ j, raw42776 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42776step0 = (fun i j => raw42776 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42776step0 raw42776; decide +kernel
      have hl : raw42776step0Labels = raw42776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42776 raw42776Labels permutation434 hz
    mixedMoment B raw42776step0 raw42776step0Labels = mixedMoment B raw42776step1 raw42776step1Labels := by
      have hz : ∀ j, raw42776step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42776step1 = (fun i j => raw42776step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42776step1 raw42776step0; decide +kernel
      have hl : raw42776step1Labels = raw42776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42776step0 raw42776step0Labels permutation80 hz
    mixedMoment B raw42776step1 raw42776step1Labels = mixedMoment B raw42776step2 raw42776step2Labels := by
      have ha : raw42776step2 = (fun i j => raw42776step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42776step2 raw42776step1; decide +kernel
      have hl : raw42776step2Labels = raw42776step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42776step1 raw42776step1Labels permutation22 permutation4
    mixedMoment B raw42776step2 raw42776step2Labels = mixedMoment B raw42776step3 raw42776step3Labels := by
      have ha : raw42776step3 = -raw42776step2 := by apply Matrix.ext; change ∀ i j, raw42776step3 i j = -(raw42776step2 i j); unfold raw42776step3 raw42776step2; decide +kernel
      have hl : raw42776step3Labels = raw42776step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42776step3 raw42776step3Labels = mixedMoment B raw42776step4 raw42776step4Labels := by
      have ha : raw42776step4 = raw42776step3 := by apply Matrix.ext; unfold raw42776step4 raw42776step3; decide +kernel
      have hl : raw42776step3Labels = labelEmbedding1 ∘ raw42776step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42776step3 raw42776step3Labels raw42776step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

theorem canonical42777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42777 raw42777Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw42777 raw42777Labels = mixedMoment B raw42777step0 raw42777step0Labels := by
      have hz : ∀ j, raw42777 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42777step0 = (fun i j => raw42777 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42777step0 raw42777; decide +kernel
      have hl : raw42777step0Labels = raw42777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42777 raw42777Labels permutation434 hz
    mixedMoment B raw42777step0 raw42777step0Labels = mixedMoment B raw42777step1 raw42777step1Labels := by
      have hz : ∀ j, raw42777step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42777step1 = (fun i j => raw42777step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42777step1 raw42777step0; decide +kernel
      have hl : raw42777step1Labels = raw42777step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42777step0 raw42777step0Labels permutation80 hz
    mixedMoment B raw42777step1 raw42777step1Labels = mixedMoment B raw42777step2 raw42777step2Labels := by
      have ha : raw42777step2 = (fun i j => raw42777step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42777step2 raw42777step1; decide +kernel
      have hl : raw42777step2Labels = raw42777step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42777step1 raw42777step1Labels permutation25 permutation6
    _ = mixedMoment B node4476 node4476Labels := by rfl

theorem canonical42778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42778 raw42778Labels = mixedMoment B node1520 node1520Labels := by
  calc
    mixedMoment B raw42778 raw42778Labels = mixedMoment B raw42778step0 raw42778step0Labels := by
      have hz : ∀ j, raw42778 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42778step0 = (fun i j => raw42778 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42778step0 raw42778; decide +kernel
      have hl : raw42778step0Labels = raw42778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42778 raw42778Labels permutation434 hz
    mixedMoment B raw42778step0 raw42778step0Labels = mixedMoment B raw42778step1 raw42778step1Labels := by
      have hz : ∀ j, raw42778step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42778step1 = (fun i j => raw42778step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42778step1 raw42778step0; decide +kernel
      have hl : raw42778step1Labels = raw42778step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42778step0 raw42778step0Labels permutation80 hz
    mixedMoment B raw42778step1 raw42778step1Labels = mixedMoment B raw42778step2 raw42778step2Labels := by
      have ha : raw42778step2 = (fun i j => raw42778step1 (permutation28 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42778step2 raw42778step1; decide +kernel
      have hl : raw42778step2Labels = raw42778step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42778step1 raw42778step1Labels permutation28 permutation4
    mixedMoment B raw42778step2 raw42778step2Labels = mixedMoment B raw42778step3 raw42778step3Labels := by
      have ha : raw42778step3 = -raw42778step2 := by apply Matrix.ext; change ∀ i j, raw42778step3 i j = -(raw42778step2 i j); unfold raw42778step3 raw42778step2; decide +kernel
      have hl : raw42778step3Labels = raw42778step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42778step3 raw42778step3Labels = mixedMoment B raw42778step4 raw42778step4Labels := by
      have ha : raw42778step4 = raw42778step3 := by apply Matrix.ext; unfold raw42778step4 raw42778step3; decide +kernel
      have hl : raw42778step3Labels = labelEmbedding1 ∘ raw42778step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42778step3 raw42778step3Labels raw42778step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1520 node1520Labels := by rfl

theorem canonical42779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42779 raw42779Labels = mixedMoment B node4178 node4178Labels := by
  calc
    mixedMoment B raw42779 raw42779Labels = mixedMoment B raw42779step0 raw42779step0Labels := by
      have hz : ∀ j, raw42779 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42779step0 = (fun i j => raw42779 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42779step0 raw42779; decide +kernel
      have hl : raw42779step0Labels = raw42779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42779 raw42779Labels permutation434 hz
    mixedMoment B raw42779step0 raw42779step0Labels = mixedMoment B raw42779step1 raw42779step1Labels := by
      have hz : ∀ j, raw42779step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42779step1 = (fun i j => raw42779step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42779step1 raw42779step0; decide +kernel
      have hl : raw42779step1Labels = raw42779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42779step0 raw42779step0Labels permutation80 hz
    mixedMoment B raw42779step1 raw42779step1Labels = mixedMoment B raw42779step2 raw42779step2Labels := by
      have ha : raw42779step2 = (fun i j => raw42779step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42779step2 raw42779step1; decide +kernel
      have hl : raw42779step2Labels = raw42779step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42779step1 raw42779step1Labels permutation29 permutation6
    _ = mixedMoment B node4178 node4178Labels := by rfl

theorem canonical42780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42780 raw42780Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw42780 raw42780Labels = mixedMoment B raw42780step0 raw42780step0Labels := by
      have hz : ∀ j, raw42780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42780step0 = (fun i j => raw42780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42780step0 raw42780; decide +kernel
      have hl : raw42780step0Labels = raw42780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42780 raw42780Labels permutation346 hz
    mixedMoment B raw42780step0 raw42780step0Labels = mixedMoment B raw42780step1 raw42780step1Labels := by
      have ha : raw42780step1 = (fun i j => raw42780step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42780step1 raw42780step0; decide +kernel
      have hl : raw42780step1Labels = raw42780step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42780step0 raw42780step0Labels permutation139 permutation4
    mixedMoment B raw42780step1 raw42780step1Labels = mixedMoment B raw42780step2 raw42780step2Labels := by
      have ha : raw42780step2 = -raw42780step1 := by apply Matrix.ext; change ∀ i j, raw42780step2 i j = -(raw42780step1 i j); unfold raw42780step2 raw42780step1; decide +kernel
      have hl : raw42780step2Labels = raw42780step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42780step2 raw42780step2Labels = mixedMoment B raw42780step3 raw42780step3Labels := by
      have ha : raw42780step3 = raw42780step2 := by apply Matrix.ext; unfold raw42780step3 raw42780step2; decide +kernel
      have hl : raw42780step2Labels = labelEmbedding1 ∘ raw42780step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42780step2 raw42780step2Labels raw42780step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1514 node1514Labels := by rfl

theorem canonical42781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42781 raw42781Labels = mixedMoment B node4153 node4153Labels := by
  calc
    mixedMoment B raw42781 raw42781Labels = mixedMoment B raw42781step0 raw42781step0Labels := by
      have hz : ∀ j, raw42781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42781step0 = (fun i j => raw42781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42781step0 raw42781; decide +kernel
      have hl : raw42781step0Labels = raw42781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42781 raw42781Labels permutation346 hz
    mixedMoment B raw42781step0 raw42781step0Labels = mixedMoment B raw42781step1 raw42781step1Labels := by
      have ha : raw42781step1 = (fun i j => raw42781step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42781step1 raw42781step0; decide +kernel
      have hl : raw42781step1Labels = raw42781step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42781step0 raw42781step0Labels permutation149 permutation6
    _ = mixedMoment B node4153 node4153Labels := by rfl

theorem canonical42782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42782 raw42782Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw42782 raw42782Labels = mixedMoment B raw42782step0 raw42782step0Labels := by
      have hz : ∀ j, raw42782 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42782step0 = (fun i j => raw42782 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42782step0 raw42782; decide +kernel
      have hl : raw42782step0Labels = raw42782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42782 raw42782Labels permutation346 hz
    mixedMoment B raw42782step0 raw42782step0Labels = mixedMoment B raw42782step1 raw42782step1Labels := by
      have ha : raw42782step1 = (fun i j => raw42782step0 (permutation94 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42782step1 raw42782step0; decide +kernel
      have hl : raw42782step1Labels = raw42782step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42782step0 raw42782step0Labels permutation94 permutation4
    mixedMoment B raw42782step1 raw42782step1Labels = mixedMoment B raw42782step2 raw42782step2Labels := by
      have ha : raw42782step2 = -raw42782step1 := by apply Matrix.ext; change ∀ i j, raw42782step2 i j = -(raw42782step1 i j); unfold raw42782step2 raw42782step1; decide +kernel
      have hl : raw42782step2Labels = raw42782step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42782step2 raw42782step2Labels = mixedMoment B raw42782step3 raw42782step3Labels := by
      have ha : raw42782step3 = raw42782step2 := by apply Matrix.ext; unfold raw42782step3 raw42782step2; decide +kernel
      have hl : raw42782step2Labels = labelEmbedding1 ∘ raw42782step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42782step2 raw42782step2Labels raw42782step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

theorem canonical42783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42783 raw42783Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw42783 raw42783Labels = mixedMoment B raw42783step0 raw42783step0Labels := by
      have hz : ∀ j, raw42783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42783step0 = (fun i j => raw42783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42783step0 raw42783; decide +kernel
      have hl : raw42783step0Labels = raw42783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42783 raw42783Labels permutation346 hz
    mixedMoment B raw42783step0 raw42783step0Labels = mixedMoment B raw42783step1 raw42783step1Labels := by
      have ha : raw42783step1 = (fun i j => raw42783step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42783step1 raw42783step0; decide +kernel
      have hl : raw42783step1Labels = raw42783step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42783step0 raw42783step0Labels permutation95 permutation6
    _ = mixedMoment B node4347 node4347Labels := by rfl

theorem canonical42784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42784 raw42784Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw42784 raw42784Labels = mixedMoment B raw42784step0 raw42784step0Labels := by
      have hz : ∀ j, raw42784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42784step0 = (fun i j => raw42784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42784step0 raw42784; decide +kernel
      have hl : raw42784step0Labels = raw42784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42784 raw42784Labels permutation346 hz
    mixedMoment B raw42784step0 raw42784step0Labels = mixedMoment B raw42784step1 raw42784step1Labels := by
      have ha : raw42784step1 = (fun i j => raw42784step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42784step1 raw42784step0; decide +kernel
      have hl : raw42784step1Labels = raw42784step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42784step0 raw42784step0Labels permutation89 permutation4
    mixedMoment B raw42784step1 raw42784step1Labels = mixedMoment B raw42784step2 raw42784step2Labels := by
      have ha : raw42784step2 = -raw42784step1 := by apply Matrix.ext; change ∀ i j, raw42784step2 i j = -(raw42784step1 i j); unfold raw42784step2 raw42784step1; decide +kernel
      have hl : raw42784step2Labels = raw42784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42784step2 raw42784step2Labels = mixedMoment B raw42784step3 raw42784step3Labels := by
      have ha : raw42784step3 = raw42784step2 := by apply Matrix.ext; unfold raw42784step3 raw42784step2; decide +kernel
      have hl : raw42784step2Labels = labelEmbedding1 ∘ raw42784step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42784step2 raw42784step2Labels raw42784step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

theorem canonical42785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42785 raw42785Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw42785 raw42785Labels = mixedMoment B raw42785step0 raw42785step0Labels := by
      have hz : ∀ j, raw42785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42785step0 = (fun i j => raw42785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42785step0 raw42785; decide +kernel
      have hl : raw42785step0Labels = raw42785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42785 raw42785Labels permutation346 hz
    mixedMoment B raw42785step0 raw42785step0Labels = mixedMoment B raw42785step1 raw42785step1Labels := by
      have ha : raw42785step1 = (fun i j => raw42785step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42785step1 raw42785step0; decide +kernel
      have hl : raw42785step1Labels = raw42785step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42785step0 raw42785step0Labels permutation97 permutation6
    _ = mixedMoment B node4440 node4440Labels := by rfl

theorem canonical42786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42786 raw42786Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw42786 raw42786Labels = mixedMoment B raw42786step0 raw42786step0Labels := by
      have hz : ∀ j, raw42786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42786step0 = (fun i j => raw42786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42786step0 raw42786; decide +kernel
      have hl : raw42786step0Labels = raw42786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42786 raw42786Labels permutation346 hz
    mixedMoment B raw42786step0 raw42786step0Labels = mixedMoment B raw42786step1 raw42786step1Labels := by
      have ha : raw42786step1 = (fun i j => raw42786step0 (permutation94 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42786step1 raw42786step0; decide +kernel
      have hl : raw42786step1Labels = raw42786step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42786step0 raw42786step0Labels permutation94 permutation4
    mixedMoment B raw42786step1 raw42786step1Labels = mixedMoment B raw42786step2 raw42786step2Labels := by
      have ha : raw42786step2 = -raw42786step1 := by apply Matrix.ext; change ∀ i j, raw42786step2 i j = -(raw42786step1 i j); unfold raw42786step2 raw42786step1; decide +kernel
      have hl : raw42786step2Labels = raw42786step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42786step2 raw42786step2Labels = mixedMoment B raw42786step3 raw42786step3Labels := by
      have ha : raw42786step3 = raw42786step2 := by apply Matrix.ext; unfold raw42786step3 raw42786step2; decide +kernel
      have hl : raw42786step2Labels = labelEmbedding1 ∘ raw42786step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42786step2 raw42786step2Labels raw42786step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

theorem canonical42787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42787 raw42787Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw42787 raw42787Labels = mixedMoment B raw42787step0 raw42787step0Labels := by
      have hz : ∀ j, raw42787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42787step0 = (fun i j => raw42787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42787step0 raw42787; decide +kernel
      have hl : raw42787step0Labels = raw42787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42787 raw42787Labels permutation346 hz
    mixedMoment B raw42787step0 raw42787step0Labels = mixedMoment B raw42787step1 raw42787step1Labels := by
      have ha : raw42787step1 = (fun i j => raw42787step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42787step1 raw42787step0; decide +kernel
      have hl : raw42787step1Labels = raw42787step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42787step0 raw42787step0Labels permutation95 permutation6
    _ = mixedMoment B node4944 node4944Labels := by rfl

theorem canonical42788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42788 raw42788Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw42788 raw42788Labels = mixedMoment B raw42788step0 raw42788step0Labels := by
      have ha : raw42788step0 = (fun i j => raw42788 (permutation494 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42788step0 raw42788; decide +kernel
      have hl : raw42788step0Labels = raw42788Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42788 raw42788Labels permutation494 permutation4
    mixedMoment B raw42788step0 raw42788step0Labels = mixedMoment B raw42788step1 raw42788step1Labels := by
      have ha : raw42788step1 = -raw42788step0 := by apply Matrix.ext; change ∀ i j, raw42788step1 i j = -(raw42788step0 i j); unfold raw42788step1 raw42788step0; decide +kernel
      have hl : raw42788step1Labels = raw42788step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42788step1 raw42788step1Labels = mixedMoment B raw42788step2 raw42788step2Labels := by
      have ha : raw42788step2 = raw42788step1 := by apply Matrix.ext; unfold raw42788step2 raw42788step1; decide +kernel
      have hl : raw42788step1Labels = labelEmbedding1 ∘ raw42788step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42788step1 raw42788step1Labels raw42788step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

theorem canonical42789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42789 raw42789Labels = mixedMoment B node4327 node4327Labels := by
  calc
    mixedMoment B raw42789 raw42789Labels = mixedMoment B raw42789step0 raw42789step0Labels := by
      have ha : raw42789step0 = (fun i j => raw42789 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42789step0 raw42789; decide +kernel
      have hl : raw42789step0Labels = raw42789Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42789 raw42789Labels permutation502 permutation6
    _ = mixedMoment B node4327 node4327Labels := by rfl

theorem canonical42790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42790 raw42790Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw42790 raw42790Labels = mixedMoment B raw42790step0 raw42790step0Labels := by
      have ha : raw42790step0 = (fun i j => raw42790 (permutation494 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42790step0 raw42790; decide +kernel
      have hl : raw42790step0Labels = raw42790Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42790 raw42790Labels permutation494 permutation4
    mixedMoment B raw42790step0 raw42790step0Labels = mixedMoment B raw42790step1 raw42790step1Labels := by
      have ha : raw42790step1 = -raw42790step0 := by apply Matrix.ext; change ∀ i j, raw42790step1 i j = -(raw42790step0 i j); unfold raw42790step1 raw42790step0; decide +kernel
      have hl : raw42790step1Labels = raw42790step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42790step1 raw42790step1Labels = mixedMoment B raw42790step2 raw42790step2Labels := by
      have ha : raw42790step2 = raw42790step1 := by apply Matrix.ext; unfold raw42790step2 raw42790step1; decide +kernel
      have hl : raw42790step1Labels = labelEmbedding1 ∘ raw42790step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42790step1 raw42790step1Labels raw42790step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

theorem canonical42791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42791 raw42791Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw42791 raw42791Labels = mixedMoment B raw42791step0 raw42791step0Labels := by
      have ha : raw42791step0 = (fun i j => raw42791 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42791step0 raw42791; decide +kernel
      have hl : raw42791step0Labels = raw42791Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42791 raw42791Labels permutation502 permutation6
    _ = mixedMoment B node4930 node4930Labels := by rfl

theorem canonical42792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42792 raw42792Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw42792 raw42792Labels = mixedMoment B raw42792step0 raw42792step0Labels := by
      have hz : ∀ j, raw42792 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42792step0 = (fun i j => raw42792 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42792step0 raw42792; decide +kernel
      have hl : raw42792step0Labels = raw42792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42792 raw42792Labels permutation434 hz
    mixedMoment B raw42792step0 raw42792step0Labels = mixedMoment B raw42792step1 raw42792step1Labels := by
      have ha : raw42792step1 = (fun i j => raw42792step0 (permutation103 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42792step1 raw42792step0; decide +kernel
      have hl : raw42792step1Labels = raw42792step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42792step0 raw42792step0Labels permutation103 permutation4
    mixedMoment B raw42792step1 raw42792step1Labels = mixedMoment B raw42792step2 raw42792step2Labels := by
      have ha : raw42792step2 = -raw42792step1 := by apply Matrix.ext; change ∀ i j, raw42792step2 i j = -(raw42792step1 i j); unfold raw42792step2 raw42792step1; decide +kernel
      have hl : raw42792step2Labels = raw42792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42792step2 raw42792step2Labels = mixedMoment B raw42792step3 raw42792step3Labels := by
      have ha : raw42792step3 = raw42792step2 := by apply Matrix.ext; unfold raw42792step3 raw42792step2; decide +kernel
      have hl : raw42792step2Labels = labelEmbedding1 ∘ raw42792step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42792step2 raw42792step2Labels raw42792step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2164 node2164Labels := by rfl

theorem canonical42793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42793 raw42793Labels = mixedMoment B node4670 node4670Labels := by
  calc
    mixedMoment B raw42793 raw42793Labels = mixedMoment B raw42793step0 raw42793step0Labels := by
      have hz : ∀ j, raw42793 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42793step0 = (fun i j => raw42793 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42793step0 raw42793; decide +kernel
      have hl : raw42793step0Labels = raw42793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42793 raw42793Labels permutation434 hz
    mixedMoment B raw42793step0 raw42793step0Labels = mixedMoment B raw42793step1 raw42793step1Labels := by
      have ha : raw42793step1 = (fun i j => raw42793step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42793step1 raw42793step0; decide +kernel
      have hl : raw42793step1Labels = raw42793step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42793step0 raw42793step0Labels permutation103 permutation6
    _ = mixedMoment B node4670 node4670Labels := by rfl

theorem canonical42794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42794 raw42794Labels = mixedMoment B node2181 node2181Labels := by
  calc
    mixedMoment B raw42794 raw42794Labels = mixedMoment B raw42794step0 raw42794step0Labels := by
      have ha : raw42794step0 = (fun i j => raw42794 (permutation394 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42794step0 raw42794; decide +kernel
      have hl : raw42794step0Labels = raw42794Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42794 raw42794Labels permutation394 permutation4
    mixedMoment B raw42794step0 raw42794step0Labels = mixedMoment B raw42794step1 raw42794step1Labels := by
      have ha : raw42794step1 = -raw42794step0 := by apply Matrix.ext; change ∀ i j, raw42794step1 i j = -(raw42794step0 i j); unfold raw42794step1 raw42794step0; decide +kernel
      have hl : raw42794step1Labels = raw42794step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42794step1 raw42794step1Labels = mixedMoment B raw42794step2 raw42794step2Labels := by
      have ha : raw42794step2 = raw42794step1 := by apply Matrix.ext; unfold raw42794step2 raw42794step1; decide +kernel
      have hl : raw42794step1Labels = labelEmbedding1 ∘ raw42794step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42794step1 raw42794step1Labels raw42794step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2181 node2181Labels := by rfl

theorem canonical42795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42795 raw42795Labels = mixedMoment B node4757 node4757Labels := by
  calc
    mixedMoment B raw42795 raw42795Labels = mixedMoment B raw42795step0 raw42795step0Labels := by
      have ha : raw42795step0 = (fun i j => raw42795 (permutation394 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42795step0 raw42795; decide +kernel
      have hl : raw42795step0Labels = raw42795Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42795 raw42795Labels permutation394 permutation6
    _ = mixedMoment B node4757 node4757Labels := by rfl

theorem canonical42796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42796 raw42796Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw42796 raw42796Labels = mixedMoment B raw42796step0 raw42796step0Labels := by
      have ha : raw42796step0 = (fun i j => raw42796 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42796step0 raw42796; decide +kernel
      have hl : raw42796step0Labels = raw42796Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42796 raw42796Labels permutation158 permutation2
    mixedMoment B raw42796step0 raw42796step0Labels = mixedMoment B raw42796step1 raw42796step1Labels := by
      have ha : raw42796step1 = raw42796step0 := by apply Matrix.ext; unfold raw42796step1 raw42796step0; decide +kernel
      have hl : raw42796step0Labels = labelEmbedding1 ∘ raw42796step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42796step0 raw42796step0Labels raw42796step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

theorem canonical42797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42797 raw42797Labels = mixedMoment B node4931 node4931Labels := by
  calc
    mixedMoment B raw42797 raw42797Labels = mixedMoment B raw42797step0 raw42797step0Labels := by
      have ha : raw42797step0 = (fun i j => raw42797 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42797step0 raw42797; decide +kernel
      have hl : raw42797step0Labels = raw42797Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42797 raw42797Labels permutation166 permutation7
    mixedMoment B raw42797step0 raw42797step0Labels = mixedMoment B raw42797step1 raw42797step1Labels := by
      have ha : raw42797step1 = -raw42797step0 := by apply Matrix.ext; change ∀ i j, raw42797step1 i j = -(raw42797step0 i j); unfold raw42797step1 raw42797step0; decide +kernel
      have hl : raw42797step1Labels = raw42797step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42797step1 raw42797step1Labels = mixedMoment B raw42797step2 raw42797step2Labels := by
      have ha : raw42797step2 = raw42797step1 := by apply Matrix.ext; unfold raw42797step2 raw42797step1; decide +kernel
      have hl : raw42797step1Labels = labelEmbedding6 ∘ raw42797step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42797step1 raw42797step1Labels raw42797step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4931 node4931Labels := by rfl

theorem canonical42798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42798 raw42798Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw42798 raw42798Labels = mixedMoment B raw42798step0 raw42798step0Labels := by
      have hz : ∀ j, raw42798 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42798step0 = (fun i j => raw42798 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42798step0 raw42798; decide +kernel
      have hl : raw42798step0Labels = raw42798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42798 raw42798Labels permutation434 hz
    mixedMoment B raw42798step0 raw42798step0Labels = mixedMoment B raw42798step1 raw42798step1Labels := by
      have ha : raw42798step1 = raw42798step0 := by apply Matrix.ext; unfold raw42798step1 raw42798step0; decide +kernel
      have hl : raw42798step0Labels = labelEmbedding1 ∘ raw42798step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42798step0 raw42798step0Labels raw42798step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

theorem canonical42799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42799 raw42799Labels = mixedMoment B node4934 node4934Labels := by
  calc
    mixedMoment B raw42799 raw42799Labels = mixedMoment B raw42799step0 raw42799step0Labels := by
      have hz : ∀ j, raw42799 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42799step0 = (fun i j => raw42799 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42799step0 raw42799; decide +kernel
      have hl : raw42799step0Labels = raw42799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42799 raw42799Labels permutation434 hz
    mixedMoment B raw42799step0 raw42799step0Labels = mixedMoment B raw42799step1 raw42799step1Labels := by
      have ha : raw42799step1 = (fun i j => raw42799step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42799step1 raw42799step0; decide +kernel
      have hl : raw42799step1Labels = raw42799step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42799step0 raw42799step0Labels permutation34 permutation7
    mixedMoment B raw42799step1 raw42799step1Labels = mixedMoment B raw42799step2 raw42799step2Labels := by
      have ha : raw42799step2 = -raw42799step1 := by apply Matrix.ext; change ∀ i j, raw42799step2 i j = -(raw42799step1 i j); unfold raw42799step2 raw42799step1; decide +kernel
      have hl : raw42799step2Labels = raw42799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42799step2 raw42799step2Labels = mixedMoment B raw42799step3 raw42799step3Labels := by
      have ha : raw42799step3 = raw42799step2 := by apply Matrix.ext; unfold raw42799step3 raw42799step2; decide +kernel
      have hl : raw42799step2Labels = labelEmbedding6 ∘ raw42799step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42799step2 raw42799step2Labels raw42799step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4934 node4934Labels := by rfl

theorem canonical42800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42800 raw42800Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw42800 raw42800Labels = mixedMoment B raw42800step0 raw42800step0Labels := by
      have ha : raw42800step0 = (fun i j => raw42800 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42800step0 raw42800; decide +kernel
      have hl : raw42800step0Labels = raw42800Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42800 raw42800Labels permutation157 permutation2
    mixedMoment B raw42800step0 raw42800step0Labels = mixedMoment B raw42800step1 raw42800step1Labels := by
      have ha : raw42800step1 = raw42800step0 := by apply Matrix.ext; unfold raw42800step1 raw42800step0; decide +kernel
      have hl : raw42800step0Labels = labelEmbedding1 ∘ raw42800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42800step0 raw42800step0Labels raw42800step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

theorem canonical42801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42801 raw42801Labels = mixedMoment B node4933 node4933Labels := by
  calc
    mixedMoment B raw42801 raw42801Labels = mixedMoment B raw42801step0 raw42801step0Labels := by
      have ha : raw42801step0 = (fun i j => raw42801 (permutation174 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42801step0 raw42801; decide +kernel
      have hl : raw42801step0Labels = raw42801Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42801 raw42801Labels permutation174 permutation7
    mixedMoment B raw42801step0 raw42801step0Labels = mixedMoment B raw42801step1 raw42801step1Labels := by
      have ha : raw42801step1 = -raw42801step0 := by apply Matrix.ext; change ∀ i j, raw42801step1 i j = -(raw42801step0 i j); unfold raw42801step1 raw42801step0; decide +kernel
      have hl : raw42801step1Labels = raw42801step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42801step1 raw42801step1Labels = mixedMoment B raw42801step2 raw42801step2Labels := by
      have ha : raw42801step2 = raw42801step1 := by apply Matrix.ext; unfold raw42801step2 raw42801step1; decide +kernel
      have hl : raw42801step1Labels = labelEmbedding6 ∘ raw42801step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42801step1 raw42801step1Labels raw42801step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4933 node4933Labels := by rfl

theorem canonical42802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42802 raw42802Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw42802 raw42802Labels = mixedMoment B raw42802step0 raw42802step0Labels := by
      have hz : ∀ j, raw42802 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42802step0 = (fun i j => raw42802 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42802step0 raw42802; decide +kernel
      have hl : raw42802step0Labels = raw42802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42802 raw42802Labels permutation434 hz
    mixedMoment B raw42802step0 raw42802step0Labels = mixedMoment B raw42802step1 raw42802step1Labels := by
      have ha : raw42802step1 = (fun i j => raw42802step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42802step1 raw42802step0; decide +kernel
      have hl : raw42802step1Labels = raw42802step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42802step0 raw42802step0Labels permutation145 permutation4
    mixedMoment B raw42802step1 raw42802step1Labels = mixedMoment B raw42802step2 raw42802step2Labels := by
      have ha : raw42802step2 = -raw42802step1 := by apply Matrix.ext; change ∀ i j, raw42802step2 i j = -(raw42802step1 i j); unfold raw42802step2 raw42802step1; decide +kernel
      have hl : raw42802step2Labels = raw42802step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42802step2 raw42802step2Labels = mixedMoment B raw42802step3 raw42802step3Labels := by
      have ha : raw42802step3 = raw42802step2 := by apply Matrix.ext; unfold raw42802step3 raw42802step2; decide +kernel
      have hl : raw42802step2Labels = labelEmbedding1 ∘ raw42802step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42802step2 raw42802step2Labels raw42802step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

theorem canonical42803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42803 raw42803Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw42803 raw42803Labels = mixedMoment B raw42803step0 raw42803step0Labels := by
      have hz : ∀ j, raw42803 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42803step0 = (fun i j => raw42803 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42803step0 raw42803; decide +kernel
      have hl : raw42803step0Labels = raw42803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42803 raw42803Labels permutation434 hz
    mixedMoment B raw42803step0 raw42803step0Labels = mixedMoment B raw42803step1 raw42803step1Labels := by
      have ha : raw42803step1 = (fun i j => raw42803step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42803step1 raw42803step0; decide +kernel
      have hl : raw42803step1Labels = raw42803step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42803step0 raw42803step0Labels permutation145 permutation6
    _ = mixedMoment B node4535 node4535Labels := by rfl

theorem canonical42804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42804 raw42804Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw42804 raw42804Labels = mixedMoment B raw42804step0 raw42804step0Labels := by
      have ha : raw42804step0 = (fun i j => raw42804 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42804step0 raw42804; decide +kernel
      have hl : raw42804step0Labels = raw42804Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42804 raw42804Labels permutation157 permutation2
    mixedMoment B raw42804step0 raw42804step0Labels = mixedMoment B raw42804step1 raw42804step1Labels := by
      have ha : raw42804step1 = raw42804step0 := by apply Matrix.ext; unfold raw42804step1 raw42804step0; decide +kernel
      have hl : raw42804step0Labels = labelEmbedding1 ∘ raw42804step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42804step0 raw42804step0Labels raw42804step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

theorem canonical42805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42805 raw42805Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw42805 raw42805Labels = mixedMoment B raw42805step0 raw42805step0Labels := by
      have ha : raw42805step0 = (fun i j => raw42805 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42805step0 raw42805; decide +kernel
      have hl : raw42805step0Labels = raw42805Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42805 raw42805Labels permutation171 permutation7
    mixedMoment B raw42805step0 raw42805step0Labels = mixedMoment B raw42805step1 raw42805step1Labels := by
      have ha : raw42805step1 = -raw42805step0 := by apply Matrix.ext; change ∀ i j, raw42805step1 i j = -(raw42805step0 i j); unfold raw42805step1 raw42805step0; decide +kernel
      have hl : raw42805step1Labels = raw42805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42805step1 raw42805step1Labels = mixedMoment B raw42805step2 raw42805step2Labels := by
      have ha : raw42805step2 = raw42805step1 := by apply Matrix.ext; unfold raw42805step2 raw42805step1; decide +kernel
      have hl : raw42805step1Labels = labelEmbedding6 ∘ raw42805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42805step1 raw42805step1Labels raw42805step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4930 node4930Labels := by rfl

theorem canonical42806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42806 raw42806Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw42806 raw42806Labels = mixedMoment B raw42806step0 raw42806step0Labels := by
      have hz : ∀ j, raw42806 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42806step0 = (fun i j => raw42806 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42806step0 raw42806; decide +kernel
      have hl : raw42806step0Labels = raw42806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42806 raw42806Labels permutation434 hz
    mixedMoment B raw42806step0 raw42806step0Labels = mixedMoment B raw42806step1 raw42806step1Labels := by
      have hz : ∀ j, raw42806step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42806step1 = (fun i j => raw42806step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42806step1 raw42806step0; decide +kernel
      have hl : raw42806step1Labels = raw42806step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42806step0 raw42806step0Labels permutation80 hz
    mixedMoment B raw42806step1 raw42806step1Labels = mixedMoment B raw42806step2 raw42806step2Labels := by
      have ha : raw42806step2 = (fun i j => raw42806step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42806step2 raw42806step1; decide +kernel
      have hl : raw42806step2Labels = raw42806step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42806step1 raw42806step1Labels permutation31 permutation4
    mixedMoment B raw42806step2 raw42806step2Labels = mixedMoment B raw42806step3 raw42806step3Labels := by
      have ha : raw42806step3 = -raw42806step2 := by apply Matrix.ext; change ∀ i j, raw42806step3 i j = -(raw42806step2 i j); unfold raw42806step3 raw42806step2; decide +kernel
      have hl : raw42806step3Labels = raw42806step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42806step3 raw42806step3Labels = mixedMoment B raw42806step4 raw42806step4Labels := by
      have ha : raw42806step4 = raw42806step3 := by apply Matrix.ext; unfold raw42806step4 raw42806step3; decide +kernel
      have hl : raw42806step3Labels = labelEmbedding1 ∘ raw42806step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42806step3 raw42806step3Labels raw42806step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1533 node1533Labels := by rfl

theorem canonical42807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42807 raw42807Labels = mixedMoment B node4161 node4161Labels := by
  calc
    mixedMoment B raw42807 raw42807Labels = mixedMoment B raw42807step0 raw42807step0Labels := by
      have hz : ∀ j, raw42807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42807step0 = (fun i j => raw42807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42807step0 raw42807; decide +kernel
      have hl : raw42807step0Labels = raw42807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42807 raw42807Labels permutation434 hz
    mixedMoment B raw42807step0 raw42807step0Labels = mixedMoment B raw42807step1 raw42807step1Labels := by
      have hz : ∀ j, raw42807step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42807step1 = (fun i j => raw42807step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42807step1 raw42807step0; decide +kernel
      have hl : raw42807step1Labels = raw42807step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42807step0 raw42807step0Labels permutation80 hz
    mixedMoment B raw42807step1 raw42807step1Labels = mixedMoment B raw42807step2 raw42807step2Labels := by
      have ha : raw42807step2 = (fun i j => raw42807step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42807step2 raw42807step1; decide +kernel
      have hl : raw42807step2Labels = raw42807step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42807step1 raw42807step1Labels permutation31 permutation6
    _ = mixedMoment B node4161 node4161Labels := by rfl

theorem canonical42808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42808 raw42808Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw42808 raw42808Labels = mixedMoment B raw42808step0 raw42808step0Labels := by
      have hz : ∀ j, raw42808 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42808step0 = (fun i j => raw42808 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42808step0 raw42808; decide +kernel
      have hl : raw42808step0Labels = raw42808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42808 raw42808Labels permutation346 hz
    mixedMoment B raw42808step0 raw42808step0Labels = mixedMoment B raw42808step1 raw42808step1Labels := by
      have ha : raw42808step1 = (fun i j => raw42808step0 (permutation97 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42808step1 raw42808step0; decide +kernel
      have hl : raw42808step1Labels = raw42808step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42808step0 raw42808step0Labels permutation97 permutation4
    mixedMoment B raw42808step1 raw42808step1Labels = mixedMoment B raw42808step2 raw42808step2Labels := by
      have ha : raw42808step2 = -raw42808step1 := by apply Matrix.ext; change ∀ i j, raw42808step2 i j = -(raw42808step1 i j); unfold raw42808step2 raw42808step1; decide +kernel
      have hl : raw42808step2Labels = raw42808step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42808step2 raw42808step2Labels = mixedMoment B raw42808step3 raw42808step3Labels := by
      have ha : raw42808step3 = raw42808step2 := by apply Matrix.ext; unfold raw42808step3 raw42808step2; decide +kernel
      have hl : raw42808step2Labels = labelEmbedding1 ∘ raw42808step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42808step2 raw42808step2Labels raw42808step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

theorem canonical42809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42809 raw42809Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw42809 raw42809Labels = mixedMoment B raw42809step0 raw42809step0Labels := by
      have hz : ∀ j, raw42809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42809step0 = (fun i j => raw42809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42809step0 raw42809; decide +kernel
      have hl : raw42809step0Labels = raw42809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42809 raw42809Labels permutation346 hz
    mixedMoment B raw42809step0 raw42809step0Labels = mixedMoment B raw42809step1 raw42809step1Labels := by
      have ha : raw42809step1 = (fun i j => raw42809step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42809step1 raw42809step0; decide +kernel
      have hl : raw42809step1Labels = raw42809step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42809step0 raw42809step0Labels permutation97 permutation6
    _ = mixedMoment B node4335 node4335Labels := by rfl

theorem canonical42810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42810 raw42810Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw42810 raw42810Labels = mixedMoment B raw42810step0 raw42810step0Labels := by
      have hz : ∀ j, raw42810 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42810step0 = (fun i j => raw42810 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42810step0 raw42810; decide +kernel
      have hl : raw42810step0Labels = raw42810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42810 raw42810Labels permutation346 hz
    mixedMoment B raw42810step0 raw42810step0Labels = mixedMoment B raw42810step1 raw42810step1Labels := by
      have ha : raw42810step1 = (fun i j => raw42810step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42810step1 raw42810step0; decide +kernel
      have hl : raw42810step1Labels = raw42810step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42810step0 raw42810step0Labels permutation37 permutation2
    mixedMoment B raw42810step1 raw42810step1Labels = mixedMoment B raw42810step2 raw42810step2Labels := by
      have ha : raw42810step2 = raw42810step1 := by apply Matrix.ext; unfold raw42810step2 raw42810step1; decide +kernel
      have hl : raw42810step1Labels = labelEmbedding1 ∘ raw42810step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42810step1 raw42810step1Labels raw42810step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3419 node3419Labels := by rfl

theorem canonical42811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42811 raw42811Labels = mixedMoment B node4935 node4935Labels := by
  calc
    mixedMoment B raw42811 raw42811Labels = mixedMoment B raw42811step0 raw42811step0Labels := by
      have hz : ∀ j, raw42811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42811step0 = (fun i j => raw42811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42811step0 raw42811; decide +kernel
      have hl : raw42811step0Labels = raw42811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42811 raw42811Labels permutation346 hz
    mixedMoment B raw42811step0 raw42811step0Labels = mixedMoment B raw42811step1 raw42811step1Labels := by
      have ha : raw42811step1 = (fun i j => raw42811step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42811step1 raw42811step0; decide +kernel
      have hl : raw42811step1Labels = raw42811step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42811step0 raw42811step0Labels permutation97 permutation6
    _ = mixedMoment B node4935 node4935Labels := by rfl

theorem canonical42812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42812 raw42812Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw42812 raw42812Labels = mixedMoment B raw42812step0 raw42812step0Labels := by
      have hz : ∀ j, raw42812 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42812step0 = (fun i j => raw42812 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42812step0 raw42812; decide +kernel
      have hl : raw42812step0Labels = raw42812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42812 raw42812Labels permutation434 hz
    mixedMoment B raw42812step0 raw42812step0Labels = mixedMoment B raw42812step1 raw42812step1Labels := by
      have hz : ∀ j, raw42812step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42812step1 = (fun i j => raw42812step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42812step1 raw42812step0; decide +kernel
      have hl : raw42812step1Labels = raw42812step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42812step0 raw42812step0Labels permutation80 hz
    mixedMoment B raw42812step1 raw42812step1Labels = mixedMoment B raw42812step2 raw42812step2Labels := by
      have ha : raw42812step2 = (fun i j => raw42812step1 (permutation19 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42812step2 raw42812step1; decide +kernel
      have hl : raw42812step2Labels = raw42812step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42812step1 raw42812step1Labels permutation19 permutation4
    mixedMoment B raw42812step2 raw42812step2Labels = mixedMoment B raw42812step3 raw42812step3Labels := by
      have ha : raw42812step3 = -raw42812step2 := by apply Matrix.ext; change ∀ i j, raw42812step3 i j = -(raw42812step2 i j); unfold raw42812step3 raw42812step2; decide +kernel
      have hl : raw42812step3Labels = raw42812step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42812step3 raw42812step3Labels = mixedMoment B raw42812step4 raw42812step4Labels := by
      have ha : raw42812step4 = raw42812step3 := by apply Matrix.ext; unfold raw42812step4 raw42812step3; decide +kernel
      have hl : raw42812step3Labels = labelEmbedding1 ∘ raw42812step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42812step3 raw42812step3Labels raw42812step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

theorem canonical42813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42813 raw42813Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw42813 raw42813Labels = mixedMoment B raw42813step0 raw42813step0Labels := by
      have hz : ∀ j, raw42813 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42813step0 = (fun i j => raw42813 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42813step0 raw42813; decide +kernel
      have hl : raw42813step0Labels = raw42813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42813 raw42813Labels permutation434 hz
    mixedMoment B raw42813step0 raw42813step0Labels = mixedMoment B raw42813step1 raw42813step1Labels := by
      have hz : ∀ j, raw42813step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42813step1 = (fun i j => raw42813step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42813step1 raw42813step0; decide +kernel
      have hl : raw42813step1Labels = raw42813step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42813step0 raw42813step0Labels permutation80 hz
    mixedMoment B raw42813step1 raw42813step1Labels = mixedMoment B raw42813step2 raw42813step2Labels := by
      have ha : raw42813step2 = (fun i j => raw42813step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42813step2 raw42813step1; decide +kernel
      have hl : raw42813step2Labels = raw42813step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42813step1 raw42813step1Labels permutation11 permutation6
    mixedMoment B raw42813step2 raw42813step2Labels = mixedMoment B raw42813step3 raw42813step3Labels := by
      have ha : raw42813step3 = -raw42813step2 := by apply Matrix.ext; change ∀ i j, raw42813step3 i j = -(raw42813step2 i j); unfold raw42813step3 raw42813step2; decide +kernel
      have hl : raw42813step3Labels = raw42813step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4611 node4611Labels := by rfl

theorem canonical42814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42814 raw42814Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw42814 raw42814Labels = mixedMoment B raw42814step0 raw42814step0Labels := by
      have hz : ∀ j, raw42814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42814step0 = (fun i j => raw42814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42814step0 raw42814; decide +kernel
      have hl : raw42814step0Labels = raw42814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42814 raw42814Labels permutation346 hz
    mixedMoment B raw42814step0 raw42814step0Labels = mixedMoment B raw42814step1 raw42814step1Labels := by
      have ha : raw42814step1 = (fun i j => raw42814step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42814step1 raw42814step0; decide +kernel
      have hl : raw42814step1Labels = raw42814step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42814step0 raw42814step0Labels permutation65 permutation4
    mixedMoment B raw42814step1 raw42814step1Labels = mixedMoment B raw42814step2 raw42814step2Labels := by
      have ha : raw42814step2 = -raw42814step1 := by apply Matrix.ext; change ∀ i j, raw42814step2 i j = -(raw42814step1 i j); unfold raw42814step2 raw42814step1; decide +kernel
      have hl : raw42814step2Labels = raw42814step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42814step2 raw42814step2Labels = mixedMoment B raw42814step3 raw42814step3Labels := by
      have ha : raw42814step3 = raw42814step2 := by apply Matrix.ext; unfold raw42814step3 raw42814step2; decide +kernel
      have hl : raw42814step2Labels = labelEmbedding1 ∘ raw42814step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42814step2 raw42814step2Labels raw42814step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

theorem canonical42815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42815 raw42815Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw42815 raw42815Labels = mixedMoment B raw42815step0 raw42815step0Labels := by
      have hz : ∀ j, raw42815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42815step0 = (fun i j => raw42815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42815step0 raw42815; decide +kernel
      have hl : raw42815step0Labels = raw42815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42815 raw42815Labels permutation346 hz
    mixedMoment B raw42815step0 raw42815step0Labels = mixedMoment B raw42815step1 raw42815step1Labels := by
      have ha : raw42815step1 = (fun i j => raw42815step0 (permutation53 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42815step1 raw42815step0; decide +kernel
      have hl : raw42815step1Labels = raw42815step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42815step0 raw42815step0Labels permutation53 permutation6
    mixedMoment B raw42815step1 raw42815step1Labels = mixedMoment B raw42815step2 raw42815step2Labels := by
      have ha : raw42815step2 = -raw42815step1 := by apply Matrix.ext; change ∀ i j, raw42815step2 i j = -(raw42815step1 i j); unfold raw42815step2 raw42815step1; decide +kernel
      have hl : raw42815step2Labels = raw42815step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4600 node4600Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2720 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2720) =
      Integer.Sparse.eval keyMomentRow2720 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2720).leftCharge (GramAssembly.key 2720).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3475) := by
    have ha : gramCharges (GramAssembly.key 2720).leftCharge (GramAssembly.key 2720).rightCharge = raw42752 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42752Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42752 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2720).leftCharge (GramAssembly.key 2720).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4965) := by
    have ha : gramCharges (GramAssembly.key 2720).leftCharge (GramAssembly.key 2720).rightCharge = raw42753 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42753Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42753 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2720).leftCharge (GramAssembly.key 2720).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2720).leftCharge (GramAssembly.key 2720).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2720, Integer.Sparse.eval] <;> ring

theorem keyMoment2721 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2721) =
      Integer.Sparse.eval keyMomentRow2721 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2721).leftCharge (GramAssembly.key 2721).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3452) := by
    have ha : gramCharges (GramAssembly.key 2721).leftCharge (GramAssembly.key 2721).rightCharge = raw42754 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42754Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42754 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2721).leftCharge (GramAssembly.key 2721).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4954) := by
    have ha : gramCharges (GramAssembly.key 2721).leftCharge (GramAssembly.key 2721).rightCharge = raw42755 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42755Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42755 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2721).leftCharge (GramAssembly.key 2721).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2721).leftCharge (GramAssembly.key 2721).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2721, Integer.Sparse.eval] <;> ring

theorem keyMoment2722 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2722) =
      Integer.Sparse.eval keyMomentRow2722 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2722).leftCharge (GramAssembly.key 2722).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3474) := by
    have ha : gramCharges (GramAssembly.key 2722).leftCharge (GramAssembly.key 2722).rightCharge = raw42756 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42756Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42756 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2722).leftCharge (GramAssembly.key 2722).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5044) := by
    have ha : gramCharges (GramAssembly.key 2722).leftCharge (GramAssembly.key 2722).rightCharge = raw42757 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42757Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42757 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2722).leftCharge (GramAssembly.key 2722).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2722).leftCharge (GramAssembly.key 2722).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2722, Integer.Sparse.eval] <;> ring

theorem keyMoment2723 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2723) =
      Integer.Sparse.eval keyMomentRow2723 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2723).leftCharge (GramAssembly.key 2723).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3476) := by
    have ha : gramCharges (GramAssembly.key 2723).leftCharge (GramAssembly.key 2723).rightCharge = raw42758 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42758Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42758 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2723).leftCharge (GramAssembly.key 2723).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5067) := by
    have ha : gramCharges (GramAssembly.key 2723).leftCharge (GramAssembly.key 2723).rightCharge = raw42759 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42759Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42759 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2723).leftCharge (GramAssembly.key 2723).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2723).leftCharge (GramAssembly.key 2723).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2723, Integer.Sparse.eval] <;> ring

theorem keyMoment2724 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2724) =
      Integer.Sparse.eval keyMomentRow2724 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2724).leftCharge (GramAssembly.key 2724).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3461) := by
    have ha : gramCharges (GramAssembly.key 2724).leftCharge (GramAssembly.key 2724).rightCharge = raw42760 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42760Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42760 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2724).leftCharge (GramAssembly.key 2724).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5085) := by
    have ha : gramCharges (GramAssembly.key 2724).leftCharge (GramAssembly.key 2724).rightCharge = raw42761 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42761Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42761 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2724).leftCharge (GramAssembly.key 2724).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2724).leftCharge (GramAssembly.key 2724).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2724, Integer.Sparse.eval] <;> ring

theorem keyMoment2725 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2725) =
      Integer.Sparse.eval keyMomentRow2725 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2725).leftCharge (GramAssembly.key 2725).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3458) := by
    have ha : gramCharges (GramAssembly.key 2725).leftCharge (GramAssembly.key 2725).rightCharge = raw42762 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42762Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42762 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2725).leftCharge (GramAssembly.key 2725).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5041) := by
    have ha : gramCharges (GramAssembly.key 2725).leftCharge (GramAssembly.key 2725).rightCharge = raw42763 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42763Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42763 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2725).leftCharge (GramAssembly.key 2725).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2725).leftCharge (GramAssembly.key 2725).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2725, Integer.Sparse.eval] <;> ring

theorem keyMoment2726 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2726) =
      Integer.Sparse.eval keyMomentRow2726 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2726).leftCharge (GramAssembly.key 2726).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3472) := by
    have ha : gramCharges (GramAssembly.key 2726).leftCharge (GramAssembly.key 2726).rightCharge = raw42764 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42764Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42764 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2726).leftCharge (GramAssembly.key 2726).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5087) := by
    have ha : gramCharges (GramAssembly.key 2726).leftCharge (GramAssembly.key 2726).rightCharge = raw42765 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42765Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42765 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2726).leftCharge (GramAssembly.key 2726).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2726).leftCharge (GramAssembly.key 2726).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2726, Integer.Sparse.eval] <;> ring

theorem keyMoment2727 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2727) =
      Integer.Sparse.eval keyMomentRow2727 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2727).leftCharge (GramAssembly.key 2727).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3266) := by
    have ha : gramCharges (GramAssembly.key 2727).leftCharge (GramAssembly.key 2727).rightCharge = raw42766 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42766Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42766 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2727).leftCharge (GramAssembly.key 2727).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4547) := by
    have ha : gramCharges (GramAssembly.key 2727).leftCharge (GramAssembly.key 2727).rightCharge = raw42767 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42767Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42767 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2727).leftCharge (GramAssembly.key 2727).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2727).leftCharge (GramAssembly.key 2727).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2727, Integer.Sparse.eval] <;> ring

theorem keyMoment2728 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2728) =
      Integer.Sparse.eval keyMomentRow2728 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2728).leftCharge (GramAssembly.key 2728).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3260) := by
    have ha : gramCharges (GramAssembly.key 2728).leftCharge (GramAssembly.key 2728).rightCharge = raw42768 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42768Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42768 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2728).leftCharge (GramAssembly.key 2728).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4528) := by
    have ha : gramCharges (GramAssembly.key 2728).leftCharge (GramAssembly.key 2728).rightCharge = raw42769 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42769Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42769 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2728).leftCharge (GramAssembly.key 2728).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2728).leftCharge (GramAssembly.key 2728).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2728, Integer.Sparse.eval] <;> ring

theorem keyMoment2729 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2729) =
      Integer.Sparse.eval keyMomentRow2729 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2729).leftCharge (GramAssembly.key 2729).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3451) := by
    have ha : gramCharges (GramAssembly.key 2729).leftCharge (GramAssembly.key 2729).rightCharge = raw42770 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42770Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42770 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2729).leftCharge (GramAssembly.key 2729).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5034) := by
    have ha : gramCharges (GramAssembly.key 2729).leftCharge (GramAssembly.key 2729).rightCharge = raw42771 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42771Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42771 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2729).leftCharge (GramAssembly.key 2729).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2729).leftCharge (GramAssembly.key 2729).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2729, Integer.Sparse.eval] <;> ring

theorem keyMoment2730 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2730) =
      Integer.Sparse.eval keyMomentRow2730 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2730).leftCharge (GramAssembly.key 2730).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3466) := by
    have ha : gramCharges (GramAssembly.key 2730).leftCharge (GramAssembly.key 2730).rightCharge = raw42772 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42772Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42772 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2730).leftCharge (GramAssembly.key 2730).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5065) := by
    have ha : gramCharges (GramAssembly.key 2730).leftCharge (GramAssembly.key 2730).rightCharge = raw42773 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42773Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42773 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2730).leftCharge (GramAssembly.key 2730).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2730).leftCharge (GramAssembly.key 2730).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2730, Integer.Sparse.eval] <;> ring

theorem keyMoment2731 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2731) =
      Integer.Sparse.eval keyMomentRow2731 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2731).leftCharge (GramAssembly.key 2731).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3465) := by
    have ha : gramCharges (GramAssembly.key 2731).leftCharge (GramAssembly.key 2731).rightCharge = raw42774 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42774Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42774 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2731).leftCharge (GramAssembly.key 2731).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5043) := by
    have ha : gramCharges (GramAssembly.key 2731).leftCharge (GramAssembly.key 2731).rightCharge = raw42775 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42775Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42775 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2731).leftCharge (GramAssembly.key 2731).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2731).leftCharge (GramAssembly.key 2731).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2731, Integer.Sparse.eval] <;> ring

theorem keyMoment2732 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2732) =
      Integer.Sparse.eval keyMomentRow2732 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2732).leftCharge (GramAssembly.key 2732).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1729) := by
    have ha : gramCharges (GramAssembly.key 2732).leftCharge (GramAssembly.key 2732).rightCharge = raw42776 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42776Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42776 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2732).leftCharge (GramAssembly.key 2732).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4476) := by
    have ha : gramCharges (GramAssembly.key 2732).leftCharge (GramAssembly.key 2732).rightCharge = raw42777 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42777Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42777 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2732).leftCharge (GramAssembly.key 2732).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2732).leftCharge (GramAssembly.key 2732).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2732, Integer.Sparse.eval] <;> ring

theorem keyMoment2733 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2733) =
      Integer.Sparse.eval keyMomentRow2733 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2733).leftCharge (GramAssembly.key 2733).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1520) := by
    have ha : gramCharges (GramAssembly.key 2733).leftCharge (GramAssembly.key 2733).rightCharge = raw42778 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42778Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42778 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2733).leftCharge (GramAssembly.key 2733).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4178) := by
    have ha : gramCharges (GramAssembly.key 2733).leftCharge (GramAssembly.key 2733).rightCharge = raw42779 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42779Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42779 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2733).leftCharge (GramAssembly.key 2733).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2733).leftCharge (GramAssembly.key 2733).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2733, Integer.Sparse.eval] <;> ring

theorem keyMoment2734 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2734) =
      Integer.Sparse.eval keyMomentRow2734 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2734).leftCharge (GramAssembly.key 2734).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1514) := by
    have ha : gramCharges (GramAssembly.key 2734).leftCharge (GramAssembly.key 2734).rightCharge = raw42780 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42780Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42780 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2734).leftCharge (GramAssembly.key 2734).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4153) := by
    have ha : gramCharges (GramAssembly.key 2734).leftCharge (GramAssembly.key 2734).rightCharge = raw42781 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42781Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42781 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2734).leftCharge (GramAssembly.key 2734).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2734).leftCharge (GramAssembly.key 2734).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2734, Integer.Sparse.eval] <;> ring

theorem keyMoment2735 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2735) =
      Integer.Sparse.eval keyMomentRow2735 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2735).leftCharge (GramAssembly.key 2735).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1676) := by
    have ha : gramCharges (GramAssembly.key 2735).leftCharge (GramAssembly.key 2735).rightCharge = raw42782 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42782Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42782 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2735).leftCharge (GramAssembly.key 2735).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4347) := by
    have ha : gramCharges (GramAssembly.key 2735).leftCharge (GramAssembly.key 2735).rightCharge = raw42783 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42783Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42783 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2735).leftCharge (GramAssembly.key 2735).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2735).leftCharge (GramAssembly.key 2735).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2735, Integer.Sparse.eval] <;> ring

theorem keyMoment2736 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2736) =
      Integer.Sparse.eval keyMomentRow2736 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2736).leftCharge (GramAssembly.key 2736).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1723) := by
    have ha : gramCharges (GramAssembly.key 2736).leftCharge (GramAssembly.key 2736).rightCharge = raw42784 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42784Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42784 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2736).leftCharge (GramAssembly.key 2736).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4440) := by
    have ha : gramCharges (GramAssembly.key 2736).leftCharge (GramAssembly.key 2736).rightCharge = raw42785 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42785Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42785 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2736).leftCharge (GramAssembly.key 2736).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2736).leftCharge (GramAssembly.key 2736).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2736, Integer.Sparse.eval] <;> ring

theorem keyMoment2737 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2737) =
      Integer.Sparse.eval keyMomentRow2737 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2737).leftCharge (GramAssembly.key 2737).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3413) := by
    have ha : gramCharges (GramAssembly.key 2737).leftCharge (GramAssembly.key 2737).rightCharge = raw42786 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42786Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42786 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2737).leftCharge (GramAssembly.key 2737).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4944) := by
    have ha : gramCharges (GramAssembly.key 2737).leftCharge (GramAssembly.key 2737).rightCharge = raw42787 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42787Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42787 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2737).leftCharge (GramAssembly.key 2737).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2737).leftCharge (GramAssembly.key 2737).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2737, Integer.Sparse.eval] <;> ring

theorem keyMoment2738 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2738) =
      Integer.Sparse.eval keyMomentRow2738 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2738).leftCharge (GramAssembly.key 2738).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1670) := by
    have ha : gramCharges (GramAssembly.key 2738).leftCharge (GramAssembly.key 2738).rightCharge = raw42788 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42788Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42788 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2738).leftCharge (GramAssembly.key 2738).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4327) := by
    have ha : gramCharges (GramAssembly.key 2738).leftCharge (GramAssembly.key 2738).rightCharge = raw42789 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42789Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42789 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2738).leftCharge (GramAssembly.key 2738).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2738).leftCharge (GramAssembly.key 2738).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2738, Integer.Sparse.eval] <;> ring

theorem keyMoment2739 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2739) =
      Integer.Sparse.eval keyMomentRow2739 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2739).leftCharge (GramAssembly.key 2739).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3408) := by
    have ha : gramCharges (GramAssembly.key 2739).leftCharge (GramAssembly.key 2739).rightCharge = raw42790 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42790Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42790 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2739).leftCharge (GramAssembly.key 2739).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4930) := by
    have ha : gramCharges (GramAssembly.key 2739).leftCharge (GramAssembly.key 2739).rightCharge = raw42791 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42791Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42791 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2739).leftCharge (GramAssembly.key 2739).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2739).leftCharge (GramAssembly.key 2739).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2739, Integer.Sparse.eval] <;> ring

theorem keyMoment2740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2740) =
      Integer.Sparse.eval keyMomentRow2740 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2740).leftCharge (GramAssembly.key 2740).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2164) := by
    have ha : gramCharges (GramAssembly.key 2740).leftCharge (GramAssembly.key 2740).rightCharge = raw42792 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42792Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42792 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2740).leftCharge (GramAssembly.key 2740).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4670) := by
    have ha : gramCharges (GramAssembly.key 2740).leftCharge (GramAssembly.key 2740).rightCharge = raw42793 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42793Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42793 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2740).leftCharge (GramAssembly.key 2740).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2740).leftCharge (GramAssembly.key 2740).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2740, Integer.Sparse.eval] <;> ring

theorem keyMoment2741 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2741) =
      Integer.Sparse.eval keyMomentRow2741 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2741).leftCharge (GramAssembly.key 2741).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2181) := by
    have ha : gramCharges (GramAssembly.key 2741).leftCharge (GramAssembly.key 2741).rightCharge = raw42794 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42794Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42794 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2741).leftCharge (GramAssembly.key 2741).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4757) := by
    have ha : gramCharges (GramAssembly.key 2741).leftCharge (GramAssembly.key 2741).rightCharge = raw42795 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42795Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42795 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2741).leftCharge (GramAssembly.key 2741).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2741).leftCharge (GramAssembly.key 2741).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2741, Integer.Sparse.eval] <;> ring

theorem keyMoment2742 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2742) =
      Integer.Sparse.eval keyMomentRow2742 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2742).leftCharge (GramAssembly.key 2742).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3406) := by
    have ha : gramCharges (GramAssembly.key 2742).leftCharge (GramAssembly.key 2742).rightCharge = raw42796 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42796Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42796 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2742).leftCharge (GramAssembly.key 2742).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4931) := by
    have ha : gramCharges (GramAssembly.key 2742).leftCharge (GramAssembly.key 2742).rightCharge = raw42797 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42797Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42797 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2742).leftCharge (GramAssembly.key 2742).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2742).leftCharge (GramAssembly.key 2742).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2742, Integer.Sparse.eval] <;> ring

theorem keyMoment2743 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2743) =
      Integer.Sparse.eval keyMomentRow2743 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2743).leftCharge (GramAssembly.key 2743).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3415) := by
    have ha : gramCharges (GramAssembly.key 2743).leftCharge (GramAssembly.key 2743).rightCharge = raw42798 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42798Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42798 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2743).leftCharge (GramAssembly.key 2743).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4934) := by
    have ha : gramCharges (GramAssembly.key 2743).leftCharge (GramAssembly.key 2743).rightCharge = raw42799 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42799Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42799 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2743).leftCharge (GramAssembly.key 2743).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2743).leftCharge (GramAssembly.key 2743).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2743, Integer.Sparse.eval] <;> ring

theorem keyMoment2744 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2744) =
      Integer.Sparse.eval keyMomentRow2744 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2744).leftCharge (GramAssembly.key 2744).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3414) := by
    have ha : gramCharges (GramAssembly.key 2744).leftCharge (GramAssembly.key 2744).rightCharge = raw42800 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42800Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42800 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2744).leftCharge (GramAssembly.key 2744).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4933) := by
    have ha : gramCharges (GramAssembly.key 2744).leftCharge (GramAssembly.key 2744).rightCharge = raw42801 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42801Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42801 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2744).leftCharge (GramAssembly.key 2744).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2744).leftCharge (GramAssembly.key 2744).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2744, Integer.Sparse.eval] <;> ring

theorem keyMoment2745 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2745) =
      Integer.Sparse.eval keyMomentRow2745 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2745).leftCharge (GramAssembly.key 2745).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3272) := by
    have ha : gramCharges (GramAssembly.key 2745).leftCharge (GramAssembly.key 2745).rightCharge = raw42802 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42802Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42802 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2745).leftCharge (GramAssembly.key 2745).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4535) := by
    have ha : gramCharges (GramAssembly.key 2745).leftCharge (GramAssembly.key 2745).rightCharge = raw42803 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42803Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42803 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2745).leftCharge (GramAssembly.key 2745).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2745).leftCharge (GramAssembly.key 2745).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2745, Integer.Sparse.eval] <;> ring

theorem keyMoment2746 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2746) =
      Integer.Sparse.eval keyMomentRow2746 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2746).leftCharge (GramAssembly.key 2746).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3408) := by
    have ha : gramCharges (GramAssembly.key 2746).leftCharge (GramAssembly.key 2746).rightCharge = raw42804 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42804Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42804 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2746).leftCharge (GramAssembly.key 2746).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4930) := by
    have ha : gramCharges (GramAssembly.key 2746).leftCharge (GramAssembly.key 2746).rightCharge = raw42805 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42805Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42805 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2746).leftCharge (GramAssembly.key 2746).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2746).leftCharge (GramAssembly.key 2746).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2746, Integer.Sparse.eval] <;> ring

theorem keyMoment2747 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2747) =
      Integer.Sparse.eval keyMomentRow2747 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2747).leftCharge (GramAssembly.key 2747).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1533) := by
    have ha : gramCharges (GramAssembly.key 2747).leftCharge (GramAssembly.key 2747).rightCharge = raw42806 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42806Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42806 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2747).leftCharge (GramAssembly.key 2747).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4161) := by
    have ha : gramCharges (GramAssembly.key 2747).leftCharge (GramAssembly.key 2747).rightCharge = raw42807 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42807Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42807 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2747).leftCharge (GramAssembly.key 2747).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2747).leftCharge (GramAssembly.key 2747).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2747, Integer.Sparse.eval] <;> ring

theorem keyMoment2748 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2748) =
      Integer.Sparse.eval keyMomentRow2748 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2748).leftCharge (GramAssembly.key 2748).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1689) := by
    have ha : gramCharges (GramAssembly.key 2748).leftCharge (GramAssembly.key 2748).rightCharge = raw42808 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42808Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42808 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2748).leftCharge (GramAssembly.key 2748).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4335) := by
    have ha : gramCharges (GramAssembly.key 2748).leftCharge (GramAssembly.key 2748).rightCharge = raw42809 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42809Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42809 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2748).leftCharge (GramAssembly.key 2748).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2748).leftCharge (GramAssembly.key 2748).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2748, Integer.Sparse.eval] <;> ring

theorem keyMoment2749 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2749) =
      Integer.Sparse.eval keyMomentRow2749 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2749).leftCharge (GramAssembly.key 2749).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3419) := by
    have ha : gramCharges (GramAssembly.key 2749).leftCharge (GramAssembly.key 2749).rightCharge = raw42810 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42810Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42810 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2749).leftCharge (GramAssembly.key 2749).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4935) := by
    have ha : gramCharges (GramAssembly.key 2749).leftCharge (GramAssembly.key 2749).rightCharge = raw42811 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42811Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42811 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2749).leftCharge (GramAssembly.key 2749).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2749).leftCharge (GramAssembly.key 2749).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2749, Integer.Sparse.eval] <;> ring

theorem keyMoment2750 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2750) =
      Integer.Sparse.eval keyMomentRow2750 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2750).leftCharge (GramAssembly.key 2750).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2683) := by
    have ha : gramCharges (GramAssembly.key 2750).leftCharge (GramAssembly.key 2750).rightCharge = raw42812 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42812Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42812 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2750).leftCharge (GramAssembly.key 2750).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4611) := by
    have ha : gramCharges (GramAssembly.key 2750).leftCharge (GramAssembly.key 2750).rightCharge = raw42813 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42813Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42813 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2750).leftCharge (GramAssembly.key 2750).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2750).leftCharge (GramAssembly.key 2750).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2750, Integer.Sparse.eval] <;> ring

theorem keyMoment2751 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2751) =
      Integer.Sparse.eval keyMomentRow2751 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2751).leftCharge (GramAssembly.key 2751).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2702) := by
    have ha : gramCharges (GramAssembly.key 2751).leftCharge (GramAssembly.key 2751).rightCharge = raw42814 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42814Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42814 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2751).leftCharge (GramAssembly.key 2751).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4600) := by
    have ha : gramCharges (GramAssembly.key 2751).leftCharge (GramAssembly.key 2751).rightCharge = raw42815 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42815Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42815 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2751).leftCharge (GramAssembly.key 2751).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2751).leftCharge (GramAssembly.key 2751).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2751, Integer.Sparse.eval] <;> ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2720 : keyMomentRows (2720 : Fin 2886) =
    keyMomentRow2720 := by decide +kernel

theorem keyMomentRowsAt2721 : keyMomentRows (2721 : Fin 2886) =
    keyMomentRow2721 := by decide +kernel

theorem keyMomentRowsAt2722 : keyMomentRows (2722 : Fin 2886) =
    keyMomentRow2722 := by decide +kernel

theorem keyMomentRowsAt2723 : keyMomentRows (2723 : Fin 2886) =
    keyMomentRow2723 := by decide +kernel

theorem keyMomentRowsAt2724 : keyMomentRows (2724 : Fin 2886) =
    keyMomentRow2724 := by decide +kernel

theorem keyMomentRowsAt2725 : keyMomentRows (2725 : Fin 2886) =
    keyMomentRow2725 := by decide +kernel

theorem keyMomentRowsAt2726 : keyMomentRows (2726 : Fin 2886) =
    keyMomentRow2726 := by decide +kernel

theorem keyMomentRowsAt2727 : keyMomentRows (2727 : Fin 2886) =
    keyMomentRow2727 := by decide +kernel

theorem keyMomentRowsAt2728 : keyMomentRows (2728 : Fin 2886) =
    keyMomentRow2728 := by decide +kernel

theorem keyMomentRowsAt2729 : keyMomentRows (2729 : Fin 2886) =
    keyMomentRow2729 := by decide +kernel

theorem keyMomentRowsAt2730 : keyMomentRows (2730 : Fin 2886) =
    keyMomentRow2730 := by decide +kernel

theorem keyMomentRowsAt2731 : keyMomentRows (2731 : Fin 2886) =
    keyMomentRow2731 := by decide +kernel

theorem keyMomentRowsAt2732 : keyMomentRows (2732 : Fin 2886) =
    keyMomentRow2732 := by decide +kernel

theorem keyMomentRowsAt2733 : keyMomentRows (2733 : Fin 2886) =
    keyMomentRow2733 := by decide +kernel

theorem keyMomentRowsAt2734 : keyMomentRows (2734 : Fin 2886) =
    keyMomentRow2734 := by decide +kernel

theorem keyMomentRowsAt2735 : keyMomentRows (2735 : Fin 2886) =
    keyMomentRow2735 := by decide +kernel

theorem keyMomentRowsAt2736 : keyMomentRows (2736 : Fin 2886) =
    keyMomentRow2736 := by decide +kernel

theorem keyMomentRowsAt2737 : keyMomentRows (2737 : Fin 2886) =
    keyMomentRow2737 := by decide +kernel

theorem keyMomentRowsAt2738 : keyMomentRows (2738 : Fin 2886) =
    keyMomentRow2738 := by decide +kernel

theorem keyMomentRowsAt2739 : keyMomentRows (2739 : Fin 2886) =
    keyMomentRow2739 := by decide +kernel

theorem keyMomentRowsAt2740 : keyMomentRows (2740 : Fin 2886) =
    keyMomentRow2740 := by decide +kernel

theorem keyMomentRowsAt2741 : keyMomentRows (2741 : Fin 2886) =
    keyMomentRow2741 := by decide +kernel

theorem keyMomentRowsAt2742 : keyMomentRows (2742 : Fin 2886) =
    keyMomentRow2742 := by decide +kernel

theorem keyMomentRowsAt2743 : keyMomentRows (2743 : Fin 2886) =
    keyMomentRow2743 := by decide +kernel

theorem keyMomentRowsAt2744 : keyMomentRows (2744 : Fin 2886) =
    keyMomentRow2744 := by decide +kernel

theorem keyMomentRowsAt2745 : keyMomentRows (2745 : Fin 2886) =
    keyMomentRow2745 := by decide +kernel

theorem keyMomentRowsAt2746 : keyMomentRows (2746 : Fin 2886) =
    keyMomentRow2746 := by decide +kernel

theorem keyMomentRowsAt2747 : keyMomentRows (2747 : Fin 2886) =
    keyMomentRow2747 := by decide +kernel

theorem keyMomentRowsAt2748 : keyMomentRows (2748 : Fin 2886) =
    keyMomentRow2748 := by decide +kernel

theorem keyMomentRowsAt2749 : keyMomentRows (2749 : Fin 2886) =
    keyMomentRow2749 := by decide +kernel

theorem keyMomentRowsAt2750 : keyMomentRows (2750 : Fin 2886) =
    keyMomentRow2750 := by decide +kernel

theorem keyMomentRowsAt2751 : keyMomentRows (2751 : Fin 2886) =
    keyMomentRow2751 := by decide +kernel

theorem keyMomentChunkSound85_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 85) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2720 ∨ k.val = 2721 ∨ k.val = 2722 ∨ k.val = 2723 ∨ k.val = 2724 ∨ k.val = 2725 ∨ k.val = 2726 ∨ k.val = 2727 ∨ k.val = 2728 ∨ k.val = 2729 ∨ k.val = 2730 ∨ k.val = 2731 ∨ k.val = 2732 ∨ k.val = 2733 ∨ k.val = 2734 ∨ k.val = 2735 ∨ k.val = 2736 ∨ k.val = 2737 ∨ k.val = 2738 ∨ k.val = 2739 ∨ k.val = 2740 ∨ k.val = 2741 ∨ k.val = 2742 ∨ k.val = 2743 ∨ k.val = 2744 ∨ k.val = 2745 ∨ k.val = 2746 ∨ k.val = 2747 ∨ k.val = 2748 ∨ k.val = 2749 ∨ k.val = 2750 ∨ k.val = 2751 := by omega
  rcases heq with h2720 | h2721 | h2722 | h2723 | h2724 | h2725 | h2726 | h2727 | h2728 | h2729 | h2730 | h2731 | h2732 | h2733 | h2734 | h2735 | h2736 | h2737 | h2738 | h2739 | h2740 | h2741 | h2742 | h2743 | h2744 | h2745 | h2746 | h2747 | h2748 | h2749 | h2750 | h2751
  · have he : k = (2720 : Fin 2886) := Fin.ext h2720
    subst k
    rw [keyMomentRowsAt2720]
    exact keyMoment2720 B hB
  · have he : k = (2721 : Fin 2886) := Fin.ext h2721
    subst k
    rw [keyMomentRowsAt2721]
    exact keyMoment2721 B hB
  · have he : k = (2722 : Fin 2886) := Fin.ext h2722
    subst k
    rw [keyMomentRowsAt2722]
    exact keyMoment2722 B hB
  · have he : k = (2723 : Fin 2886) := Fin.ext h2723
    subst k
    rw [keyMomentRowsAt2723]
    exact keyMoment2723 B hB
  · have he : k = (2724 : Fin 2886) := Fin.ext h2724
    subst k
    rw [keyMomentRowsAt2724]
    exact keyMoment2724 B hB
  · have he : k = (2725 : Fin 2886) := Fin.ext h2725
    subst k
    rw [keyMomentRowsAt2725]
    exact keyMoment2725 B hB
  · have he : k = (2726 : Fin 2886) := Fin.ext h2726
    subst k
    rw [keyMomentRowsAt2726]
    exact keyMoment2726 B hB
  · have he : k = (2727 : Fin 2886) := Fin.ext h2727
    subst k
    rw [keyMomentRowsAt2727]
    exact keyMoment2727 B hB
  · have he : k = (2728 : Fin 2886) := Fin.ext h2728
    subst k
    rw [keyMomentRowsAt2728]
    exact keyMoment2728 B hB
  · have he : k = (2729 : Fin 2886) := Fin.ext h2729
    subst k
    rw [keyMomentRowsAt2729]
    exact keyMoment2729 B hB
  · have he : k = (2730 : Fin 2886) := Fin.ext h2730
    subst k
    rw [keyMomentRowsAt2730]
    exact keyMoment2730 B hB
  · have he : k = (2731 : Fin 2886) := Fin.ext h2731
    subst k
    rw [keyMomentRowsAt2731]
    exact keyMoment2731 B hB
  · have he : k = (2732 : Fin 2886) := Fin.ext h2732
    subst k
    rw [keyMomentRowsAt2732]
    exact keyMoment2732 B hB
  · have he : k = (2733 : Fin 2886) := Fin.ext h2733
    subst k
    rw [keyMomentRowsAt2733]
    exact keyMoment2733 B hB
  · have he : k = (2734 : Fin 2886) := Fin.ext h2734
    subst k
    rw [keyMomentRowsAt2734]
    exact keyMoment2734 B hB
  · have he : k = (2735 : Fin 2886) := Fin.ext h2735
    subst k
    rw [keyMomentRowsAt2735]
    exact keyMoment2735 B hB
  · have he : k = (2736 : Fin 2886) := Fin.ext h2736
    subst k
    rw [keyMomentRowsAt2736]
    exact keyMoment2736 B hB
  · have he : k = (2737 : Fin 2886) := Fin.ext h2737
    subst k
    rw [keyMomentRowsAt2737]
    exact keyMoment2737 B hB
  · have he : k = (2738 : Fin 2886) := Fin.ext h2738
    subst k
    rw [keyMomentRowsAt2738]
    exact keyMoment2738 B hB
  · have he : k = (2739 : Fin 2886) := Fin.ext h2739
    subst k
    rw [keyMomentRowsAt2739]
    exact keyMoment2739 B hB
  · have he : k = (2740 : Fin 2886) := Fin.ext h2740
    subst k
    rw [keyMomentRowsAt2740]
    exact keyMoment2740 B hB
  · have he : k = (2741 : Fin 2886) := Fin.ext h2741
    subst k
    rw [keyMomentRowsAt2741]
    exact keyMoment2741 B hB
  · have he : k = (2742 : Fin 2886) := Fin.ext h2742
    subst k
    rw [keyMomentRowsAt2742]
    exact keyMoment2742 B hB
  · have he : k = (2743 : Fin 2886) := Fin.ext h2743
    subst k
    rw [keyMomentRowsAt2743]
    exact keyMoment2743 B hB
  · have he : k = (2744 : Fin 2886) := Fin.ext h2744
    subst k
    rw [keyMomentRowsAt2744]
    exact keyMoment2744 B hB
  · have he : k = (2745 : Fin 2886) := Fin.ext h2745
    subst k
    rw [keyMomentRowsAt2745]
    exact keyMoment2745 B hB
  · have he : k = (2746 : Fin 2886) := Fin.ext h2746
    subst k
    rw [keyMomentRowsAt2746]
    exact keyMoment2746 B hB
  · have he : k = (2747 : Fin 2886) := Fin.ext h2747
    subst k
    rw [keyMomentRowsAt2747]
    exact keyMoment2747 B hB
  · have he : k = (2748 : Fin 2886) := Fin.ext h2748
    subst k
    rw [keyMomentRowsAt2748]
    exact keyMoment2748 B hB
  · have he : k = (2749 : Fin 2886) := Fin.ext h2749
    subst k
    rw [keyMomentRowsAt2749]
    exact keyMoment2749 B hB
  · have he : k = (2750 : Fin 2886) := Fin.ext h2750
    subst k
    rw [keyMomentRowsAt2750]
    exact keyMoment2750 B hB
  · have he : k = (2751 : Fin 2886) := Fin.ext h2751
    subst k
    rw [keyMomentRowsAt2751]
    exact keyMoment2751 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound85_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound85_e_oai
