-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound86_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:14:45.658203+00:00
-- url     : https://prove2.me/submissions/d4e2d33b-e8cf-4563-9928-c1f0d1220ca5

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

theorem canonical42816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42816 raw42816Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw42816 raw42816Labels = mixedMoment B raw42816step0 raw42816step0Labels := by
      have hz : ∀ j, raw42816 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42816step0 = (fun i j => raw42816 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42816step0 raw42816; decide +kernel
      have hl : raw42816step0Labels = raw42816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42816 raw42816Labels permutation434 hz
    mixedMoment B raw42816step0 raw42816step0Labels = mixedMoment B raw42816step1 raw42816step1Labels := by
      have ha : raw42816step1 = (fun i j => raw42816step0 (permutation49 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42816step1 raw42816step0; decide +kernel
      have hl : raw42816step1Labels = raw42816step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42816step0 raw42816step0Labels permutation49 permutation4
    mixedMoment B raw42816step1 raw42816step1Labels = mixedMoment B raw42816step2 raw42816step2Labels := by
      have ha : raw42816step2 = raw42816step1 := by apply Matrix.ext; unfold raw42816step2 raw42816step1; decide +kernel
      have hl : raw42816step1Labels = labelEmbedding1 ∘ raw42816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42816step1 raw42816step1Labels raw42816step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

theorem canonical42817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42817 raw42817Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw42817 raw42817Labels = mixedMoment B raw42817step0 raw42817step0Labels := by
      have hz : ∀ j, raw42817 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42817step0 = (fun i j => raw42817 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42817step0 raw42817; decide +kernel
      have hl : raw42817step0Labels = raw42817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42817 raw42817Labels permutation434 hz
    mixedMoment B raw42817step0 raw42817step0Labels = mixedMoment B raw42817step1 raw42817step1Labels := by
      have ha : raw42817step1 = (fun i j => raw42817step0 (permutation46 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42817step1 raw42817step0; decide +kernel
      have hl : raw42817step1Labels = raw42817step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42817step0 raw42817step0Labels permutation46 permutation6
    mixedMoment B raw42817step1 raw42817step1Labels = mixedMoment B raw42817step2 raw42817step2Labels := by
      have ha : raw42817step2 = -raw42817step1 := by apply Matrix.ext; change ∀ i j, raw42817step2 i j = -(raw42817step1 i j); unfold raw42817step2 raw42817step1; decide +kernel
      have hl : raw42817step2Labels = raw42817step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4607 node4607Labels := by rfl

theorem canonical42818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42818 raw42818Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw42818 raw42818Labels = mixedMoment B raw42818step0 raw42818step0Labels := by
      have ha : raw42818step0 = (fun i j => raw42818 (permutation259 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42818step0 raw42818; decide +kernel
      have hl : raw42818step0Labels = raw42818Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42818 raw42818Labels permutation259 permutation4
    mixedMoment B raw42818step0 raw42818step0Labels = mixedMoment B raw42818step1 raw42818step1Labels := by
      have ha : raw42818step1 = raw42818step0 := by apply Matrix.ext; unfold raw42818step1 raw42818step0; decide +kernel
      have hl : raw42818step0Labels = labelEmbedding1 ∘ raw42818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42818step0 raw42818step0Labels raw42818step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical42819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42819 raw42819Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw42819 raw42819Labels = mixedMoment B raw42819step0 raw42819step0Labels := by
      have ha : raw42819step0 = (fun i j => raw42819 (permutation259 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42819step0 raw42819; decide +kernel
      have hl : raw42819step0Labels = raw42819Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42819 raw42819Labels permutation259 permutation6
    mixedMoment B raw42819step0 raw42819step0Labels = mixedMoment B raw42819step1 raw42819step1Labels := by
      have ha : raw42819step1 = -raw42819step0 := by apply Matrix.ext; change ∀ i j, raw42819step1 i j = -(raw42819step0 i j); unfold raw42819step1 raw42819step0; decide +kernel
      have hl : raw42819step1Labels = raw42819step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4599 node4599Labels := by rfl

theorem canonical42820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42820 raw42820Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw42820 raw42820Labels = mixedMoment B raw42820step0 raw42820step0Labels := by
      have hz : ∀ j, raw42820 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42820step0 = (fun i j => raw42820 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42820step0 raw42820; decide +kernel
      have hl : raw42820step0Labels = raw42820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42820 raw42820Labels permutation434 hz
    mixedMoment B raw42820step0 raw42820step0Labels = mixedMoment B raw42820step1 raw42820step1Labels := by
      have hz : ∀ j, raw42820step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42820step1 = (fun i j => raw42820step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42820step1 raw42820step0; decide +kernel
      have hl : raw42820step1Labels = raw42820step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42820step0 raw42820step0Labels permutation80 hz
    mixedMoment B raw42820step1 raw42820step1Labels = mixedMoment B raw42820step2 raw42820step2Labels := by
      have ha : raw42820step2 = (fun i j => raw42820step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42820step2 raw42820step1; decide +kernel
      have hl : raw42820step2Labels = raw42820step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42820step1 raw42820step1Labels permutation11 permutation4
    mixedMoment B raw42820step2 raw42820step2Labels = mixedMoment B raw42820step3 raw42820step3Labels := by
      have ha : raw42820step3 = raw42820step2 := by apply Matrix.ext; unfold raw42820step3 raw42820step2; decide +kernel
      have hl : raw42820step2Labels = labelEmbedding1 ∘ raw42820step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42820step2 raw42820step2Labels raw42820step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

theorem canonical42821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42821 raw42821Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw42821 raw42821Labels = mixedMoment B raw42821step0 raw42821step0Labels := by
      have hz : ∀ j, raw42821 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42821step0 = (fun i j => raw42821 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42821step0 raw42821; decide +kernel
      have hl : raw42821step0Labels = raw42821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42821 raw42821Labels permutation434 hz
    mixedMoment B raw42821step0 raw42821step0Labels = mixedMoment B raw42821step1 raw42821step1Labels := by
      have hz : ∀ j, raw42821step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42821step1 = (fun i j => raw42821step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42821step1 raw42821step0; decide +kernel
      have hl : raw42821step1Labels = raw42821step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42821step0 raw42821step0Labels permutation80 hz
    mixedMoment B raw42821step1 raw42821step1Labels = mixedMoment B raw42821step2 raw42821step2Labels := by
      have ha : raw42821step2 = (fun i j => raw42821step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42821step2 raw42821step1; decide +kernel
      have hl : raw42821step2Labels = raw42821step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42821step1 raw42821step1Labels permutation10 permutation6
    mixedMoment B raw42821step2 raw42821step2Labels = mixedMoment B raw42821step3 raw42821step3Labels := by
      have ha : raw42821step3 = -raw42821step2 := by apply Matrix.ext; change ∀ i j, raw42821step3 i j = -(raw42821step2 i j); unfold raw42821step3 raw42821step2; decide +kernel
      have hl : raw42821step3Labels = raw42821step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4609 node4609Labels := by rfl

theorem canonical42822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42822 raw42822Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw42822 raw42822Labels = mixedMoment B raw42822step0 raw42822step0Labels := by
      have hz : ∀ j, raw42822 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42822step0 = (fun i j => raw42822 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42822step0 raw42822; decide +kernel
      have hl : raw42822step0Labels = raw42822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42822 raw42822Labels permutation346 hz
    mixedMoment B raw42822step0 raw42822step0Labels = mixedMoment B raw42822step1 raw42822step1Labels := by
      have ha : raw42822step1 = (fun i j => raw42822step0 (permutation55 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42822step1 raw42822step0; decide +kernel
      have hl : raw42822step1Labels = raw42822step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42822step0 raw42822step0Labels permutation55 permutation4
    mixedMoment B raw42822step1 raw42822step1Labels = mixedMoment B raw42822step2 raw42822step2Labels := by
      have ha : raw42822step2 = raw42822step1 := by apply Matrix.ext; unfold raw42822step2 raw42822step1; decide +kernel
      have hl : raw42822step1Labels = labelEmbedding1 ∘ raw42822step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42822step1 raw42822step1Labels raw42822step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical42823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42823 raw42823Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw42823 raw42823Labels = mixedMoment B raw42823step0 raw42823step0Labels := by
      have hz : ∀ j, raw42823 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42823step0 = (fun i j => raw42823 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42823step0 raw42823; decide +kernel
      have hl : raw42823step0Labels = raw42823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42823 raw42823Labels permutation346 hz
    mixedMoment B raw42823step0 raw42823step0Labels = mixedMoment B raw42823step1 raw42823step1Labels := by
      have ha : raw42823step1 = (fun i j => raw42823step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42823step1 raw42823step0; decide +kernel
      have hl : raw42823step1Labels = raw42823step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42823step0 raw42823step0Labels permutation54 permutation6
    mixedMoment B raw42823step1 raw42823step1Labels = mixedMoment B raw42823step2 raw42823step2Labels := by
      have ha : raw42823step2 = -raw42823step1 := by apply Matrix.ext; change ∀ i j, raw42823step2 i j = -(raw42823step1 i j); unfold raw42823step2 raw42823step1; decide +kernel
      have hl : raw42823step2Labels = raw42823step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4603 node4603Labels := by rfl

theorem canonical42824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42824 raw42824Labels = mixedMoment B node3295 node3295Labels := by
  calc
    mixedMoment B raw42824 raw42824Labels = mixedMoment B raw42824step0 raw42824step0Labels := by
      have hz : ∀ j, raw42824 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42824step0 = (fun i j => raw42824 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42824step0 raw42824; decide +kernel
      have hl : raw42824step0Labels = raw42824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42824 raw42824Labels permutation434 hz
    mixedMoment B raw42824step0 raw42824step0Labels = mixedMoment B raw42824step1 raw42824step1Labels := by
      have ha : raw42824step1 = raw42824step0 := by apply Matrix.ext; unfold raw42824step1 raw42824step0; decide +kernel
      have hl : raw42824step0Labels = labelEmbedding1 ∘ raw42824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42824step0 raw42824step0Labels raw42824step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3295 node3295Labels := by rfl

theorem canonical42825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42825 raw42825Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw42825 raw42825Labels = mixedMoment B raw42825step0 raw42825step0Labels := by
      have hz : ∀ j, raw42825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42825step0 = (fun i j => raw42825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42825step0 raw42825; decide +kernel
      have hl : raw42825step0Labels = raw42825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42825 raw42825Labels permutation434 hz
    mixedMoment B raw42825step0 raw42825step0Labels = mixedMoment B raw42825step1 raw42825step1Labels := by
      have ha : raw42825step1 = (fun i j => raw42825step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42825step1 raw42825step0; decide +kernel
      have hl : raw42825step1Labels = raw42825step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42825step0 raw42825step0Labels permutation45 permutation6
    mixedMoment B raw42825step1 raw42825step1Labels = mixedMoment B raw42825step2 raw42825step2Labels := by
      have ha : raw42825step2 = -raw42825step1 := by apply Matrix.ext; change ∀ i j, raw42825step2 i j = -(raw42825step1 i j); unfold raw42825step2 raw42825step1; decide +kernel
      have hl : raw42825step2Labels = raw42825step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4592 node4592Labels := by rfl

theorem canonical42826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42826 raw42826Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw42826 raw42826Labels = mixedMoment B raw42826step0 raw42826step0Labels := by
      have ha : raw42826step0 = (fun i j => raw42826 (permutation258 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42826step0 raw42826; decide +kernel
      have hl : raw42826step0Labels = raw42826Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42826 raw42826Labels permutation258 permutation4
    mixedMoment B raw42826step0 raw42826step0Labels = mixedMoment B raw42826step1 raw42826step1Labels := by
      have ha : raw42826step1 = raw42826step0 := by apply Matrix.ext; unfold raw42826step1 raw42826step0; decide +kernel
      have hl : raw42826step0Labels = labelEmbedding1 ∘ raw42826step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42826step0 raw42826step0Labels raw42826step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

theorem canonical42827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42827 raw42827Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw42827 raw42827Labels = mixedMoment B raw42827step0 raw42827step0Labels := by
      have ha : raw42827step0 = (fun i j => raw42827 (permutation249 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42827step0 raw42827; decide +kernel
      have hl : raw42827step0Labels = raw42827Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42827 raw42827Labels permutation249 permutation6
    mixedMoment B raw42827step0 raw42827step0Labels = mixedMoment B raw42827step1 raw42827step1Labels := by
      have ha : raw42827step1 = -raw42827step0 := by apply Matrix.ext; change ∀ i j, raw42827step1 i j = -(raw42827step0 i j); unfold raw42827step1 raw42827step0; decide +kernel
      have hl : raw42827step1Labels = raw42827step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4589 node4589Labels := by rfl

theorem canonical42828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42828 raw42828Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw42828 raw42828Labels = mixedMoment B raw42828step0 raw42828step0Labels := by
      have ha : raw42828step0 = raw42828 := by apply Matrix.ext; unfold raw42828step0 raw42828; decide +kernel
      have hl : raw42828Labels = labelEmbedding1 ∘ raw42828step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42828 raw42828Labels raw42828step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

theorem canonical42829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42829 raw42829Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw42829 raw42829Labels = mixedMoment B raw42829step0 raw42829step0Labels := by
      have ha : raw42829step0 = (fun i j => raw42829 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42829step0 raw42829; decide +kernel
      have hl : raw42829step0Labels = raw42829Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42829 raw42829Labels permutation164 permutation7
    mixedMoment B raw42829step0 raw42829step0Labels = mixedMoment B raw42829step1 raw42829step1Labels := by
      have ha : raw42829step1 = -raw42829step0 := by apply Matrix.ext; change ∀ i j, raw42829step1 i j = -(raw42829step0 i j); unfold raw42829step1 raw42829step0; decide +kernel
      have hl : raw42829step1Labels = raw42829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42829step1 raw42829step1Labels = mixedMoment B raw42829step2 raw42829step2Labels := by
      have ha : raw42829step2 = raw42829step1 := by apply Matrix.ext; unfold raw42829step2 raw42829step1; decide +kernel
      have hl : raw42829step1Labels = labelEmbedding6 ∘ raw42829step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42829step1 raw42829step1Labels raw42829step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4589 node4589Labels := by rfl

theorem canonical42830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42830 raw42830Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw42830 raw42830Labels = mixedMoment B raw42830step0 raw42830step0Labels := by
      have hz : ∀ j, raw42830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42830step0 = (fun i j => raw42830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42830step0 raw42830; decide +kernel
      have hl : raw42830step0Labels = raw42830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42830 raw42830Labels permutation434 hz
    mixedMoment B raw42830step0 raw42830step0Labels = mixedMoment B raw42830step1 raw42830step1Labels := by
      have ha : raw42830step1 = raw42830step0 := by apply Matrix.ext; unfold raw42830step1 raw42830step0; decide +kernel
      have hl : raw42830step0Labels = labelEmbedding1 ∘ raw42830step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42830step0 raw42830step0Labels raw42830step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical42831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42831 raw42831Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw42831 raw42831Labels = mixedMoment B raw42831step0 raw42831step0Labels := by
      have hz : ∀ j, raw42831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42831step0 = (fun i j => raw42831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42831step0 raw42831; decide +kernel
      have hl : raw42831step0Labels = raw42831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42831 raw42831Labels permutation434 hz
    mixedMoment B raw42831step0 raw42831step0Labels = mixedMoment B raw42831step1 raw42831step1Labels := by
      have ha : raw42831step1 = (fun i j => raw42831step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42831step1 raw42831step0; decide +kernel
      have hl : raw42831step1Labels = raw42831step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42831step0 raw42831step0Labels permutation34 permutation7
    mixedMoment B raw42831step1 raw42831step1Labels = mixedMoment B raw42831step2 raw42831step2Labels := by
      have ha : raw42831step2 = -raw42831step1 := by apply Matrix.ext; change ∀ i j, raw42831step2 i j = -(raw42831step1 i j); unfold raw42831step2 raw42831step1; decide +kernel
      have hl : raw42831step2Labels = raw42831step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42831step2 raw42831step2Labels = mixedMoment B raw42831step3 raw42831step3Labels := by
      have ha : raw42831step3 = raw42831step2 := by apply Matrix.ext; unfold raw42831step3 raw42831step2; decide +kernel
      have hl : raw42831step2Labels = labelEmbedding6 ∘ raw42831step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42831step2 raw42831step2Labels raw42831step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

theorem canonical42832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42832 raw42832Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw42832 raw42832Labels = mixedMoment B raw42832step0 raw42832step0Labels := by
      have ha : raw42832step0 = (fun i j => raw42832 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42832step0 raw42832; decide +kernel
      have hl : raw42832step0Labels = raw42832Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42832 raw42832Labels permutation157 permutation2
    mixedMoment B raw42832step0 raw42832step0Labels = mixedMoment B raw42832step1 raw42832step1Labels := by
      have ha : raw42832step1 = raw42832step0 := by apply Matrix.ext; unfold raw42832step1 raw42832step0; decide +kernel
      have hl : raw42832step0Labels = labelEmbedding1 ∘ raw42832step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42832step0 raw42832step0Labels raw42832step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

theorem canonical42833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42833 raw42833Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw42833 raw42833Labels = mixedMoment B raw42833step0 raw42833step0Labels := by
      have ha : raw42833step0 = (fun i j => raw42833 (permutation250 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42833step0 raw42833; decide +kernel
      have hl : raw42833step0Labels = raw42833Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42833 raw42833Labels permutation250 permutation6
    mixedMoment B raw42833step0 raw42833step0Labels = mixedMoment B raw42833step1 raw42833step1Labels := by
      have ha : raw42833step1 = -raw42833step0 := by apply Matrix.ext; change ∀ i j, raw42833step1 i j = -(raw42833step0 i j); unfold raw42833step1 raw42833step0; decide +kernel
      have hl : raw42833step1Labels = raw42833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4590 node4590Labels := by rfl

theorem canonical42834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42834 raw42834Labels = mixedMoment B node3298 node3298Labels := by
  calc
    mixedMoment B raw42834 raw42834Labels = mixedMoment B raw42834step0 raw42834step0Labels := by
      have hz : ∀ j, raw42834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42834step0 = (fun i j => raw42834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42834step0 raw42834; decide +kernel
      have hl : raw42834step0Labels = raw42834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42834 raw42834Labels permutation434 hz
    mixedMoment B raw42834step0 raw42834step0Labels = mixedMoment B raw42834step1 raw42834step1Labels := by
      have hz : ∀ j, raw42834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42834step1 = (fun i j => raw42834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42834step1 raw42834step0; decide +kernel
      have hl : raw42834step1Labels = raw42834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42834step0 raw42834step0Labels permutation80 hz
    mixedMoment B raw42834step1 raw42834step1Labels = mixedMoment B raw42834step2 raw42834step2Labels := by
      have ha : raw42834step2 = raw42834step1 := by apply Matrix.ext; unfold raw42834step2 raw42834step1; decide +kernel
      have hl : raw42834step1Labels = labelEmbedding1 ∘ raw42834step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42834step1 raw42834step1Labels raw42834step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3298 node3298Labels := by rfl

theorem canonical42835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42835 raw42835Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw42835 raw42835Labels = mixedMoment B raw42835step0 raw42835step0Labels := by
      have hz : ∀ j, raw42835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42835step0 = (fun i j => raw42835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42835step0 raw42835; decide +kernel
      have hl : raw42835step0Labels = raw42835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42835 raw42835Labels permutation434 hz
    mixedMoment B raw42835step0 raw42835step0Labels = mixedMoment B raw42835step1 raw42835step1Labels := by
      have hz : ∀ j, raw42835step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42835step1 = (fun i j => raw42835step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42835step1 raw42835step0; decide +kernel
      have hl : raw42835step1Labels = raw42835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42835step0 raw42835step0Labels permutation80 hz
    mixedMoment B raw42835step1 raw42835step1Labels = mixedMoment B raw42835step2 raw42835step2Labels := by
      have ha : raw42835step2 = (fun i j => raw42835step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42835step2 raw42835step1; decide +kernel
      have hl : raw42835step2Labels = raw42835step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42835step1 raw42835step1Labels permutation29 permutation6
    _ = mixedMoment B node4594 node4594Labels := by rfl

theorem canonical42836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42836 raw42836Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw42836 raw42836Labels = mixedMoment B raw42836step0 raw42836step0Labels := by
      have hz : ∀ j, raw42836 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42836step0 = (fun i j => raw42836 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42836step0 raw42836; decide +kernel
      have hl : raw42836step0Labels = raw42836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42836 raw42836Labels permutation346 hz
    mixedMoment B raw42836step0 raw42836step0Labels = mixedMoment B raw42836step1 raw42836step1Labels := by
      have ha : raw42836step1 = (fun i j => raw42836step0 (permutation54 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42836step1 raw42836step0; decide +kernel
      have hl : raw42836step1Labels = raw42836step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42836step0 raw42836step0Labels permutation54 permutation4
    mixedMoment B raw42836step1 raw42836step1Labels = mixedMoment B raw42836step2 raw42836step2Labels := by
      have ha : raw42836step2 = raw42836step1 := by apply Matrix.ext; unfold raw42836step2 raw42836step1; decide +kernel
      have hl : raw42836step1Labels = labelEmbedding1 ∘ raw42836step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42836step1 raw42836step1Labels raw42836step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical42837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42837 raw42837Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw42837 raw42837Labels = mixedMoment B raw42837step0 raw42837step0Labels := by
      have hz : ∀ j, raw42837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42837step0 = (fun i j => raw42837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42837step0 raw42837; decide +kernel
      have hl : raw42837step0Labels = raw42837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42837 raw42837Labels permutation346 hz
    mixedMoment B raw42837step0 raw42837step0Labels = mixedMoment B raw42837step1 raw42837step1Labels := by
      have ha : raw42837step1 = (fun i j => raw42837step0 (permutation51 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42837step1 raw42837step0; decide +kernel
      have hl : raw42837step1Labels = raw42837step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42837step0 raw42837step0Labels permutation51 permutation6
    mixedMoment B raw42837step1 raw42837step1Labels = mixedMoment B raw42837step2 raw42837step2Labels := by
      have ha : raw42837step2 = -raw42837step1 := by apply Matrix.ext; change ∀ i j, raw42837step2 i j = -(raw42837step1 i j); unfold raw42837step2 raw42837step1; decide +kernel
      have hl : raw42837step2Labels = raw42837step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4591 node4591Labels := by rfl

theorem canonical42838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42838 raw42838Labels = mixedMoment B node3297 node3297Labels := by
  calc
    mixedMoment B raw42838 raw42838Labels = mixedMoment B raw42838step0 raw42838step0Labels := by
      have hz : ∀ j, raw42838 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42838step0 = (fun i j => raw42838 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42838step0 raw42838; decide +kernel
      have hl : raw42838step0Labels = raw42838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42838 raw42838Labels permutation346 hz
    mixedMoment B raw42838step0 raw42838step0Labels = mixedMoment B raw42838step1 raw42838step1Labels := by
      have ha : raw42838step1 = (fun i j => raw42838step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42838step1 raw42838step0; decide +kernel
      have hl : raw42838step1Labels = raw42838step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42838step0 raw42838step0Labels permutation36 permutation2
    mixedMoment B raw42838step1 raw42838step1Labels = mixedMoment B raw42838step2 raw42838step2Labels := by
      have ha : raw42838step2 = raw42838step1 := by apply Matrix.ext; unfold raw42838step2 raw42838step1; decide +kernel
      have hl : raw42838step1Labels = labelEmbedding1 ∘ raw42838step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42838step1 raw42838step1Labels raw42838step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3297 node3297Labels := by rfl

theorem canonical42839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42839 raw42839Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw42839 raw42839Labels = mixedMoment B raw42839step0 raw42839step0Labels := by
      have hz : ∀ j, raw42839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42839step0 = (fun i j => raw42839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42839step0 raw42839; decide +kernel
      have hl : raw42839step0Labels = raw42839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42839 raw42839Labels permutation346 hz
    mixedMoment B raw42839step0 raw42839step0Labels = mixedMoment B raw42839step1 raw42839step1Labels := by
      have ha : raw42839step1 = (fun i j => raw42839step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42839step1 raw42839step0; decide +kernel
      have hl : raw42839step1Labels = raw42839step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42839step0 raw42839step0Labels permutation50 permutation6
    mixedMoment B raw42839step1 raw42839step1Labels = mixedMoment B raw42839step2 raw42839step2Labels := by
      have ha : raw42839step2 = -raw42839step1 := by apply Matrix.ext; change ∀ i j, raw42839step2 i j = -(raw42839step1 i j); unfold raw42839step2 raw42839step1; decide +kernel
      have hl : raw42839step2Labels = raw42839step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4593 node4593Labels := by rfl

theorem canonical42840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42840 raw42840Labels = mixedMoment B node2149 node2149Labels := by
  calc
    mixedMoment B raw42840 raw42840Labels = mixedMoment B raw42840step0 raw42840step0Labels := by
      have hz : ∀ j, raw42840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42840step0 = (fun i j => raw42840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42840step0 raw42840; decide +kernel
      have hl : raw42840step0Labels = raw42840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42840 raw42840Labels permutation434 hz
    mixedMoment B raw42840step0 raw42840step0Labels = mixedMoment B raw42840step1 raw42840step1Labels := by
      have ha : raw42840step1 = (fun i j => raw42840step0 (permutation101 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42840step1 raw42840step0; decide +kernel
      have hl : raw42840step1Labels = raw42840step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42840step0 raw42840step0Labels permutation101 permutation4
    mixedMoment B raw42840step1 raw42840step1Labels = mixedMoment B raw42840step2 raw42840step2Labels := by
      have ha : raw42840step2 = -raw42840step1 := by apply Matrix.ext; change ∀ i j, raw42840step2 i j = -(raw42840step1 i j); unfold raw42840step2 raw42840step1; decide +kernel
      have hl : raw42840step2Labels = raw42840step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42840step2 raw42840step2Labels = mixedMoment B raw42840step3 raw42840step3Labels := by
      have ha : raw42840step3 = raw42840step2 := by apply Matrix.ext; unfold raw42840step3 raw42840step2; decide +kernel
      have hl : raw42840step2Labels = labelEmbedding1 ∘ raw42840step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42840step2 raw42840step2Labels raw42840step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2149 node2149Labels := by rfl

theorem canonical42841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42841 raw42841Labels = mixedMoment B node4536 node4536Labels := by
  calc
    mixedMoment B raw42841 raw42841Labels = mixedMoment B raw42841step0 raw42841step0Labels := by
      have hz : ∀ j, raw42841 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42841step0 = (fun i j => raw42841 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42841step0 raw42841; decide +kernel
      have hl : raw42841step0Labels = raw42841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42841 raw42841Labels permutation434 hz
    mixedMoment B raw42841step0 raw42841step0Labels = mixedMoment B raw42841step1 raw42841step1Labels := by
      have ha : raw42841step1 = (fun i j => raw42841step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42841step1 raw42841step0; decide +kernel
      have hl : raw42841step1Labels = raw42841step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42841step0 raw42841step0Labels permutation35 permutation7
    mixedMoment B raw42841step1 raw42841step1Labels = mixedMoment B raw42841step2 raw42841step2Labels := by
      have ha : raw42841step2 = -raw42841step1 := by apply Matrix.ext; change ∀ i j, raw42841step2 i j = -(raw42841step1 i j); unfold raw42841step2 raw42841step1; decide +kernel
      have hl : raw42841step2Labels = raw42841step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42841step2 raw42841step2Labels = mixedMoment B raw42841step3 raw42841step3Labels := by
      have ha : raw42841step3 = raw42841step2 := by apply Matrix.ext; unfold raw42841step3 raw42841step2; decide +kernel
      have hl : raw42841step2Labels = labelEmbedding6 ∘ raw42841step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42841step2 raw42841step2Labels raw42841step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4536 node4536Labels := by rfl

theorem canonical42842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42842 raw42842Labels = mixedMoment B node2172 node2172Labels := by
  calc
    mixedMoment B raw42842 raw42842Labels = mixedMoment B raw42842step0 raw42842step0Labels := by
      have ha : raw42842step0 = (fun i j => raw42842 (permutation392 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42842step0 raw42842; decide +kernel
      have hl : raw42842step0Labels = raw42842Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42842 raw42842Labels permutation392 permutation4
    mixedMoment B raw42842step0 raw42842step0Labels = mixedMoment B raw42842step1 raw42842step1Labels := by
      have ha : raw42842step1 = -raw42842step0 := by apply Matrix.ext; change ∀ i j, raw42842step1 i j = -(raw42842step0 i j); unfold raw42842step1 raw42842step0; decide +kernel
      have hl : raw42842step1Labels = raw42842step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42842step1 raw42842step1Labels = mixedMoment B raw42842step2 raw42842step2Labels := by
      have ha : raw42842step2 = raw42842step1 := by apply Matrix.ext; unfold raw42842step2 raw42842step1; decide +kernel
      have hl : raw42842step1Labels = labelEmbedding1 ∘ raw42842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42842step1 raw42842step1Labels raw42842step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2172 node2172Labels := by rfl

theorem canonical42843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42843 raw42843Labels = mixedMoment B node4532 node4532Labels := by
  calc
    mixedMoment B raw42843 raw42843Labels = mixedMoment B raw42843step0 raw42843step0Labels := by
      have ha : raw42843step0 = (fun i j => raw42843 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42843step0 raw42843; decide +kernel
      have hl : raw42843step0Labels = raw42843Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42843 raw42843Labels permutation173 permutation7
    mixedMoment B raw42843step0 raw42843step0Labels = mixedMoment B raw42843step1 raw42843step1Labels := by
      have ha : raw42843step1 = -raw42843step0 := by apply Matrix.ext; change ∀ i j, raw42843step1 i j = -(raw42843step0 i j); unfold raw42843step1 raw42843step0; decide +kernel
      have hl : raw42843step1Labels = raw42843step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42843step1 raw42843step1Labels = mixedMoment B raw42843step2 raw42843step2Labels := by
      have ha : raw42843step2 = raw42843step1 := by apply Matrix.ext; unfold raw42843step2 raw42843step1; decide +kernel
      have hl : raw42843step1Labels = labelEmbedding6 ∘ raw42843step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42843step1 raw42843step1Labels raw42843step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4532 node4532Labels := by rfl

theorem canonical42844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42844 raw42844Labels = mixedMoment B node3258 node3258Labels := by
  calc
    mixedMoment B raw42844 raw42844Labels = mixedMoment B raw42844step0 raw42844step0Labels := by
      have ha : raw42844step0 = (fun i j => raw42844 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42844step0 raw42844; decide +kernel
      have hl : raw42844step0Labels = raw42844Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42844 raw42844Labels permutation158 permutation2
    mixedMoment B raw42844step0 raw42844step0Labels = mixedMoment B raw42844step1 raw42844step1Labels := by
      have ha : raw42844step1 = raw42844step0 := by apply Matrix.ext; unfold raw42844step1 raw42844step0; decide +kernel
      have hl : raw42844step0Labels = labelEmbedding1 ∘ raw42844step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42844step0 raw42844step0Labels raw42844step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3258 node3258Labels := by rfl

theorem canonical42845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42845 raw42845Labels = mixedMoment B node4529 node4529Labels := by
  calc
    mixedMoment B raw42845 raw42845Labels = mixedMoment B raw42845step0 raw42845step0Labels := by
      have ha : raw42845step0 = (fun i j => raw42845 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42845step0 raw42845; decide +kernel
      have hl : raw42845step0Labels = raw42845Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42845 raw42845Labels permutation166 permutation7
    mixedMoment B raw42845step0 raw42845step0Labels = mixedMoment B raw42845step1 raw42845step1Labels := by
      have ha : raw42845step1 = -raw42845step0 := by apply Matrix.ext; change ∀ i j, raw42845step1 i j = -(raw42845step0 i j); unfold raw42845step1 raw42845step0; decide +kernel
      have hl : raw42845step1Labels = raw42845step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42845step1 raw42845step1Labels = mixedMoment B raw42845step2 raw42845step2Labels := by
      have ha : raw42845step2 = raw42845step1 := by apply Matrix.ext; unfold raw42845step2 raw42845step1; decide +kernel
      have hl : raw42845step1Labels = labelEmbedding6 ∘ raw42845step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42845step1 raw42845step1Labels raw42845step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4529 node4529Labels := by rfl

theorem canonical42846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42846 raw42846Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw42846 raw42846Labels = mixedMoment B raw42846step0 raw42846step0Labels := by
      have hz : ∀ j, raw42846 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42846step0 = (fun i j => raw42846 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42846step0 raw42846; decide +kernel
      have hl : raw42846step0Labels = raw42846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42846 raw42846Labels permutation434 hz
    mixedMoment B raw42846step0 raw42846step0Labels = mixedMoment B raw42846step1 raw42846step1Labels := by
      have ha : raw42846step1 = raw42846step0 := by apply Matrix.ext; unfold raw42846step1 raw42846step0; decide +kernel
      have hl : raw42846step0Labels = labelEmbedding1 ∘ raw42846step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42846step0 raw42846step0Labels raw42846step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3268 node3268Labels := by rfl

theorem canonical42847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42847 raw42847Labels = mixedMoment B node4534 node4534Labels := by
  calc
    mixedMoment B raw42847 raw42847Labels = mixedMoment B raw42847step0 raw42847step0Labels := by
      have hz : ∀ j, raw42847 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42847step0 = (fun i j => raw42847 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42847step0 raw42847; decide +kernel
      have hl : raw42847step0Labels = raw42847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42847 raw42847Labels permutation434 hz
    mixedMoment B raw42847step0 raw42847step0Labels = mixedMoment B raw42847step1 raw42847step1Labels := by
      have ha : raw42847step1 = (fun i j => raw42847step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42847step1 raw42847step0; decide +kernel
      have hl : raw42847step1Labels = raw42847step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42847step0 raw42847step0Labels permutation34 permutation7
    mixedMoment B raw42847step1 raw42847step1Labels = mixedMoment B raw42847step2 raw42847step2Labels := by
      have ha : raw42847step2 = -raw42847step1 := by apply Matrix.ext; change ∀ i j, raw42847step2 i j = -(raw42847step1 i j); unfold raw42847step2 raw42847step1; decide +kernel
      have hl : raw42847step2Labels = raw42847step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42847step2 raw42847step2Labels = mixedMoment B raw42847step3 raw42847step3Labels := by
      have ha : raw42847step3 = raw42847step2 := by apply Matrix.ext; unfold raw42847step3 raw42847step2; decide +kernel
      have hl : raw42847step2Labels = labelEmbedding6 ∘ raw42847step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42847step2 raw42847step2Labels raw42847step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4534 node4534Labels := by rfl

theorem canonical42848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42848 raw42848Labels = mixedMoment B node3267 node3267Labels := by
  calc
    mixedMoment B raw42848 raw42848Labels = mixedMoment B raw42848step0 raw42848step0Labels := by
      have ha : raw42848step0 = (fun i j => raw42848 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42848step0 raw42848; decide +kernel
      have hl : raw42848step0Labels = raw42848Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42848 raw42848Labels permutation157 permutation2
    mixedMoment B raw42848step0 raw42848step0Labels = mixedMoment B raw42848step1 raw42848step1Labels := by
      have ha : raw42848step1 = raw42848step0 := by apply Matrix.ext; unfold raw42848step1 raw42848step0; decide +kernel
      have hl : raw42848step0Labels = labelEmbedding1 ∘ raw42848step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42848step0 raw42848step0Labels raw42848step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3267 node3267Labels := by rfl

theorem canonical42849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42849 raw42849Labels = mixedMoment B node4533 node4533Labels := by
  calc
    mixedMoment B raw42849 raw42849Labels = mixedMoment B raw42849step0 raw42849step0Labels := by
      have ha : raw42849step0 = (fun i j => raw42849 (permutation174 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42849step0 raw42849; decide +kernel
      have hl : raw42849step0Labels = raw42849Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42849 raw42849Labels permutation174 permutation7
    mixedMoment B raw42849step0 raw42849step0Labels = mixedMoment B raw42849step1 raw42849step1Labels := by
      have ha : raw42849step1 = -raw42849step0 := by apply Matrix.ext; change ∀ i j, raw42849step1 i j = -(raw42849step0 i j); unfold raw42849step1 raw42849step0; decide +kernel
      have hl : raw42849step1Labels = raw42849step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42849step1 raw42849step1Labels = mixedMoment B raw42849step2 raw42849step2Labels := by
      have ha : raw42849step2 = raw42849step1 := by apply Matrix.ext; unfold raw42849step2 raw42849step1; decide +kernel
      have hl : raw42849step1Labels = labelEmbedding6 ∘ raw42849step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42849step1 raw42849step1Labels raw42849step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4533 node4533Labels := by rfl

theorem canonical42850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42850 raw42850Labels = mixedMoment B node3255 node3255Labels := by
  calc
    mixedMoment B raw42850 raw42850Labels = mixedMoment B raw42850step0 raw42850step0Labels := by
      have ha : raw42850step0 = raw42850 := by apply Matrix.ext; unfold raw42850step0 raw42850; decide +kernel
      have hl : raw42850Labels = labelEmbedding1 ∘ raw42850step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42850 raw42850Labels raw42850step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3255 node3255Labels := by rfl

theorem canonical42851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42851 raw42851Labels = mixedMoment B node4527 node4527Labels := by
  calc
    mixedMoment B raw42851 raw42851Labels = mixedMoment B raw42851step0 raw42851step0Labels := by
      have ha : raw42851step0 = (fun i j => raw42851 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42851step0 raw42851; decide +kernel
      have hl : raw42851step0Labels = raw42851Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42851 raw42851Labels permutation164 permutation7
    mixedMoment B raw42851step0 raw42851step0Labels = mixedMoment B raw42851step1 raw42851step1Labels := by
      have ha : raw42851step1 = -raw42851step0 := by apply Matrix.ext; change ∀ i j, raw42851step1 i j = -(raw42851step0 i j); unfold raw42851step1 raw42851step0; decide +kernel
      have hl : raw42851step1Labels = raw42851step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42851step1 raw42851step1Labels = mixedMoment B raw42851step2 raw42851step2Labels := by
      have ha : raw42851step2 = raw42851step1 := by apply Matrix.ext; unfold raw42851step2 raw42851step1; decide +kernel
      have hl : raw42851step1Labels = labelEmbedding6 ∘ raw42851step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42851step1 raw42851step1Labels raw42851step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4527 node4527Labels := by rfl

theorem canonical42852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42852 raw42852Labels = mixedMoment B node3262 node3262Labels := by
  calc
    mixedMoment B raw42852 raw42852Labels = mixedMoment B raw42852step0 raw42852step0Labels := by
      have hz : ∀ j, raw42852 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42852step0 = (fun i j => raw42852 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42852step0 raw42852; decide +kernel
      have hl : raw42852step0Labels = raw42852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42852 raw42852Labels permutation434 hz
    mixedMoment B raw42852step0 raw42852step0Labels = mixedMoment B raw42852step1 raw42852step1Labels := by
      have ha : raw42852step1 = raw42852step0 := by apply Matrix.ext; unfold raw42852step1 raw42852step0; decide +kernel
      have hl : raw42852step0Labels = labelEmbedding1 ∘ raw42852step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42852step0 raw42852step0Labels raw42852step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3262 node3262Labels := by rfl

theorem canonical42853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42853 raw42853Labels = mixedMoment B node4531 node4531Labels := by
  calc
    mixedMoment B raw42853 raw42853Labels = mixedMoment B raw42853step0 raw42853step0Labels := by
      have hz : ∀ j, raw42853 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42853step0 = (fun i j => raw42853 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42853step0 raw42853; decide +kernel
      have hl : raw42853step0Labels = raw42853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42853 raw42853Labels permutation434 hz
    mixedMoment B raw42853step0 raw42853step0Labels = mixedMoment B raw42853step1 raw42853step1Labels := by
      have ha : raw42853step1 = (fun i j => raw42853step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42853step1 raw42853step0; decide +kernel
      have hl : raw42853step1Labels = raw42853step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42853step0 raw42853step0Labels permutation145 permutation6
    _ = mixedMoment B node4531 node4531Labels := by rfl

theorem canonical42854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42854 raw42854Labels = mixedMoment B node3260 node3260Labels := by
  calc
    mixedMoment B raw42854 raw42854Labels = mixedMoment B raw42854step0 raw42854step0Labels := by
      have ha : raw42854step0 = (fun i j => raw42854 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42854step0 raw42854; decide +kernel
      have hl : raw42854step0Labels = raw42854Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42854 raw42854Labels permutation157 permutation2
    mixedMoment B raw42854step0 raw42854step0Labels = mixedMoment B raw42854step1 raw42854step1Labels := by
      have ha : raw42854step1 = raw42854step0 := by apply Matrix.ext; unfold raw42854step1 raw42854step0; decide +kernel
      have hl : raw42854step0Labels = labelEmbedding1 ∘ raw42854step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42854step0 raw42854step0Labels raw42854step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3260 node3260Labels := by rfl

theorem canonical42855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42855 raw42855Labels = mixedMoment B node4528 node4528Labels := by
  calc
    mixedMoment B raw42855 raw42855Labels = mixedMoment B raw42855step0 raw42855step0Labels := by
      have ha : raw42855step0 = (fun i j => raw42855 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42855step0 raw42855; decide +kernel
      have hl : raw42855step0Labels = raw42855Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42855 raw42855Labels permutation171 permutation7
    mixedMoment B raw42855step0 raw42855step0Labels = mixedMoment B raw42855step1 raw42855step1Labels := by
      have ha : raw42855step1 = -raw42855step0 := by apply Matrix.ext; change ∀ i j, raw42855step1 i j = -(raw42855step0 i j); unfold raw42855step1 raw42855step0; decide +kernel
      have hl : raw42855step1Labels = raw42855step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42855step1 raw42855step1Labels = mixedMoment B raw42855step2 raw42855step2Labels := by
      have ha : raw42855step2 = raw42855step1 := by apply Matrix.ext; unfold raw42855step2 raw42855step1; decide +kernel
      have hl : raw42855step1Labels = labelEmbedding6 ∘ raw42855step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42855step1 raw42855step1Labels raw42855step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4528 node4528Labels := by rfl

theorem canonical42856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42856 raw42856Labels = mixedMoment B node3261 node3261Labels := by
  calc
    mixedMoment B raw42856 raw42856Labels = mixedMoment B raw42856step0 raw42856step0Labels := by
      have ha : raw42856step0 = (fun i j => raw42856 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42856step0 raw42856; decide +kernel
      have hl : raw42856step0Labels = raw42856Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42856 raw42856Labels permutation156 permutation2
    mixedMoment B raw42856step0 raw42856step0Labels = mixedMoment B raw42856step1 raw42856step1Labels := by
      have ha : raw42856step1 = raw42856step0 := by apply Matrix.ext; unfold raw42856step1 raw42856step0; decide +kernel
      have hl : raw42856step0Labels = labelEmbedding1 ∘ raw42856step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42856step0 raw42856step0Labels raw42856step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3261 node3261Labels := by rfl

theorem canonical42857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42857 raw42857Labels = mixedMoment B node4530 node4530Labels := by
  calc
    mixedMoment B raw42857 raw42857Labels = mixedMoment B raw42857step0 raw42857step0Labels := by
      have ha : raw42857step0 = (fun i j => raw42857 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42857step0 raw42857; decide +kernel
      have hl : raw42857step0Labels = raw42857Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42857 raw42857Labels permutation170 permutation7
    mixedMoment B raw42857step0 raw42857step0Labels = mixedMoment B raw42857step1 raw42857step1Labels := by
      have ha : raw42857step1 = -raw42857step0 := by apply Matrix.ext; change ∀ i j, raw42857step1 i j = -(raw42857step0 i j); unfold raw42857step1 raw42857step0; decide +kernel
      have hl : raw42857step1Labels = raw42857step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42857step1 raw42857step1Labels = mixedMoment B raw42857step2 raw42857step2Labels := by
      have ha : raw42857step2 = raw42857step1 := by apply Matrix.ext; unfold raw42857step2 raw42857step1; decide +kernel
      have hl : raw42857step1Labels = labelEmbedding6 ∘ raw42857step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42857step1 raw42857step1Labels raw42857step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4530 node4530Labels := by rfl

theorem canonical42858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42858 raw42858Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw42858 raw42858Labels = mixedMoment B raw42858step0 raw42858step0Labels := by
      have hz : ∀ j, raw42858 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42858step0 = (fun i j => raw42858 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42858step0 raw42858; decide +kernel
      have hl : raw42858step0Labels = raw42858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42858 raw42858Labels permutation434 hz
    mixedMoment B raw42858step0 raw42858step0Labels = mixedMoment B raw42858step1 raw42858step1Labels := by
      have hz : ∀ j, raw42858step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42858step1 = (fun i j => raw42858step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42858step1 raw42858step0; decide +kernel
      have hl : raw42858step1Labels = raw42858step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42858step0 raw42858step0Labels permutation80 hz
    mixedMoment B raw42858step1 raw42858step1Labels = mixedMoment B raw42858step2 raw42858step2Labels := by
      have ha : raw42858step2 = (fun i j => raw42858step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42858step2 raw42858step1; decide +kernel
      have hl : raw42858step2Labels = raw42858step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42858step1 raw42858step1Labels permutation29 permutation4
    mixedMoment B raw42858step2 raw42858step2Labels = mixedMoment B raw42858step3 raw42858step3Labels := by
      have ha : raw42858step3 = -raw42858step2 := by apply Matrix.ext; change ∀ i j, raw42858step3 i j = -(raw42858step2 i j); unfold raw42858step3 raw42858step2; decide +kernel
      have hl : raw42858step3Labels = raw42858step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42858step3 raw42858step3Labels = mixedMoment B raw42858step4 raw42858step4Labels := by
      have ha : raw42858step4 = raw42858step3 := by apply Matrix.ext; unfold raw42858step4 raw42858step3; decide +kernel
      have hl : raw42858step3Labels = labelEmbedding1 ∘ raw42858step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42858step3 raw42858step3Labels raw42858step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1516 node1516Labels := by rfl

theorem canonical42859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42859 raw42859Labels = mixedMoment B node4156 node4156Labels := by
  calc
    mixedMoment B raw42859 raw42859Labels = mixedMoment B raw42859step0 raw42859step0Labels := by
      have hz : ∀ j, raw42859 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42859step0 = (fun i j => raw42859 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42859step0 raw42859; decide +kernel
      have hl : raw42859step0Labels = raw42859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42859 raw42859Labels permutation434 hz
    mixedMoment B raw42859step0 raw42859step0Labels = mixedMoment B raw42859step1 raw42859step1Labels := by
      have hz : ∀ j, raw42859step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42859step1 = (fun i j => raw42859step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42859step1 raw42859step0; decide +kernel
      have hl : raw42859step1Labels = raw42859step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42859step0 raw42859step0Labels permutation80 hz
    mixedMoment B raw42859step1 raw42859step1Labels = mixedMoment B raw42859step2 raw42859step2Labels := by
      have ha : raw42859step2 = (fun i j => raw42859step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42859step2 raw42859step1; decide +kernel
      have hl : raw42859step2Labels = raw42859step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42859step1 raw42859step1Labels permutation31 permutation6
    _ = mixedMoment B node4156 node4156Labels := by rfl

theorem canonical42860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42860 raw42860Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw42860 raw42860Labels = mixedMoment B raw42860step0 raw42860step0Labels := by
      have hz : ∀ j, raw42860 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42860step0 = (fun i j => raw42860 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42860step0 raw42860; decide +kernel
      have hl : raw42860step0Labels = raw42860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42860 raw42860Labels permutation346 hz
    mixedMoment B raw42860step0 raw42860step0Labels = mixedMoment B raw42860step1 raw42860step1Labels := by
      have ha : raw42860step1 = (fun i j => raw42860step0 (permutation95 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42860step1 raw42860step0; decide +kernel
      have hl : raw42860step1Labels = raw42860step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42860step0 raw42860step0Labels permutation95 permutation4
    mixedMoment B raw42860step1 raw42860step1Labels = mixedMoment B raw42860step2 raw42860step2Labels := by
      have ha : raw42860step2 = -raw42860step1 := by apply Matrix.ext; change ∀ i j, raw42860step2 i j = -(raw42860step1 i j); unfold raw42860step2 raw42860step1; decide +kernel
      have hl : raw42860step2Labels = raw42860step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42860step2 raw42860step2Labels = mixedMoment B raw42860step3 raw42860step3Labels := by
      have ha : raw42860step3 = raw42860step2 := by apply Matrix.ext; unfold raw42860step3 raw42860step2; decide +kernel
      have hl : raw42860step2Labels = labelEmbedding1 ∘ raw42860step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42860step2 raw42860step2Labels raw42860step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

theorem canonical42861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42861 raw42861Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw42861 raw42861Labels = mixedMoment B raw42861step0 raw42861step0Labels := by
      have hz : ∀ j, raw42861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42861step0 = (fun i j => raw42861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42861step0 raw42861; decide +kernel
      have hl : raw42861step0Labels = raw42861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42861 raw42861Labels permutation346 hz
    mixedMoment B raw42861step0 raw42861step0Labels = mixedMoment B raw42861step1 raw42861step1Labels := by
      have ha : raw42861step1 = (fun i j => raw42861step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42861step1 raw42861step0; decide +kernel
      have hl : raw42861step1Labels = raw42861step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42861step0 raw42861step0Labels permutation97 permutation6
    _ = mixedMoment B node4330 node4330Labels := by rfl

theorem canonical42862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42862 raw42862Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw42862 raw42862Labels = mixedMoment B raw42862step0 raw42862step0Labels := by
      have hz : ∀ j, raw42862 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42862step0 = (fun i j => raw42862 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42862step0 raw42862; decide +kernel
      have hl : raw42862step0Labels = raw42862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42862 raw42862Labels permutation346 hz
    mixedMoment B raw42862step0 raw42862step0Labels = mixedMoment B raw42862step1 raw42862step1Labels := by
      have ha : raw42862step1 = (fun i j => raw42862step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42862step1 raw42862step0; decide +kernel
      have hl : raw42862step1Labels = raw42862step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42862step0 raw42862step0Labels permutation37 permutation2
    mixedMoment B raw42862step1 raw42862step1Labels = mixedMoment B raw42862step2 raw42862step2Labels := by
      have ha : raw42862step2 = raw42862step1 := by apply Matrix.ext; unfold raw42862step2 raw42862step1; decide +kernel
      have hl : raw42862step1Labels = labelEmbedding1 ∘ raw42862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42862step1 raw42862step1Labels raw42862step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

theorem canonical42863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42863 raw42863Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw42863 raw42863Labels = mixedMoment B raw42863step0 raw42863step0Labels := by
      have hz : ∀ j, raw42863 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42863step0 = (fun i j => raw42863 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42863step0 raw42863; decide +kernel
      have hl : raw42863step0Labels = raw42863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42863 raw42863Labels permutation346 hz
    mixedMoment B raw42863step0 raw42863step0Labels = mixedMoment B raw42863step1 raw42863step1Labels := by
      have ha : raw42863step1 = (fun i j => raw42863step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42863step1 raw42863step0; decide +kernel
      have hl : raw42863step1Labels = raw42863step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42863step0 raw42863step0Labels permutation37 permutation7
    mixedMoment B raw42863step1 raw42863step1Labels = mixedMoment B raw42863step2 raw42863step2Labels := by
      have ha : raw42863step2 = -raw42863step1 := by apply Matrix.ext; change ∀ i j, raw42863step2 i j = -(raw42863step1 i j); unfold raw42863step2 raw42863step1; decide +kernel
      have hl : raw42863step2Labels = raw42863step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42863step2 raw42863step2Labels = mixedMoment B raw42863step3 raw42863step3Labels := by
      have ha : raw42863step3 = raw42863step2 := by apply Matrix.ext; unfold raw42863step3 raw42863step2; decide +kernel
      have hl : raw42863step2Labels = labelEmbedding6 ∘ raw42863step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42863step2 raw42863step2Labels raw42863step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4535 node4535Labels := by rfl

theorem canonical42864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42864 raw42864Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw42864 raw42864Labels = mixedMoment B raw42864step0 raw42864step0Labels := by
      have hz : ∀ j, raw42864 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42864step0 = (fun i j => raw42864 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42864step0 raw42864; decide +kernel
      have hl : raw42864step0Labels = raw42864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42864 raw42864Labels permutation520 hz
    mixedMoment B raw42864step0 raw42864step0Labels = mixedMoment B raw42864step1 raw42864step1Labels := by
      have hz : ∀ j, raw42864step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42864step1 = (fun i j => raw42864step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42864step1 raw42864step0; decide +kernel
      have hl : raw42864step1Labels = raw42864step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42864step0 raw42864step0Labels permutation104 hz
    mixedMoment B raw42864step1 raw42864step1Labels = mixedMoment B raw42864step2 raw42864step2Labels := by
      have ha : raw42864step2 = (fun i j => raw42864step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42864step2 raw42864step1; decide +kernel
      have hl : raw42864step2Labels = raw42864step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42864step1 raw42864step1Labels permutation8 permutation4
    mixedMoment B raw42864step2 raw42864step2Labels = mixedMoment B raw42864step3 raw42864step3Labels := by
      have ha : raw42864step3 = -raw42864step2 := by apply Matrix.ext; change ∀ i j, raw42864step3 i j = -(raw42864step2 i j); unfold raw42864step3 raw42864step2; decide +kernel
      have hl : raw42864step3Labels = raw42864step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42864step3 raw42864step3Labels = mixedMoment B raw42864step4 raw42864step4Labels := by
      have ha : raw42864step4 = raw42864step3 := by apply Matrix.ext; unfold raw42864step4 raw42864step3; decide +kernel
      have hl : raw42864step3Labels = labelEmbedding1 ∘ raw42864step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42864step3 raw42864step3Labels raw42864step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2755 node2755Labels := by rfl

theorem canonical42865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42865 raw42865Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw42865 raw42865Labels = mixedMoment B raw42865step0 raw42865step0Labels := by
      have hz : ∀ j, raw42865 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42865step0 = (fun i j => raw42865 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42865step0 raw42865; decide +kernel
      have hl : raw42865step0Labels = raw42865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42865 raw42865Labels permutation520 hz
    mixedMoment B raw42865step0 raw42865step0Labels = mixedMoment B raw42865step1 raw42865step1Labels := by
      have hz : ∀ j, raw42865step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42865step1 = (fun i j => raw42865step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42865step1 raw42865step0; decide +kernel
      have hl : raw42865step1Labels = raw42865step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42865step0 raw42865step0Labels permutation104 hz
    mixedMoment B raw42865step1 raw42865step1Labels = mixedMoment B raw42865step2 raw42865step2Labels := by
      have ha : raw42865step2 = (fun i j => raw42865step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42865step2 raw42865step1; decide +kernel
      have hl : raw42865step2Labels = raw42865step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42865step1 raw42865step1Labels permutation29 permutation5
    mixedMoment B raw42865step2 raw42865step2Labels = mixedMoment B raw42865step3 raw42865step3Labels := by
      have ha : raw42865step3 = raw42865step2 := by apply Matrix.ext; unfold raw42865step3 raw42865step2; decide +kernel
      have hl : raw42865step2Labels = labelEmbedding9 ∘ raw42865step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42865step2 raw42865step2Labels raw42865step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical42866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42866 raw42866Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw42866 raw42866Labels = mixedMoment B raw42866step0 raw42866step0Labels := by
      have hz : ∀ j, raw42866 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42866step0 = (fun i j => raw42866 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42866step0 raw42866; decide +kernel
      have hl : raw42866step0Labels = raw42866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42866 raw42866Labels permutation434 hz
    mixedMoment B raw42866step0 raw42866step0Labels = mixedMoment B raw42866step1 raw42866step1Labels := by
      have ha : raw42866step1 = (fun i j => raw42866step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42866step1 raw42866step0; decide +kernel
      have hl : raw42866step1Labels = raw42866step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42866step0 raw42866step0Labels permutation32 permutation4
    mixedMoment B raw42866step1 raw42866step1Labels = mixedMoment B raw42866step2 raw42866step2Labels := by
      have ha : raw42866step2 = -raw42866step1 := by apply Matrix.ext; change ∀ i j, raw42866step2 i j = -(raw42866step1 i j); unfold raw42866step2 raw42866step1; decide +kernel
      have hl : raw42866step2Labels = raw42866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42866step2 raw42866step2Labels = mixedMoment B raw42866step3 raw42866step3Labels := by
      have ha : raw42866step3 = raw42866step2 := by apply Matrix.ext; unfold raw42866step3 raw42866step2; decide +kernel
      have hl : raw42866step2Labels = labelEmbedding1 ∘ raw42866step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42866step2 raw42866step2Labels raw42866step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2753 node2753Labels := by rfl

theorem canonical42867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42867 raw42867Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw42867 raw42867Labels = mixedMoment B raw42867step0 raw42867step0Labels := by
      have hz : ∀ j, raw42867 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42867step0 = (fun i j => raw42867 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42867step0 raw42867; decide +kernel
      have hl : raw42867step0Labels = raw42867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42867 raw42867Labels permutation434 hz
    mixedMoment B raw42867step0 raw42867step0Labels = mixedMoment B raw42867step1 raw42867step1Labels := by
      have ha : raw42867step1 = (fun i j => raw42867step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42867step1 raw42867step0; decide +kernel
      have hl : raw42867step1Labels = raw42867step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42867step0 raw42867step0Labels permutation32 permutation4
    mixedMoment B raw42867step1 raw42867step1Labels = mixedMoment B raw42867step2 raw42867step2Labels := by
      have ha : raw42867step2 = -raw42867step1 := by apply Matrix.ext; change ∀ i j, raw42867step2 i j = -(raw42867step1 i j); unfold raw42867step2 raw42867step1; decide +kernel
      have hl : raw42867step2Labels = raw42867step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42867step2 raw42867step2Labels = mixedMoment B raw42867step3 raw42867step3Labels := by
      have ha : raw42867step3 = raw42867step2 := by apply Matrix.ext; unfold raw42867step3 raw42867step2; decide +kernel
      have hl : raw42867step2Labels = labelEmbedding10 ∘ raw42867step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42867step2 raw42867step2Labels raw42867step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical42868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42868 raw42868Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw42868 raw42868Labels = mixedMoment B raw42868step0 raw42868step0Labels := by
      have hz : ∀ j, raw42868 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42868step0 = (fun i j => raw42868 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42868step0 raw42868; decide +kernel
      have hl : raw42868step0Labels = raw42868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42868 raw42868Labels permutation434 hz
    mixedMoment B raw42868step0 raw42868step0Labels = mixedMoment B raw42868step1 raw42868step1Labels := by
      have ha : raw42868step1 = (fun i j => raw42868step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42868step1 raw42868step0; decide +kernel
      have hl : raw42868step1Labels = raw42868step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42868step0 raw42868step0Labels permutation33 permutation4
    mixedMoment B raw42868step1 raw42868step1Labels = mixedMoment B raw42868step2 raw42868step2Labels := by
      have ha : raw42868step2 = -raw42868step1 := by apply Matrix.ext; change ∀ i j, raw42868step2 i j = -(raw42868step1 i j); unfold raw42868step2 raw42868step1; decide +kernel
      have hl : raw42868step2Labels = raw42868step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42868step2 raw42868step2Labels = mixedMoment B raw42868step3 raw42868step3Labels := by
      have ha : raw42868step3 = raw42868step2 := by apply Matrix.ext; unfold raw42868step3 raw42868step2; decide +kernel
      have hl : raw42868step2Labels = labelEmbedding1 ∘ raw42868step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42868step2 raw42868step2Labels raw42868step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2751 node2751Labels := by rfl

theorem canonical42869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42869 raw42869Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw42869 raw42869Labels = mixedMoment B raw42869step0 raw42869step0Labels := by
      have hz : ∀ j, raw42869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42869step0 = (fun i j => raw42869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42869step0 raw42869; decide +kernel
      have hl : raw42869step0Labels = raw42869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42869 raw42869Labels permutation434 hz
    mixedMoment B raw42869step0 raw42869step0Labels = mixedMoment B raw42869step1 raw42869step1Labels := by
      have ha : raw42869step1 = (fun i j => raw42869step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42869step1 raw42869step0; decide +kernel
      have hl : raw42869step1Labels = raw42869step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42869step0 raw42869step0Labels permutation33 permutation4
    mixedMoment B raw42869step1 raw42869step1Labels = mixedMoment B raw42869step2 raw42869step2Labels := by
      have ha : raw42869step2 = -raw42869step1 := by apply Matrix.ext; change ∀ i j, raw42869step2 i j = -(raw42869step1 i j); unfold raw42869step2 raw42869step1; decide +kernel
      have hl : raw42869step2Labels = raw42869step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42869step2 raw42869step2Labels = mixedMoment B raw42869step3 raw42869step3Labels := by
      have ha : raw42869step3 = raw42869step2 := by apply Matrix.ext; unfold raw42869step3 raw42869step2; decide +kernel
      have hl : raw42869step2Labels = labelEmbedding10 ∘ raw42869step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42869step2 raw42869step2Labels raw42869step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

theorem canonical42870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42870 raw42870Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw42870 raw42870Labels = mixedMoment B raw42870step0 raw42870step0Labels := by
      have ha : raw42870step0 = (fun i j => raw42870 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42870step0 raw42870; decide +kernel
      have hl : raw42870step0Labels = raw42870Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42870 raw42870Labels permutation224 permutation4
    mixedMoment B raw42870step0 raw42870step0Labels = mixedMoment B raw42870step1 raw42870step1Labels := by
      have ha : raw42870step1 = -raw42870step0 := by apply Matrix.ext; change ∀ i j, raw42870step1 i j = -(raw42870step0 i j); unfold raw42870step1 raw42870step0; decide +kernel
      have hl : raw42870step1Labels = raw42870step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42870step1 raw42870step1Labels = mixedMoment B raw42870step2 raw42870step2Labels := by
      have ha : raw42870step2 = raw42870step1 := by apply Matrix.ext; unfold raw42870step2 raw42870step1; decide +kernel
      have hl : raw42870step1Labels = labelEmbedding1 ∘ raw42870step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42870step1 raw42870step1Labels raw42870step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2710 node2710Labels := by rfl

theorem canonical42871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42871 raw42871Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw42871 raw42871Labels = mixedMoment B raw42871step0 raw42871step0Labels := by
      have ha : raw42871step0 = (fun i j => raw42871 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42871step0 raw42871; decide +kernel
      have hl : raw42871step0Labels = raw42871Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42871 raw42871Labels permutation224 permutation4
    mixedMoment B raw42871step0 raw42871step0Labels = mixedMoment B raw42871step1 raw42871step1Labels := by
      have ha : raw42871step1 = -raw42871step0 := by apply Matrix.ext; change ∀ i j, raw42871step1 i j = -(raw42871step0 i j); unfold raw42871step1 raw42871step0; decide +kernel
      have hl : raw42871step1Labels = raw42871step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42871step1 raw42871step1Labels = mixedMoment B raw42871step2 raw42871step2Labels := by
      have ha : raw42871step2 = raw42871step1 := by apply Matrix.ext; unfold raw42871step2 raw42871step1; decide +kernel
      have hl : raw42871step1Labels = labelEmbedding10 ∘ raw42871step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42871step1 raw42871step1Labels raw42871step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical42872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42872 raw42872Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw42872 raw42872Labels = mixedMoment B raw42872step0 raw42872step0Labels := by
      have ha : raw42872step0 = (fun i j => raw42872 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42872step0 raw42872; decide +kernel
      have hl : raw42872step0Labels = raw42872Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42872 raw42872Labels permutation246 permutation4
    mixedMoment B raw42872step0 raw42872step0Labels = mixedMoment B raw42872step1 raw42872step1Labels := by
      have ha : raw42872step1 = -raw42872step0 := by apply Matrix.ext; change ∀ i j, raw42872step1 i j = -(raw42872step0 i j); unfold raw42872step1 raw42872step0; decide +kernel
      have hl : raw42872step1Labels = raw42872step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42872step1 raw42872step1Labels = mixedMoment B raw42872step2 raw42872step2Labels := by
      have ha : raw42872step2 = raw42872step1 := by apply Matrix.ext; unfold raw42872step2 raw42872step1; decide +kernel
      have hl : raw42872step1Labels = labelEmbedding1 ∘ raw42872step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42872step1 raw42872step1Labels raw42872step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2662 node2662Labels := by rfl

theorem canonical42873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42873 raw42873Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw42873 raw42873Labels = mixedMoment B raw42873step0 raw42873step0Labels := by
      have ha : raw42873step0 = (fun i j => raw42873 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42873step0 raw42873; decide +kernel
      have hl : raw42873step0Labels = raw42873Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42873 raw42873Labels permutation246 permutation4
    mixedMoment B raw42873step0 raw42873step0Labels = mixedMoment B raw42873step1 raw42873step1Labels := by
      have ha : raw42873step1 = -raw42873step0 := by apply Matrix.ext; change ∀ i j, raw42873step1 i j = -(raw42873step0 i j); unfold raw42873step1 raw42873step0; decide +kernel
      have hl : raw42873step1Labels = raw42873step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42873step1 raw42873step1Labels = mixedMoment B raw42873step2 raw42873step2Labels := by
      have ha : raw42873step2 = raw42873step1 := by apply Matrix.ext; unfold raw42873step2 raw42873step1; decide +kernel
      have hl : raw42873step1Labels = labelEmbedding10 ∘ raw42873step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42873step1 raw42873step1Labels raw42873step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

theorem canonical42874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42874 raw42874Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw42874 raw42874Labels = mixedMoment B raw42874step0 raw42874step0Labels := by
      have ha : raw42874step0 = (fun i j => raw42874 (permutation247 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42874step0 raw42874; decide +kernel
      have hl : raw42874step0Labels = raw42874Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42874 raw42874Labels permutation247 permutation4
    mixedMoment B raw42874step0 raw42874step0Labels = mixedMoment B raw42874step1 raw42874step1Labels := by
      have ha : raw42874step1 = -raw42874step0 := by apply Matrix.ext; change ∀ i j, raw42874step1 i j = -(raw42874step0 i j); unfold raw42874step1 raw42874step0; decide +kernel
      have hl : raw42874step1Labels = raw42874step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42874step1 raw42874step1Labels = mixedMoment B raw42874step2 raw42874step2Labels := by
      have ha : raw42874step2 = raw42874step1 := by apply Matrix.ext; unfold raw42874step2 raw42874step1; decide +kernel
      have hl : raw42874step1Labels = labelEmbedding1 ∘ raw42874step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42874step1 raw42874step1Labels raw42874step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2661 node2661Labels := by rfl

theorem canonical42875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42875 raw42875Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw42875 raw42875Labels = mixedMoment B raw42875step0 raw42875step0Labels := by
      have ha : raw42875step0 = (fun i j => raw42875 (permutation247 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42875step0 raw42875; decide +kernel
      have hl : raw42875step0Labels = raw42875Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42875 raw42875Labels permutation247 permutation4
    mixedMoment B raw42875step0 raw42875step0Labels = mixedMoment B raw42875step1 raw42875step1Labels := by
      have ha : raw42875step1 = -raw42875step0 := by apply Matrix.ext; change ∀ i j, raw42875step1 i j = -(raw42875step0 i j); unfold raw42875step1 raw42875step0; decide +kernel
      have hl : raw42875step1Labels = raw42875step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42875step1 raw42875step1Labels = mixedMoment B raw42875step2 raw42875step2Labels := by
      have ha : raw42875step2 = raw42875step1 := by apply Matrix.ext; unfold raw42875step2 raw42875step1; decide +kernel
      have hl : raw42875step1Labels = labelEmbedding10 ∘ raw42875step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42875step1 raw42875step1Labels raw42875step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

theorem canonical42876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42876 raw42876Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw42876 raw42876Labels = mixedMoment B raw42876step0 raw42876step0Labels := by
      have hz : ∀ j, raw42876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42876step0 = (fun i j => raw42876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42876step0 raw42876; decide +kernel
      have hl : raw42876step0Labels = raw42876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42876 raw42876Labels permutation434 hz
    mixedMoment B raw42876step0 raw42876step0Labels = mixedMoment B raw42876step1 raw42876step1Labels := by
      have ha : raw42876step1 = (fun i j => raw42876step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42876step1 raw42876step0; decide +kernel
      have hl : raw42876step1Labels = raw42876step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42876step0 raw42876step0Labels permutation44 permutation4
    mixedMoment B raw42876step1 raw42876step1Labels = mixedMoment B raw42876step2 raw42876step2Labels := by
      have ha : raw42876step2 = -raw42876step1 := by apply Matrix.ext; change ∀ i j, raw42876step2 i j = -(raw42876step1 i j); unfold raw42876step2 raw42876step1; decide +kernel
      have hl : raw42876step2Labels = raw42876step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42876step2 raw42876step2Labels = mixedMoment B raw42876step3 raw42876step3Labels := by
      have ha : raw42876step3 = raw42876step2 := by apply Matrix.ext; unfold raw42876step3 raw42876step2; decide +kernel
      have hl : raw42876step2Labels = labelEmbedding1 ∘ raw42876step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42876step2 raw42876step2Labels raw42876step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2724 node2724Labels := by rfl

theorem canonical42877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42877 raw42877Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw42877 raw42877Labels = mixedMoment B raw42877step0 raw42877step0Labels := by
      have hz : ∀ j, raw42877 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42877step0 = (fun i j => raw42877 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42877step0 raw42877; decide +kernel
      have hl : raw42877step0Labels = raw42877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42877 raw42877Labels permutation434 hz
    mixedMoment B raw42877step0 raw42877step0Labels = mixedMoment B raw42877step1 raw42877step1Labels := by
      have ha : raw42877step1 = (fun i j => raw42877step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42877step1 raw42877step0; decide +kernel
      have hl : raw42877step1Labels = raw42877step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42877step0 raw42877step0Labels permutation44 permutation4
    mixedMoment B raw42877step1 raw42877step1Labels = mixedMoment B raw42877step2 raw42877step2Labels := by
      have ha : raw42877step2 = -raw42877step1 := by apply Matrix.ext; change ∀ i j, raw42877step2 i j = -(raw42877step1 i j); unfold raw42877step2 raw42877step1; decide +kernel
      have hl : raw42877step2Labels = raw42877step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42877step2 raw42877step2Labels = mixedMoment B raw42877step3 raw42877step3Labels := by
      have ha : raw42877step3 = raw42877step2 := by apply Matrix.ext; unfold raw42877step3 raw42877step2; decide +kernel
      have hl : raw42877step2Labels = labelEmbedding10 ∘ raw42877step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42877step2 raw42877step2Labels raw42877step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

theorem canonical42878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42878 raw42878Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw42878 raw42878Labels = mixedMoment B raw42878step0 raw42878step0Labels := by
      have hz : ∀ j, raw42878 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42878step0 = (fun i j => raw42878 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42878step0 raw42878; decide +kernel
      have hl : raw42878step0Labels = raw42878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42878 raw42878Labels permutation434 hz
    mixedMoment B raw42878step0 raw42878step0Labels = mixedMoment B raw42878step1 raw42878step1Labels := by
      have ha : raw42878step1 = (fun i j => raw42878step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42878step1 raw42878step0; decide +kernel
      have hl : raw42878step1Labels = raw42878step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42878step0 raw42878step0Labels permutation37 permutation4
    mixedMoment B raw42878step1 raw42878step1Labels = mixedMoment B raw42878step2 raw42878step2Labels := by
      have ha : raw42878step2 = -raw42878step1 := by apply Matrix.ext; change ∀ i j, raw42878step2 i j = -(raw42878step1 i j); unfold raw42878step2 raw42878step1; decide +kernel
      have hl : raw42878step2Labels = raw42878step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42878step2 raw42878step2Labels = mixedMoment B raw42878step3 raw42878step3Labels := by
      have ha : raw42878step3 = raw42878step2 := by apply Matrix.ext; unfold raw42878step3 raw42878step2; decide +kernel
      have hl : raw42878step2Labels = labelEmbedding1 ∘ raw42878step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42878step2 raw42878step2Labels raw42878step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

theorem canonical42879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42879 raw42879Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw42879 raw42879Labels = mixedMoment B raw42879step0 raw42879step0Labels := by
      have hz : ∀ j, raw42879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42879step0 = (fun i j => raw42879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42879step0 raw42879; decide +kernel
      have hl : raw42879step0Labels = raw42879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42879 raw42879Labels permutation434 hz
    mixedMoment B raw42879step0 raw42879step0Labels = mixedMoment B raw42879step1 raw42879step1Labels := by
      have ha : raw42879step1 = (fun i j => raw42879step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42879step1 raw42879step0; decide +kernel
      have hl : raw42879step1Labels = raw42879step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42879step0 raw42879step0Labels permutation37 permutation4
    mixedMoment B raw42879step1 raw42879step1Labels = mixedMoment B raw42879step2 raw42879step2Labels := by
      have ha : raw42879step2 = -raw42879step1 := by apply Matrix.ext; change ∀ i j, raw42879step2 i j = -(raw42879step1 i j); unfold raw42879step2 raw42879step1; decide +kernel
      have hl : raw42879step2Labels = raw42879step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42879step2 raw42879step2Labels = mixedMoment B raw42879step3 raw42879step3Labels := by
      have ha : raw42879step3 = raw42879step2 := by apply Matrix.ext; unfold raw42879step3 raw42879step2; decide +kernel
      have hl : raw42879step2Labels = labelEmbedding10 ∘ raw42879step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42879step2 raw42879step2Labels raw42879step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2752 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2752) =
      Integer.Sparse.eval keyMomentRow2752 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2752).leftCharge (GramAssembly.key 2752).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3296) := by
    have ha : gramCharges (GramAssembly.key 2752).leftCharge (GramAssembly.key 2752).rightCharge = raw42816 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42816Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42816 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2752).leftCharge (GramAssembly.key 2752).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4607) := by
    have ha : gramCharges (GramAssembly.key 2752).leftCharge (GramAssembly.key 2752).rightCharge = raw42817 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42817Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42817 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2752).leftCharge (GramAssembly.key 2752).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2752).leftCharge (GramAssembly.key 2752).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2752, Integer.Sparse.eval]
  ring

theorem keyMoment2753 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2753) =
      Integer.Sparse.eval keyMomentRow2753 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2753).leftCharge (GramAssembly.key 2753).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3289) := by
    have ha : gramCharges (GramAssembly.key 2753).leftCharge (GramAssembly.key 2753).rightCharge = raw42818 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42818Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42818 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2753).leftCharge (GramAssembly.key 2753).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4599) := by
    have ha : gramCharges (GramAssembly.key 2753).leftCharge (GramAssembly.key 2753).rightCharge = raw42819 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42819Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42819 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2753).leftCharge (GramAssembly.key 2753).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2753).leftCharge (GramAssembly.key 2753).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2753, Integer.Sparse.eval]
  ring

theorem keyMoment2754 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2754) =
      Integer.Sparse.eval keyMomentRow2754 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2754).leftCharge (GramAssembly.key 2754).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3302) := by
    have ha : gramCharges (GramAssembly.key 2754).leftCharge (GramAssembly.key 2754).rightCharge = raw42820 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42820Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42820 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2754).leftCharge (GramAssembly.key 2754).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4609) := by
    have ha : gramCharges (GramAssembly.key 2754).leftCharge (GramAssembly.key 2754).rightCharge = raw42821 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42821Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42821 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2754).leftCharge (GramAssembly.key 2754).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2754).leftCharge (GramAssembly.key 2754).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2754, Integer.Sparse.eval]
  ring

theorem keyMoment2755 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2755) =
      Integer.Sparse.eval keyMomentRow2755 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2755).leftCharge (GramAssembly.key 2755).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3294) := by
    have ha : gramCharges (GramAssembly.key 2755).leftCharge (GramAssembly.key 2755).rightCharge = raw42822 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42822Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42822 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2755).leftCharge (GramAssembly.key 2755).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4603) := by
    have ha : gramCharges (GramAssembly.key 2755).leftCharge (GramAssembly.key 2755).rightCharge = raw42823 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42823Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42823 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2755).leftCharge (GramAssembly.key 2755).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2755).leftCharge (GramAssembly.key 2755).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2755, Integer.Sparse.eval]
  ring

theorem keyMoment2756 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2756) =
      Integer.Sparse.eval keyMomentRow2756 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2756).leftCharge (GramAssembly.key 2756).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3295) := by
    have ha : gramCharges (GramAssembly.key 2756).leftCharge (GramAssembly.key 2756).rightCharge = raw42824 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42824Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42824 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2756).leftCharge (GramAssembly.key 2756).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4592) := by
    have ha : gramCharges (GramAssembly.key 2756).leftCharge (GramAssembly.key 2756).rightCharge = raw42825 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42825Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42825 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2756).leftCharge (GramAssembly.key 2756).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2756).leftCharge (GramAssembly.key 2756).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2756, Integer.Sparse.eval]
  ring

theorem keyMoment2757 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2757) =
      Integer.Sparse.eval keyMomentRow2757 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2757).leftCharge (GramAssembly.key 2757).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3288) := by
    have ha : gramCharges (GramAssembly.key 2757).leftCharge (GramAssembly.key 2757).rightCharge = raw42826 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42826Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42826 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2757).leftCharge (GramAssembly.key 2757).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4589) := by
    have ha : gramCharges (GramAssembly.key 2757).leftCharge (GramAssembly.key 2757).rightCharge = raw42827 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42827Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42827 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2757).leftCharge (GramAssembly.key 2757).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2757).leftCharge (GramAssembly.key 2757).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2757, Integer.Sparse.eval]
  ring

theorem keyMoment2758 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2758) =
      Integer.Sparse.eval keyMomentRow2758 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2758).leftCharge (GramAssembly.key 2758).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3288) := by
    have ha : gramCharges (GramAssembly.key 2758).leftCharge (GramAssembly.key 2758).rightCharge = raw42828 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42828Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42828 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2758).leftCharge (GramAssembly.key 2758).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4589) := by
    have ha : gramCharges (GramAssembly.key 2758).leftCharge (GramAssembly.key 2758).rightCharge = raw42829 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42829Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42829 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2758).leftCharge (GramAssembly.key 2758).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2758).leftCharge (GramAssembly.key 2758).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2758, Integer.Sparse.eval]
  ring

theorem keyMoment2759 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2759) =
      Integer.Sparse.eval keyMomentRow2759 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2759).leftCharge (GramAssembly.key 2759).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3291) := by
    have ha : gramCharges (GramAssembly.key 2759).leftCharge (GramAssembly.key 2759).rightCharge = raw42830 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42830Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42830 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2759).leftCharge (GramAssembly.key 2759).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4591) := by
    have ha : gramCharges (GramAssembly.key 2759).leftCharge (GramAssembly.key 2759).rightCharge = raw42831 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42831Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42831 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2759).leftCharge (GramAssembly.key 2759).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2759).leftCharge (GramAssembly.key 2759).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2759, Integer.Sparse.eval]
  ring

theorem keyMoment2760 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2760) =
      Integer.Sparse.eval keyMomentRow2760 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2760).leftCharge (GramAssembly.key 2760).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3290) := by
    have ha : gramCharges (GramAssembly.key 2760).leftCharge (GramAssembly.key 2760).rightCharge = raw42832 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42832Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42832 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2760).leftCharge (GramAssembly.key 2760).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4590) := by
    have ha : gramCharges (GramAssembly.key 2760).leftCharge (GramAssembly.key 2760).rightCharge = raw42833 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42833Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42833 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2760).leftCharge (GramAssembly.key 2760).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2760).leftCharge (GramAssembly.key 2760).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2760, Integer.Sparse.eval]
  ring

theorem keyMoment2761 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2761) =
      Integer.Sparse.eval keyMomentRow2761 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2761).leftCharge (GramAssembly.key 2761).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3298) := by
    have ha : gramCharges (GramAssembly.key 2761).leftCharge (GramAssembly.key 2761).rightCharge = raw42834 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42834Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42834 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2761).leftCharge (GramAssembly.key 2761).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4594) := by
    have ha : gramCharges (GramAssembly.key 2761).leftCharge (GramAssembly.key 2761).rightCharge = raw42835 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42835Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42835 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2761).leftCharge (GramAssembly.key 2761).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2761).leftCharge (GramAssembly.key 2761).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2761, Integer.Sparse.eval]
  ring

theorem keyMoment2762 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2762) =
      Integer.Sparse.eval keyMomentRow2762 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2762).leftCharge (GramAssembly.key 2762).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3291) := by
    have ha : gramCharges (GramAssembly.key 2762).leftCharge (GramAssembly.key 2762).rightCharge = raw42836 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42836Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42836 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2762).leftCharge (GramAssembly.key 2762).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4591) := by
    have ha : gramCharges (GramAssembly.key 2762).leftCharge (GramAssembly.key 2762).rightCharge = raw42837 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42837Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42837 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2762).leftCharge (GramAssembly.key 2762).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2762).leftCharge (GramAssembly.key 2762).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2762, Integer.Sparse.eval]
  ring

theorem keyMoment2763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2763) =
      Integer.Sparse.eval keyMomentRow2763 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2763).leftCharge (GramAssembly.key 2763).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3297) := by
    have ha : gramCharges (GramAssembly.key 2763).leftCharge (GramAssembly.key 2763).rightCharge = raw42838 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42838Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42838 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2763).leftCharge (GramAssembly.key 2763).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4593) := by
    have ha : gramCharges (GramAssembly.key 2763).leftCharge (GramAssembly.key 2763).rightCharge = raw42839 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42839Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42839 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2763).leftCharge (GramAssembly.key 2763).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2763).leftCharge (GramAssembly.key 2763).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2763, Integer.Sparse.eval]
  ring

theorem keyMoment2764 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2764) =
      Integer.Sparse.eval keyMomentRow2764 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2764).leftCharge (GramAssembly.key 2764).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2149) := by
    have ha : gramCharges (GramAssembly.key 2764).leftCharge (GramAssembly.key 2764).rightCharge = raw42840 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42840Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42840 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2764).leftCharge (GramAssembly.key 2764).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4536) := by
    have ha : gramCharges (GramAssembly.key 2764).leftCharge (GramAssembly.key 2764).rightCharge = raw42841 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42841Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42841 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2764).leftCharge (GramAssembly.key 2764).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2764).leftCharge (GramAssembly.key 2764).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2764, Integer.Sparse.eval]
  ring

theorem keyMoment2765 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2765) =
      Integer.Sparse.eval keyMomentRow2765 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2765).leftCharge (GramAssembly.key 2765).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2172) := by
    have ha : gramCharges (GramAssembly.key 2765).leftCharge (GramAssembly.key 2765).rightCharge = raw42842 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42842Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42842 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2765).leftCharge (GramAssembly.key 2765).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4532) := by
    have ha : gramCharges (GramAssembly.key 2765).leftCharge (GramAssembly.key 2765).rightCharge = raw42843 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42843Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42843 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2765).leftCharge (GramAssembly.key 2765).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2765).leftCharge (GramAssembly.key 2765).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2765, Integer.Sparse.eval]
  ring

theorem keyMoment2766 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2766) =
      Integer.Sparse.eval keyMomentRow2766 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2766).leftCharge (GramAssembly.key 2766).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3258) := by
    have ha : gramCharges (GramAssembly.key 2766).leftCharge (GramAssembly.key 2766).rightCharge = raw42844 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42844Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42844 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2766).leftCharge (GramAssembly.key 2766).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4529) := by
    have ha : gramCharges (GramAssembly.key 2766).leftCharge (GramAssembly.key 2766).rightCharge = raw42845 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42845Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42845 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2766).leftCharge (GramAssembly.key 2766).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2766).leftCharge (GramAssembly.key 2766).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2766, Integer.Sparse.eval]
  ring

theorem keyMoment2767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2767) =
      Integer.Sparse.eval keyMomentRow2767 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2767).leftCharge (GramAssembly.key 2767).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3268) := by
    have ha : gramCharges (GramAssembly.key 2767).leftCharge (GramAssembly.key 2767).rightCharge = raw42846 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42846Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42846 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2767).leftCharge (GramAssembly.key 2767).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4534) := by
    have ha : gramCharges (GramAssembly.key 2767).leftCharge (GramAssembly.key 2767).rightCharge = raw42847 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42847Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42847 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2767).leftCharge (GramAssembly.key 2767).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2767).leftCharge (GramAssembly.key 2767).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2767, Integer.Sparse.eval]
  ring

theorem keyMoment2768 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2768) =
      Integer.Sparse.eval keyMomentRow2768 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2768).leftCharge (GramAssembly.key 2768).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3267) := by
    have ha : gramCharges (GramAssembly.key 2768).leftCharge (GramAssembly.key 2768).rightCharge = raw42848 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42848Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42848 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2768).leftCharge (GramAssembly.key 2768).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4533) := by
    have ha : gramCharges (GramAssembly.key 2768).leftCharge (GramAssembly.key 2768).rightCharge = raw42849 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42849Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42849 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2768).leftCharge (GramAssembly.key 2768).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2768).leftCharge (GramAssembly.key 2768).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2768, Integer.Sparse.eval]
  ring

theorem keyMoment2769 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2769) =
      Integer.Sparse.eval keyMomentRow2769 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2769).leftCharge (GramAssembly.key 2769).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3255) := by
    have ha : gramCharges (GramAssembly.key 2769).leftCharge (GramAssembly.key 2769).rightCharge = raw42850 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42850Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42850 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2769).leftCharge (GramAssembly.key 2769).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4527) := by
    have ha : gramCharges (GramAssembly.key 2769).leftCharge (GramAssembly.key 2769).rightCharge = raw42851 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42851Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42851 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2769).leftCharge (GramAssembly.key 2769).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2769).leftCharge (GramAssembly.key 2769).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2769, Integer.Sparse.eval]
  ring

theorem keyMoment2770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2770) =
      Integer.Sparse.eval keyMomentRow2770 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2770).leftCharge (GramAssembly.key 2770).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3262) := by
    have ha : gramCharges (GramAssembly.key 2770).leftCharge (GramAssembly.key 2770).rightCharge = raw42852 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42852Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42852 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2770).leftCharge (GramAssembly.key 2770).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4531) := by
    have ha : gramCharges (GramAssembly.key 2770).leftCharge (GramAssembly.key 2770).rightCharge = raw42853 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42853Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42853 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2770).leftCharge (GramAssembly.key 2770).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2770).leftCharge (GramAssembly.key 2770).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2770, Integer.Sparse.eval]
  ring

theorem keyMoment2771 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2771) =
      Integer.Sparse.eval keyMomentRow2771 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2771).leftCharge (GramAssembly.key 2771).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3260) := by
    have ha : gramCharges (GramAssembly.key 2771).leftCharge (GramAssembly.key 2771).rightCharge = raw42854 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42854Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42854 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2771).leftCharge (GramAssembly.key 2771).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4528) := by
    have ha : gramCharges (GramAssembly.key 2771).leftCharge (GramAssembly.key 2771).rightCharge = raw42855 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42855Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42855 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2771).leftCharge (GramAssembly.key 2771).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2771).leftCharge (GramAssembly.key 2771).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2771, Integer.Sparse.eval]
  ring

theorem keyMoment2772 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2772) =
      Integer.Sparse.eval keyMomentRow2772 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2772).leftCharge (GramAssembly.key 2772).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3261) := by
    have ha : gramCharges (GramAssembly.key 2772).leftCharge (GramAssembly.key 2772).rightCharge = raw42856 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42856Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42856 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2772).leftCharge (GramAssembly.key 2772).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4530) := by
    have ha : gramCharges (GramAssembly.key 2772).leftCharge (GramAssembly.key 2772).rightCharge = raw42857 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42857Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42857 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2772).leftCharge (GramAssembly.key 2772).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2772).leftCharge (GramAssembly.key 2772).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2772, Integer.Sparse.eval]
  ring

theorem keyMoment2773 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2773) =
      Integer.Sparse.eval keyMomentRow2773 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2773).leftCharge (GramAssembly.key 2773).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1516) := by
    have ha : gramCharges (GramAssembly.key 2773).leftCharge (GramAssembly.key 2773).rightCharge = raw42858 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42858Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42858 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2773).leftCharge (GramAssembly.key 2773).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4156) := by
    have ha : gramCharges (GramAssembly.key 2773).leftCharge (GramAssembly.key 2773).rightCharge = raw42859 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42859Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42859 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2773).leftCharge (GramAssembly.key 2773).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2773).leftCharge (GramAssembly.key 2773).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2773, Integer.Sparse.eval]
  ring

theorem keyMoment2774 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2774) =
      Integer.Sparse.eval keyMomentRow2774 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2774).leftCharge (GramAssembly.key 2774).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1672) := by
    have ha : gramCharges (GramAssembly.key 2774).leftCharge (GramAssembly.key 2774).rightCharge = raw42860 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42860Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42860 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2774).leftCharge (GramAssembly.key 2774).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4330) := by
    have ha : gramCharges (GramAssembly.key 2774).leftCharge (GramAssembly.key 2774).rightCharge = raw42861 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42861Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42861 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2774).leftCharge (GramAssembly.key 2774).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2774).leftCharge (GramAssembly.key 2774).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2774, Integer.Sparse.eval]
  ring

theorem keyMoment2775 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2775) =
      Integer.Sparse.eval keyMomentRow2775 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2775).leftCharge (GramAssembly.key 2775).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3272) := by
    have ha : gramCharges (GramAssembly.key 2775).leftCharge (GramAssembly.key 2775).rightCharge = raw42862 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42862Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42862 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2775).leftCharge (GramAssembly.key 2775).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4535) := by
    have ha : gramCharges (GramAssembly.key 2775).leftCharge (GramAssembly.key 2775).rightCharge = raw42863 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42863Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42863 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2775).leftCharge (GramAssembly.key 2775).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2775).leftCharge (GramAssembly.key 2775).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2775, Integer.Sparse.eval]
  ring

theorem keyMoment2776 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2776) =
      Integer.Sparse.eval keyMomentRow2776 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2776).leftCharge (GramAssembly.key 2776).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2755) := by
    have ha : gramCharges (GramAssembly.key 2776).leftCharge (GramAssembly.key 2776).rightCharge = raw42864 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42864Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42864 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2776).leftCharge (GramAssembly.key 2776).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4890) := by
    have ha : gramCharges (GramAssembly.key 2776).leftCharge (GramAssembly.key 2776).rightCharge = raw42865 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42865Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42865 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2776).leftCharge (GramAssembly.key 2776).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2776).leftCharge (GramAssembly.key 2776).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2776, Integer.Sparse.eval]
  ring

theorem keyMoment2777 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2777) =
      Integer.Sparse.eval keyMomentRow2777 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2777).leftCharge (GramAssembly.key 2777).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2753) := by
    have ha : gramCharges (GramAssembly.key 2777).leftCharge (GramAssembly.key 2777).rightCharge = raw42866 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42866Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42866 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2777).leftCharge (GramAssembly.key 2777).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5284) := by
    have ha : gramCharges (GramAssembly.key 2777).leftCharge (GramAssembly.key 2777).rightCharge = raw42867 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42867Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42867 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2777).leftCharge (GramAssembly.key 2777).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2777).leftCharge (GramAssembly.key 2777).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2777, Integer.Sparse.eval]
  ring

theorem keyMoment2778 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2778) =
      Integer.Sparse.eval keyMomentRow2778 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2778).leftCharge (GramAssembly.key 2778).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2751) := by
    have ha : gramCharges (GramAssembly.key 2778).leftCharge (GramAssembly.key 2778).rightCharge = raw42868 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42868Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42868 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2778).leftCharge (GramAssembly.key 2778).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5282) := by
    have ha : gramCharges (GramAssembly.key 2778).leftCharge (GramAssembly.key 2778).rightCharge = raw42869 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42869Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42869 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2778).leftCharge (GramAssembly.key 2778).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2778).leftCharge (GramAssembly.key 2778).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2778, Integer.Sparse.eval]
  ring

theorem keyMoment2779 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2779) =
      Integer.Sparse.eval keyMomentRow2779 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2779).leftCharge (GramAssembly.key 2779).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2710) := by
    have ha : gramCharges (GramAssembly.key 2779).leftCharge (GramAssembly.key 2779).rightCharge = raw42870 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42870Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42870 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2779).leftCharge (GramAssembly.key 2779).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2779).leftCharge (GramAssembly.key 2779).rightCharge = raw42871 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42871Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42871 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2779).leftCharge (GramAssembly.key 2779).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2779).leftCharge (GramAssembly.key 2779).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2779, Integer.Sparse.eval]
  ring

theorem keyMoment2780 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2780) =
      Integer.Sparse.eval keyMomentRow2780 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2780).leftCharge (GramAssembly.key 2780).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2662) := by
    have ha : gramCharges (GramAssembly.key 2780).leftCharge (GramAssembly.key 2780).rightCharge = raw42872 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42872Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42872 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2780).leftCharge (GramAssembly.key 2780).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5220) := by
    have ha : gramCharges (GramAssembly.key 2780).leftCharge (GramAssembly.key 2780).rightCharge = raw42873 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42873Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42873 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2780).leftCharge (GramAssembly.key 2780).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2780).leftCharge (GramAssembly.key 2780).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2780, Integer.Sparse.eval]
  ring

theorem keyMoment2781 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2781) =
      Integer.Sparse.eval keyMomentRow2781 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2781).leftCharge (GramAssembly.key 2781).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2661) := by
    have ha : gramCharges (GramAssembly.key 2781).leftCharge (GramAssembly.key 2781).rightCharge = raw42874 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42874Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42874 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2781).leftCharge (GramAssembly.key 2781).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5219) := by
    have ha : gramCharges (GramAssembly.key 2781).leftCharge (GramAssembly.key 2781).rightCharge = raw42875 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42875Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42875 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2781).leftCharge (GramAssembly.key 2781).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2781).leftCharge (GramAssembly.key 2781).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2781, Integer.Sparse.eval]
  ring

theorem keyMoment2782 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2782) =
      Integer.Sparse.eval keyMomentRow2782 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2782).leftCharge (GramAssembly.key 2782).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2724) := by
    have ha : gramCharges (GramAssembly.key 2782).leftCharge (GramAssembly.key 2782).rightCharge = raw42876 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42876Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42876 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2782).leftCharge (GramAssembly.key 2782).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2782).leftCharge (GramAssembly.key 2782).rightCharge = raw42877 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42877Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42877 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2782).leftCharge (GramAssembly.key 2782).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2782).leftCharge (GramAssembly.key 2782).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2782, Integer.Sparse.eval]
  ring

theorem keyMoment2783 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2783) =
      Integer.Sparse.eval keyMomentRow2783 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2783).leftCharge (GramAssembly.key 2783).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2763) := by
    have ha : gramCharges (GramAssembly.key 2783).leftCharge (GramAssembly.key 2783).rightCharge = raw42878 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42878Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42878 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2783).leftCharge (GramAssembly.key 2783).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5289) := by
    have ha : gramCharges (GramAssembly.key 2783).leftCharge (GramAssembly.key 2783).rightCharge = raw42879 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42879Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42879 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2783).leftCharge (GramAssembly.key 2783).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2783).leftCharge (GramAssembly.key 2783).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2783, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2752 : keyMomentRows (2752 : Fin 2886) =
    keyMomentRow2752 := by decide +kernel

theorem keyMomentRowsAt2753 : keyMomentRows (2753 : Fin 2886) =
    keyMomentRow2753 := by decide +kernel

theorem keyMomentRowsAt2754 : keyMomentRows (2754 : Fin 2886) =
    keyMomentRow2754 := by decide +kernel

theorem keyMomentRowsAt2755 : keyMomentRows (2755 : Fin 2886) =
    keyMomentRow2755 := by decide +kernel

theorem keyMomentRowsAt2756 : keyMomentRows (2756 : Fin 2886) =
    keyMomentRow2756 := by decide +kernel

theorem keyMomentRowsAt2757 : keyMomentRows (2757 : Fin 2886) =
    keyMomentRow2757 := by decide +kernel

theorem keyMomentRowsAt2758 : keyMomentRows (2758 : Fin 2886) =
    keyMomentRow2758 := by decide +kernel

theorem keyMomentRowsAt2759 : keyMomentRows (2759 : Fin 2886) =
    keyMomentRow2759 := by decide +kernel

theorem keyMomentRowsAt2760 : keyMomentRows (2760 : Fin 2886) =
    keyMomentRow2760 := by decide +kernel

theorem keyMomentRowsAt2761 : keyMomentRows (2761 : Fin 2886) =
    keyMomentRow2761 := by decide +kernel

theorem keyMomentRowsAt2762 : keyMomentRows (2762 : Fin 2886) =
    keyMomentRow2762 := by decide +kernel

theorem keyMomentRowsAt2763 : keyMomentRows (2763 : Fin 2886) =
    keyMomentRow2763 := by decide +kernel

theorem keyMomentRowsAt2764 : keyMomentRows (2764 : Fin 2886) =
    keyMomentRow2764 := by decide +kernel

theorem keyMomentRowsAt2765 : keyMomentRows (2765 : Fin 2886) =
    keyMomentRow2765 := by decide +kernel

theorem keyMomentRowsAt2766 : keyMomentRows (2766 : Fin 2886) =
    keyMomentRow2766 := by decide +kernel

theorem keyMomentRowsAt2767 : keyMomentRows (2767 : Fin 2886) =
    keyMomentRow2767 := by decide +kernel

theorem keyMomentRowsAt2768 : keyMomentRows (2768 : Fin 2886) =
    keyMomentRow2768 := by decide +kernel

theorem keyMomentRowsAt2769 : keyMomentRows (2769 : Fin 2886) =
    keyMomentRow2769 := by decide +kernel

theorem keyMomentRowsAt2770 : keyMomentRows (2770 : Fin 2886) =
    keyMomentRow2770 := by decide +kernel

theorem keyMomentRowsAt2771 : keyMomentRows (2771 : Fin 2886) =
    keyMomentRow2771 := by decide +kernel

theorem keyMomentRowsAt2772 : keyMomentRows (2772 : Fin 2886) =
    keyMomentRow2772 := by decide +kernel

theorem keyMomentRowsAt2773 : keyMomentRows (2773 : Fin 2886) =
    keyMomentRow2773 := by decide +kernel

theorem keyMomentRowsAt2774 : keyMomentRows (2774 : Fin 2886) =
    keyMomentRow2774 := by decide +kernel

theorem keyMomentRowsAt2775 : keyMomentRows (2775 : Fin 2886) =
    keyMomentRow2775 := by decide +kernel

theorem keyMomentRowsAt2776 : keyMomentRows (2776 : Fin 2886) =
    keyMomentRow2776 := by decide +kernel

theorem keyMomentRowsAt2777 : keyMomentRows (2777 : Fin 2886) =
    keyMomentRow2777 := by decide +kernel

theorem keyMomentRowsAt2778 : keyMomentRows (2778 : Fin 2886) =
    keyMomentRow2778 := by decide +kernel

theorem keyMomentRowsAt2779 : keyMomentRows (2779 : Fin 2886) =
    keyMomentRow2779 := by decide +kernel

theorem keyMomentRowsAt2780 : keyMomentRows (2780 : Fin 2886) =
    keyMomentRow2780 := by decide +kernel

theorem keyMomentRowsAt2781 : keyMomentRows (2781 : Fin 2886) =
    keyMomentRow2781 := by decide +kernel

theorem keyMomentRowsAt2782 : keyMomentRows (2782 : Fin 2886) =
    keyMomentRow2782 := by decide +kernel

theorem keyMomentRowsAt2783 : keyMomentRows (2783 : Fin 2886) =
    keyMomentRow2783 := by decide +kernel

theorem keyMomentChunkSound86_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 86) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2752 ∨ k.val = 2753 ∨ k.val = 2754 ∨ k.val = 2755 ∨ k.val = 2756 ∨ k.val = 2757 ∨ k.val = 2758 ∨ k.val = 2759 ∨ k.val = 2760 ∨ k.val = 2761 ∨ k.val = 2762 ∨ k.val = 2763 ∨ k.val = 2764 ∨ k.val = 2765 ∨ k.val = 2766 ∨ k.val = 2767 ∨ k.val = 2768 ∨ k.val = 2769 ∨ k.val = 2770 ∨ k.val = 2771 ∨ k.val = 2772 ∨ k.val = 2773 ∨ k.val = 2774 ∨ k.val = 2775 ∨ k.val = 2776 ∨ k.val = 2777 ∨ k.val = 2778 ∨ k.val = 2779 ∨ k.val = 2780 ∨ k.val = 2781 ∨ k.val = 2782 ∨ k.val = 2783 := by omega
  rcases heq with h2752 | h2753 | h2754 | h2755 | h2756 | h2757 | h2758 | h2759 | h2760 | h2761 | h2762 | h2763 | h2764 | h2765 | h2766 | h2767 | h2768 | h2769 | h2770 | h2771 | h2772 | h2773 | h2774 | h2775 | h2776 | h2777 | h2778 | h2779 | h2780 | h2781 | h2782 | h2783
  · have he : k = (2752 : Fin 2886) := Fin.ext h2752
    subst k
    rw [keyMomentRowsAt2752]
    exact keyMoment2752 B hB
  · have he : k = (2753 : Fin 2886) := Fin.ext h2753
    subst k
    rw [keyMomentRowsAt2753]
    exact keyMoment2753 B hB
  · have he : k = (2754 : Fin 2886) := Fin.ext h2754
    subst k
    rw [keyMomentRowsAt2754]
    exact keyMoment2754 B hB
  · have he : k = (2755 : Fin 2886) := Fin.ext h2755
    subst k
    rw [keyMomentRowsAt2755]
    exact keyMoment2755 B hB
  · have he : k = (2756 : Fin 2886) := Fin.ext h2756
    subst k
    rw [keyMomentRowsAt2756]
    exact keyMoment2756 B hB
  · have he : k = (2757 : Fin 2886) := Fin.ext h2757
    subst k
    rw [keyMomentRowsAt2757]
    exact keyMoment2757 B hB
  · have he : k = (2758 : Fin 2886) := Fin.ext h2758
    subst k
    rw [keyMomentRowsAt2758]
    exact keyMoment2758 B hB
  · have he : k = (2759 : Fin 2886) := Fin.ext h2759
    subst k
    rw [keyMomentRowsAt2759]
    exact keyMoment2759 B hB
  · have he : k = (2760 : Fin 2886) := Fin.ext h2760
    subst k
    rw [keyMomentRowsAt2760]
    exact keyMoment2760 B hB
  · have he : k = (2761 : Fin 2886) := Fin.ext h2761
    subst k
    rw [keyMomentRowsAt2761]
    exact keyMoment2761 B hB
  · have he : k = (2762 : Fin 2886) := Fin.ext h2762
    subst k
    rw [keyMomentRowsAt2762]
    exact keyMoment2762 B hB
  · have he : k = (2763 : Fin 2886) := Fin.ext h2763
    subst k
    rw [keyMomentRowsAt2763]
    exact keyMoment2763 B hB
  · have he : k = (2764 : Fin 2886) := Fin.ext h2764
    subst k
    rw [keyMomentRowsAt2764]
    exact keyMoment2764 B hB
  · have he : k = (2765 : Fin 2886) := Fin.ext h2765
    subst k
    rw [keyMomentRowsAt2765]
    exact keyMoment2765 B hB
  · have he : k = (2766 : Fin 2886) := Fin.ext h2766
    subst k
    rw [keyMomentRowsAt2766]
    exact keyMoment2766 B hB
  · have he : k = (2767 : Fin 2886) := Fin.ext h2767
    subst k
    rw [keyMomentRowsAt2767]
    exact keyMoment2767 B hB
  · have he : k = (2768 : Fin 2886) := Fin.ext h2768
    subst k
    rw [keyMomentRowsAt2768]
    exact keyMoment2768 B hB
  · have he : k = (2769 : Fin 2886) := Fin.ext h2769
    subst k
    rw [keyMomentRowsAt2769]
    exact keyMoment2769 B hB
  · have he : k = (2770 : Fin 2886) := Fin.ext h2770
    subst k
    rw [keyMomentRowsAt2770]
    exact keyMoment2770 B hB
  · have he : k = (2771 : Fin 2886) := Fin.ext h2771
    subst k
    rw [keyMomentRowsAt2771]
    exact keyMoment2771 B hB
  · have he : k = (2772 : Fin 2886) := Fin.ext h2772
    subst k
    rw [keyMomentRowsAt2772]
    exact keyMoment2772 B hB
  · have he : k = (2773 : Fin 2886) := Fin.ext h2773
    subst k
    rw [keyMomentRowsAt2773]
    exact keyMoment2773 B hB
  · have he : k = (2774 : Fin 2886) := Fin.ext h2774
    subst k
    rw [keyMomentRowsAt2774]
    exact keyMoment2774 B hB
  · have he : k = (2775 : Fin 2886) := Fin.ext h2775
    subst k
    rw [keyMomentRowsAt2775]
    exact keyMoment2775 B hB
  · have he : k = (2776 : Fin 2886) := Fin.ext h2776
    subst k
    rw [keyMomentRowsAt2776]
    exact keyMoment2776 B hB
  · have he : k = (2777 : Fin 2886) := Fin.ext h2777
    subst k
    rw [keyMomentRowsAt2777]
    exact keyMoment2777 B hB
  · have he : k = (2778 : Fin 2886) := Fin.ext h2778
    subst k
    rw [keyMomentRowsAt2778]
    exact keyMoment2778 B hB
  · have he : k = (2779 : Fin 2886) := Fin.ext h2779
    subst k
    rw [keyMomentRowsAt2779]
    exact keyMoment2779 B hB
  · have he : k = (2780 : Fin 2886) := Fin.ext h2780
    subst k
    rw [keyMomentRowsAt2780]
    exact keyMoment2780 B hB
  · have he : k = (2781 : Fin 2886) := Fin.ext h2781
    subst k
    rw [keyMomentRowsAt2781]
    exact keyMoment2781 B hB
  · have he : k = (2782 : Fin 2886) := Fin.ext h2782
    subst k
    rw [keyMomentRowsAt2782]
    exact keyMoment2782 B hB
  · have he : k = (2783 : Fin 2886) := Fin.ext h2783
    subst k
    rw [keyMomentRowsAt2783]
    exact keyMoment2783 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound86_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound86_e_oai
