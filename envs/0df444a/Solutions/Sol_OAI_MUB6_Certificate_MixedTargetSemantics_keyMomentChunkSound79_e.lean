-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound79_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:04:21.284202+00:00
-- url     : https://prove2.me/submissions/6abd7777-f199-499a-90e4-90b8eb69a214

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical331
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical42368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42368 raw42368Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw42368 raw42368Labels = mixedMoment B raw42368step0 raw42368step0Labels := by
      have hz : ∀ j, raw42368 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42368step0 = (fun i j => raw42368 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42368step0 raw42368; decide +kernel
      have hl : raw42368step0Labels = raw42368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42368 raw42368Labels permutation434 hz
    mixedMoment B raw42368step0 raw42368step0Labels = mixedMoment B raw42368step1 raw42368step1Labels := by
      have ha : raw42368step1 = (fun i j => raw42368step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42368step1 raw42368step0; decide +kernel
      have hl : raw42368step1Labels = raw42368step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42368step0 raw42368step0Labels permutation109 permutation4
    mixedMoment B raw42368step1 raw42368step1Labels = mixedMoment B raw42368step2 raw42368step2Labels := by
      have ha : raw42368step2 = raw42368step1 := by apply Matrix.ext; unfold raw42368step2 raw42368step1; decide +kernel
      have hl : raw42368step1Labels = labelEmbedding1 ∘ raw42368step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42368step1 raw42368step1Labels raw42368step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2678 node2678Labels := by rfl

theorem canonical42369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42369 raw42369Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw42369 raw42369Labels = mixedMoment B raw42369step0 raw42369step0Labels := by
      have hz : ∀ j, raw42369 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42369step0 = (fun i j => raw42369 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42369step0 raw42369; decide +kernel
      have hl : raw42369step0Labels = raw42369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42369 raw42369Labels permutation434 hz
    mixedMoment B raw42369step0 raw42369step0Labels = mixedMoment B raw42369step1 raw42369step1Labels := by
      have ha : raw42369step1 = (fun i j => raw42369step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42369step1 raw42369step0; decide +kernel
      have hl : raw42369step1Labels = raw42369step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42369step0 raw42369step0Labels permutation109 permutation4
    mixedMoment B raw42369step1 raw42369step1Labels = mixedMoment B raw42369step2 raw42369step2Labels := by
      have ha : raw42369step2 = raw42369step1 := by apply Matrix.ext; unfold raw42369step2 raw42369step1; decide +kernel
      have hl : raw42369step1Labels = labelEmbedding10 ∘ raw42369step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42369step1 raw42369step1Labels raw42369step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

theorem canonical42370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42370 raw42370Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw42370 raw42370Labels = mixedMoment B raw42370step0 raw42370step0Labels := by
      have ha : raw42370step0 = (fun i j => raw42370 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42370step0 raw42370; decide +kernel
      have hl : raw42370step0Labels = raw42370Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42370 raw42370Labels permutation158 permutation2
    mixedMoment B raw42370step0 raw42370step0Labels = mixedMoment B raw42370step1 raw42370step1Labels := by
      have ha : raw42370step1 = raw42370step0 := by apply Matrix.ext; unfold raw42370step1 raw42370step0; decide +kernel
      have hl : raw42370step0Labels = labelEmbedding1 ∘ raw42370step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42370step0 raw42370step0Labels raw42370step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3872 node3872Labels := by rfl

theorem canonical42371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42371 raw42371Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42371 raw42371Labels = mixedMoment B raw42371step0 raw42371step0Labels := by
      have ha : raw42371step0 = (fun i j => raw42371 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42371step0 raw42371; decide +kernel
      have hl : raw42371step0Labels = raw42371Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42371 raw42371Labels permutation688 permutation3
    mixedMoment B raw42371step0 raw42371step0Labels = mixedMoment B raw42371step1 raw42371step1Labels := by
      have ha : raw42371step1 = -raw42371step0 := by apply Matrix.ext; change ∀ i j, raw42371step1 i j = -(raw42371step0 i j); unfold raw42371step1 raw42371step0; decide +kernel
      have hl : raw42371step1Labels = raw42371step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42371step1 raw42371step1Labels = mixedMoment B raw42371step2 raw42371step2Labels := by
      have ha : raw42371step2 = raw42371step1 := by apply Matrix.ext; unfold raw42371step2 raw42371step1; decide +kernel
      have hl : raw42371step1Labels = labelEmbedding7 ∘ raw42371step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42371step1 raw42371step1Labels raw42371step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical42372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42372 raw42372Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw42372 raw42372Labels = mixedMoment B raw42372step0 raw42372step0Labels := by
      have ha : raw42372step0 = (fun i j => raw42372 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42372step0 raw42372; decide +kernel
      have hl : raw42372step0Labels = raw42372Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42372 raw42372Labels permutation158 permutation2
    mixedMoment B raw42372step0 raw42372step0Labels = mixedMoment B raw42372step1 raw42372step1Labels := by
      have ha : raw42372step1 = raw42372step0 := by apply Matrix.ext; unfold raw42372step1 raw42372step0; decide +kernel
      have hl : raw42372step0Labels = labelEmbedding1 ∘ raw42372step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42372step0 raw42372step0Labels raw42372step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical42373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42373 raw42373Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42373 raw42373Labels = mixedMoment B raw42373step0 raw42373step0Labels := by
      have ha : raw42373step0 = (fun i j => raw42373 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42373step0 raw42373; decide +kernel
      have hl : raw42373step0Labels = raw42373Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42373 raw42373Labels permutation212 permutation7
    mixedMoment B raw42373step0 raw42373step0Labels = mixedMoment B raw42373step1 raw42373step1Labels := by
      have ha : raw42373step1 = -raw42373step0 := by apply Matrix.ext; change ∀ i j, raw42373step1 i j = -(raw42373step0 i j); unfold raw42373step1 raw42373step0; decide +kernel
      have hl : raw42373step1Labels = raw42373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42373step1 raw42373step1Labels = mixedMoment B raw42373step2 raw42373step2Labels := by
      have ha : raw42373step2 = raw42373step1 := by apply Matrix.ext; unfold raw42373step2 raw42373step1; decide +kernel
      have hl : raw42373step1Labels = labelEmbedding6 ∘ raw42373step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42373step1 raw42373step1Labels raw42373step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical42374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42374 raw42374Labels = mixedMoment B node3870 node3870Labels := by
  calc
    mixedMoment B raw42374 raw42374Labels = mixedMoment B raw42374step0 raw42374step0Labels := by
      have ha : raw42374step0 = (fun i j => raw42374 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42374step0 raw42374; decide +kernel
      have hl : raw42374step0Labels = raw42374Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42374 raw42374Labels permutation158 permutation2
    mixedMoment B raw42374step0 raw42374step0Labels = mixedMoment B raw42374step1 raw42374step1Labels := by
      have ha : raw42374step1 = raw42374step0 := by apply Matrix.ext; unfold raw42374step1 raw42374step0; decide +kernel
      have hl : raw42374step0Labels = labelEmbedding1 ∘ raw42374step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42374step0 raw42374step0Labels raw42374step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3870 node3870Labels := by rfl

theorem canonical42375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42375 raw42375Labels = mixedMoment B node5420 node5420Labels := by
  calc
    mixedMoment B raw42375 raw42375Labels = mixedMoment B raw42375step0 raw42375step0Labels := by
      have ha : raw42375step0 = (fun i j => raw42375 (permutation634 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42375step0 raw42375; decide +kernel
      have hl : raw42375step0Labels = raw42375Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42375 raw42375Labels permutation634 permutation7
    mixedMoment B raw42375step0 raw42375step0Labels = mixedMoment B raw42375step1 raw42375step1Labels := by
      have ha : raw42375step1 = raw42375step0 := by apply Matrix.ext; unfold raw42375step1 raw42375step0; decide +kernel
      have hl : raw42375step0Labels = labelEmbedding6 ∘ raw42375step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42375step0 raw42375step0Labels raw42375step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5420 node5420Labels := by rfl

theorem canonical42376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42376 raw42376Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw42376 raw42376Labels = mixedMoment B raw42376step0 raw42376step0Labels := by
      have ha : raw42376step0 = (fun i j => raw42376 (permutation488 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42376step0 raw42376; decide +kernel
      have hl : raw42376step0Labels = raw42376Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42376 raw42376Labels permutation488 permutation4
    mixedMoment B raw42376step0 raw42376step0Labels = mixedMoment B raw42376step1 raw42376step1Labels := by
      have ha : raw42376step1 = raw42376step0 := by apply Matrix.ext; unfold raw42376step1 raw42376step0; decide +kernel
      have hl : raw42376step0Labels = labelEmbedding1 ∘ raw42376step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42376step0 raw42376step0Labels raw42376step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

theorem canonical42377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42377 raw42377Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw42377 raw42377Labels = mixedMoment B raw42377step0 raw42377step0Labels := by
      have ha : raw42377step0 = (fun i j => raw42377 (permutation445 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42377step0 raw42377; decide +kernel
      have hl : raw42377step0Labels = raw42377Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42377 raw42377Labels permutation445 permutation6
    mixedMoment B raw42377step0 raw42377step0Labels = mixedMoment B raw42377step1 raw42377step1Labels := by
      have ha : raw42377step1 = -raw42377step0 := by apply Matrix.ext; change ∀ i j, raw42377step1 i j = -(raw42377step0 i j); unfold raw42377step1 raw42377step0; decide +kernel
      have hl : raw42377step1Labels = raw42377step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5381 node5381Labels := by rfl

theorem canonical42378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42378 raw42378Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw42378 raw42378Labels = mixedMoment B raw42378step0 raw42378step0Labels := by
      have ha : raw42378step0 = (fun i j => raw42378 (permutation598 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42378step0 raw42378; decide +kernel
      have hl : raw42378step0Labels = raw42378Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42378 raw42378Labels permutation598 permutation4
    mixedMoment B raw42378step0 raw42378step0Labels = mixedMoment B raw42378step1 raw42378step1Labels := by
      have ha : raw42378step1 = raw42378step0 := by apply Matrix.ext; unfold raw42378step1 raw42378step0; decide +kernel
      have hl : raw42378step0Labels = labelEmbedding1 ∘ raw42378step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42378step0 raw42378step0Labels raw42378step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2662 node2662Labels := by rfl

theorem canonical42379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42379 raw42379Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw42379 raw42379Labels = mixedMoment B raw42379step0 raw42379step0Labels := by
      have ha : raw42379step0 = (fun i j => raw42379 (permutation598 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42379step0 raw42379; decide +kernel
      have hl : raw42379step0Labels = raw42379Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42379 raw42379Labels permutation598 permutation4
    mixedMoment B raw42379step0 raw42379step0Labels = mixedMoment B raw42379step1 raw42379step1Labels := by
      have ha : raw42379step1 = raw42379step0 := by apply Matrix.ext; unfold raw42379step1 raw42379step0; decide +kernel
      have hl : raw42379step0Labels = labelEmbedding10 ∘ raw42379step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42379step0 raw42379step0Labels raw42379step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

theorem canonical42380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42380 raw42380Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw42380 raw42380Labels = mixedMoment B raw42380step0 raw42380step0Labels := by
      have ha : raw42380step0 = (fun i j => raw42380 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42380step0 raw42380; decide +kernel
      have hl : raw42380step0Labels = raw42380Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42380 raw42380Labels permutation157 permutation2
    mixedMoment B raw42380step0 raw42380step0Labels = mixedMoment B raw42380step1 raw42380step1Labels := by
      have ha : raw42380step1 = raw42380step0 := by apply Matrix.ext; unfold raw42380step1 raw42380step0; decide +kernel
      have hl : raw42380step0Labels = labelEmbedding1 ∘ raw42380step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42380step0 raw42380step0Labels raw42380step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical42381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42381 raw42381Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw42381 raw42381Labels = mixedMoment B raw42381step0 raw42381step0Labels := by
      have ha : raw42381step0 = (fun i j => raw42381 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42381step0 raw42381; decide +kernel
      have hl : raw42381step0Labels = raw42381Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42381 raw42381Labels permutation157 permutation2
    mixedMoment B raw42381step0 raw42381step0Labels = mixedMoment B raw42381step1 raw42381step1Labels := by
      have ha : raw42381step1 = raw42381step0 := by apply Matrix.ext; unfold raw42381step1 raw42381step0; decide +kernel
      have hl : raw42381step0Labels = labelEmbedding8 ∘ raw42381step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42381step0 raw42381step0Labels raw42381step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical42382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42382 raw42382Labels = mixedMoment B node3882 node3882Labels := by
  calc
    mixedMoment B raw42382 raw42382Labels = mixedMoment B raw42382step0 raw42382step0Labels := by
      have ha : raw42382step0 = raw42382 := by apply Matrix.ext; unfold raw42382step0 raw42382; decide +kernel
      have hl : raw42382Labels = labelEmbedding1 ∘ raw42382step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42382 raw42382Labels raw42382step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3882 node3882Labels := by rfl

theorem canonical42383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42383 raw42383Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw42383 raw42383Labels = mixedMoment B raw42383step0 raw42383step0Labels := by
      have ha : raw42383step0 = raw42383 := by apply Matrix.ext; unfold raw42383step0 raw42383; decide +kernel
      have hl : raw42383Labels = labelEmbedding8 ∘ raw42383step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42383 raw42383Labels raw42383step0Labels labelEmbedding8 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical42384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42384 raw42384Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw42384 raw42384Labels = mixedMoment B raw42384step0 raw42384step0Labels := by
      have hz : ∀ j, raw42384 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42384step0 = (fun i j => raw42384 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42384step0 raw42384; decide +kernel
      have hl : raw42384step0Labels = raw42384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42384 raw42384Labels permutation434 hz
    mixedMoment B raw42384step0 raw42384step0Labels = mixedMoment B raw42384step1 raw42384step1Labels := by
      have hz : ∀ j, raw42384step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42384step1 = (fun i j => raw42384step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42384step1 raw42384step0; decide +kernel
      have hl : raw42384step1Labels = raw42384step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42384step0 raw42384step0Labels permutation80 hz
    mixedMoment B raw42384step1 raw42384step1Labels = mixedMoment B raw42384step2 raw42384step2Labels := by
      have ha : raw42384step2 = (fun i j => raw42384step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42384step2 raw42384step1; decide +kernel
      have hl : raw42384step2Labels = raw42384step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42384step1 raw42384step1Labels permutation27 permutation4
    mixedMoment B raw42384step2 raw42384step2Labels = mixedMoment B raw42384step3 raw42384step3Labels := by
      have ha : raw42384step3 = raw42384step2 := by apply Matrix.ext; unfold raw42384step3 raw42384step2; decide +kernel
      have hl : raw42384step2Labels = labelEmbedding1 ∘ raw42384step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42384step2 raw42384step2Labels raw42384step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3055 node3055Labels := by rfl

theorem canonical42385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42385 raw42385Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw42385 raw42385Labels = mixedMoment B raw42385step0 raw42385step0Labels := by
      have hz : ∀ j, raw42385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42385step0 = (fun i j => raw42385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42385step0 raw42385; decide +kernel
      have hl : raw42385step0Labels = raw42385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42385 raw42385Labels permutation434 hz
    mixedMoment B raw42385step0 raw42385step0Labels = mixedMoment B raw42385step1 raw42385step1Labels := by
      have hz : ∀ j, raw42385step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42385step1 = (fun i j => raw42385step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42385step1 raw42385step0; decide +kernel
      have hl : raw42385step1Labels = raw42385step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42385step0 raw42385step0Labels permutation80 hz
    mixedMoment B raw42385step1 raw42385step1Labels = mixedMoment B raw42385step2 raw42385step2Labels := by
      have ha : raw42385step2 = (fun i j => raw42385step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42385step2 raw42385step1; decide +kernel
      have hl : raw42385step2Labels = raw42385step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42385step1 raw42385step1Labels permutation27 permutation5
    mixedMoment B raw42385step2 raw42385step2Labels = mixedMoment B raw42385step3 raw42385step3Labels := by
      have ha : raw42385step3 = raw42385step2 := by apply Matrix.ext; unfold raw42385step3 raw42385step2; decide +kernel
      have hl : raw42385step2Labels = labelEmbedding9 ∘ raw42385step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42385step2 raw42385step2Labels raw42385step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

theorem canonical42386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42386 raw42386Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw42386 raw42386Labels = mixedMoment B raw42386step0 raw42386step0Labels := by
      have hz : ∀ j, raw42386 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42386step0 = (fun i j => raw42386 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42386step0 raw42386; decide +kernel
      have hl : raw42386step0Labels = raw42386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42386 raw42386Labels permutation434 hz
    mixedMoment B raw42386step0 raw42386step0Labels = mixedMoment B raw42386step1 raw42386step1Labels := by
      have hz : ∀ j, raw42386step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42386step1 = (fun i j => raw42386step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42386step1 raw42386step0; decide +kernel
      have hl : raw42386step1Labels = raw42386step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42386step0 raw42386step0Labels permutation80 hz
    mixedMoment B raw42386step1 raw42386step1Labels = mixedMoment B raw42386step2 raw42386step2Labels := by
      have ha : raw42386step2 = (fun i j => raw42386step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42386step2 raw42386step1; decide +kernel
      have hl : raw42386step2Labels = raw42386step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42386step1 raw42386step1Labels permutation21 permutation4
    mixedMoment B raw42386step2 raw42386step2Labels = mixedMoment B raw42386step3 raw42386step3Labels := by
      have ha : raw42386step3 = raw42386step2 := by apply Matrix.ext; unfold raw42386step3 raw42386step2; decide +kernel
      have hl : raw42386step2Labels = labelEmbedding1 ∘ raw42386step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42386step2 raw42386step2Labels raw42386step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2687 node2687Labels := by rfl

theorem canonical42387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42387 raw42387Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw42387 raw42387Labels = mixedMoment B raw42387step0 raw42387step0Labels := by
      have hz : ∀ j, raw42387 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42387step0 = (fun i j => raw42387 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42387step0 raw42387; decide +kernel
      have hl : raw42387step0Labels = raw42387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42387 raw42387Labels permutation434 hz
    mixedMoment B raw42387step0 raw42387step0Labels = mixedMoment B raw42387step1 raw42387step1Labels := by
      have hz : ∀ j, raw42387step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42387step1 = (fun i j => raw42387step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42387step1 raw42387step0; decide +kernel
      have hl : raw42387step1Labels = raw42387step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42387step0 raw42387step0Labels permutation80 hz
    mixedMoment B raw42387step1 raw42387step1Labels = mixedMoment B raw42387step2 raw42387step2Labels := by
      have ha : raw42387step2 = (fun i j => raw42387step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42387step2 raw42387step1; decide +kernel
      have hl : raw42387step2Labels = raw42387step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42387step1 raw42387step1Labels permutation29 permutation7
    mixedMoment B raw42387step2 raw42387step2Labels = mixedMoment B raw42387step3 raw42387step3Labels := by
      have ha : raw42387step3 = raw42387step2 := by apply Matrix.ext; unfold raw42387step3 raw42387step2; decide +kernel
      have hl : raw42387step2Labels = labelEmbedding6 ∘ raw42387step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42387step2 raw42387step2Labels raw42387step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5206 node5206Labels := by rfl

theorem canonical42388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42388 raw42388Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw42388 raw42388Labels = mixedMoment B raw42388step0 raw42388step0Labels := by
      have hz : ∀ j, raw42388 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42388step0 = (fun i j => raw42388 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42388step0 raw42388; decide +kernel
      have hl : raw42388step0Labels = raw42388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42388 raw42388Labels permutation346 hz
    mixedMoment B raw42388step0 raw42388step0Labels = mixedMoment B raw42388step1 raw42388step1Labels := by
      have ha : raw42388step1 = raw42388step0 := by apply Matrix.ext; unfold raw42388step1 raw42388step0; decide +kernel
      have hl : raw42388step0Labels = labelEmbedding1 ∘ raw42388step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42388step0 raw42388step0Labels raw42388step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

theorem canonical42389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42389 raw42389Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw42389 raw42389Labels = mixedMoment B raw42389step0 raw42389step0Labels := by
      have hz : ∀ j, raw42389 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42389step0 = (fun i j => raw42389 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42389step0 raw42389; decide +kernel
      have hl : raw42389step0Labels = raw42389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42389 raw42389Labels permutation346 hz
    mixedMoment B raw42389step0 raw42389step0Labels = mixedMoment B raw42389step1 raw42389step1Labels := by
      have ha : raw42389step1 = (fun i j => raw42389step0 (permutation141 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42389step1 raw42389step0; decide +kernel
      have hl : raw42389step1Labels = raw42389step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42389step0 raw42389step0Labels permutation141 permutation5
    mixedMoment B raw42389step1 raw42389step1Labels = mixedMoment B raw42389step2 raw42389step2Labels := by
      have ha : raw42389step2 = raw42389step1 := by apply Matrix.ext; unfold raw42389step2 raw42389step1; decide +kernel
      have hl : raw42389step1Labels = labelEmbedding9 ∘ raw42389step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42389step1 raw42389step1Labels raw42389step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

theorem canonical42390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42390 raw42390Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw42390 raw42390Labels = mixedMoment B raw42390step0 raw42390step0Labels := by
      have hz : ∀ j, raw42390 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42390step0 = (fun i j => raw42390 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42390step0 raw42390; decide +kernel
      have hl : raw42390step0Labels = raw42390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42390 raw42390Labels permutation346 hz
    mixedMoment B raw42390step0 raw42390step0Labels = mixedMoment B raw42390step1 raw42390step1Labels := by
      have ha : raw42390step1 = (fun i j => raw42390step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42390step1 raw42390step0; decide +kernel
      have hl : raw42390step1Labels = raw42390step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42390step0 raw42390step0Labels permutation151 permutation2
    mixedMoment B raw42390step1 raw42390step1Labels = mixedMoment B raw42390step2 raw42390step2Labels := by
      have ha : raw42390step2 = -raw42390step1 := by apply Matrix.ext; change ∀ i j, raw42390step2 i j = -(raw42390step1 i j); unfold raw42390step2 raw42390step1; decide +kernel
      have hl : raw42390step2Labels = raw42390step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42390step2 raw42390step2Labels = mixedMoment B raw42390step3 raw42390step3Labels := by
      have ha : raw42390step3 = raw42390step2 := by apply Matrix.ext; unfold raw42390step3 raw42390step2; decide +kernel
      have hl : raw42390step2Labels = labelEmbedding1 ∘ raw42390step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42390step2 raw42390step2Labels raw42390step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

theorem canonical42391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42391 raw42391Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw42391 raw42391Labels = mixedMoment B raw42391step0 raw42391step0Labels := by
      have hz : ∀ j, raw42391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42391step0 = (fun i j => raw42391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42391step0 raw42391; decide +kernel
      have hl : raw42391step0Labels = raw42391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42391 raw42391Labels permutation346 hz
    mixedMoment B raw42391step0 raw42391step0Labels = mixedMoment B raw42391step1 raw42391step1Labels := by
      have ha : raw42391step1 = (fun i j => raw42391step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42391step1 raw42391step0; decide +kernel
      have hl : raw42391step1Labels = raw42391step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42391step0 raw42391step0Labels permutation139 permutation7
    mixedMoment B raw42391step1 raw42391step1Labels = mixedMoment B raw42391step2 raw42391step2Labels := by
      have ha : raw42391step2 = raw42391step1 := by apply Matrix.ext; unfold raw42391step2 raw42391step1; decide +kernel
      have hl : raw42391step1Labels = labelEmbedding6 ∘ raw42391step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42391step1 raw42391step1Labels raw42391step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

theorem canonical42392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42392 raw42392Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw42392 raw42392Labels = mixedMoment B raw42392step0 raw42392step0Labels := by
      have hz : ∀ j, raw42392 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42392step0 = (fun i j => raw42392 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42392step0 raw42392; decide +kernel
      have hl : raw42392step0Labels = raw42392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42392 raw42392Labels permutation346 hz
    mixedMoment B raw42392step0 raw42392step0Labels = mixedMoment B raw42392step1 raw42392step1Labels := by
      have ha : raw42392step1 = (fun i j => raw42392step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42392step1 raw42392step0; decide +kernel
      have hl : raw42392step1Labels = raw42392step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42392step0 raw42392step0Labels permutation151 permutation2
    mixedMoment B raw42392step1 raw42392step1Labels = mixedMoment B raw42392step2 raw42392step2Labels := by
      have ha : raw42392step2 = -raw42392step1 := by apply Matrix.ext; change ∀ i j, raw42392step2 i j = -(raw42392step1 i j); unfold raw42392step2 raw42392step1; decide +kernel
      have hl : raw42392step2Labels = raw42392step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42392step2 raw42392step2Labels = mixedMoment B raw42392step3 raw42392step3Labels := by
      have ha : raw42392step3 = raw42392step2 := by apply Matrix.ext; unfold raw42392step3 raw42392step2; decide +kernel
      have hl : raw42392step2Labels = labelEmbedding1 ∘ raw42392step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42392step2 raw42392step2Labels raw42392step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

theorem canonical42393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42393 raw42393Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw42393 raw42393Labels = mixedMoment B raw42393step0 raw42393step0Labels := by
      have hz : ∀ j, raw42393 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42393step0 = (fun i j => raw42393 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42393step0 raw42393; decide +kernel
      have hl : raw42393step0Labels = raw42393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42393 raw42393Labels permutation346 hz
    mixedMoment B raw42393step0 raw42393step0Labels = mixedMoment B raw42393step1 raw42393step1Labels := by
      have ha : raw42393step1 = (fun i j => raw42393step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42393step1 raw42393step0; decide +kernel
      have hl : raw42393step1Labels = raw42393step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42393step0 raw42393step0Labels permutation139 permutation7
    mixedMoment B raw42393step1 raw42393step1Labels = mixedMoment B raw42393step2 raw42393step2Labels := by
      have ha : raw42393step2 = raw42393step1 := by apply Matrix.ext; unfold raw42393step2 raw42393step1; decide +kernel
      have hl : raw42393step1Labels = labelEmbedding6 ∘ raw42393step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42393step1 raw42393step1Labels raw42393step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

theorem canonical42394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42394 raw42394Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw42394 raw42394Labels = mixedMoment B raw42394step0 raw42394step0Labels := by
      have hz : ∀ j, raw42394 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42394step0 = (fun i j => raw42394 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42394step0 raw42394; decide +kernel
      have hl : raw42394step0Labels = raw42394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42394 raw42394Labels permutation346 hz
    mixedMoment B raw42394step0 raw42394step0Labels = mixedMoment B raw42394step1 raw42394step1Labels := by
      have ha : raw42394step1 = (fun i j => raw42394step0 (permutation133 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42394step1 raw42394step0; decide +kernel
      have hl : raw42394step1Labels = raw42394step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42394step0 raw42394step0Labels permutation133 permutation4
    mixedMoment B raw42394step1 raw42394step1Labels = mixedMoment B raw42394step2 raw42394step2Labels := by
      have ha : raw42394step2 = raw42394step1 := by apply Matrix.ext; unfold raw42394step2 raw42394step1; decide +kernel
      have hl : raw42394step1Labels = labelEmbedding1 ∘ raw42394step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42394step1 raw42394step1Labels raw42394step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2673 node2673Labels := by rfl

theorem canonical42395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42395 raw42395Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw42395 raw42395Labels = mixedMoment B raw42395step0 raw42395step0Labels := by
      have hz : ∀ j, raw42395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42395step0 = (fun i j => raw42395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42395step0 raw42395; decide +kernel
      have hl : raw42395step0Labels = raw42395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42395 raw42395Labels permutation346 hz
    mixedMoment B raw42395step0 raw42395step0Labels = mixedMoment B raw42395step1 raw42395step1Labels := by
      have ha : raw42395step1 = (fun i j => raw42395step0 (permutation133 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42395step1 raw42395step0; decide +kernel
      have hl : raw42395step1Labels = raw42395step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42395step0 raw42395step0Labels permutation133 permutation4
    mixedMoment B raw42395step1 raw42395step1Labels = mixedMoment B raw42395step2 raw42395step2Labels := by
      have ha : raw42395step2 = raw42395step1 := by apply Matrix.ext; unfold raw42395step2 raw42395step1; decide +kernel
      have hl : raw42395step1Labels = labelEmbedding10 ∘ raw42395step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42395step1 raw42395step1Labels raw42395step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

theorem canonical42396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42396 raw42396Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw42396 raw42396Labels = mixedMoment B raw42396step0 raw42396step0Labels := by
      have hz : ∀ j, raw42396 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42396step0 = (fun i j => raw42396 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42396step0 raw42396; decide +kernel
      have hl : raw42396step0Labels = raw42396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42396 raw42396Labels permutation346 hz
    mixedMoment B raw42396step0 raw42396step0Labels = mixedMoment B raw42396step1 raw42396step1Labels := by
      have ha : raw42396step1 = (fun i j => raw42396step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42396step1 raw42396step0; decide +kernel
      have hl : raw42396step1Labels = raw42396step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42396step0 raw42396step0Labels permutation37 permutation2
    mixedMoment B raw42396step1 raw42396step1Labels = mixedMoment B raw42396step2 raw42396step2Labels := by
      have ha : raw42396step2 = raw42396step1 := by apply Matrix.ext; unfold raw42396step2 raw42396step1; decide +kernel
      have hl : raw42396step1Labels = labelEmbedding1 ∘ raw42396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42396step1 raw42396step1Labels raw42396step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

theorem canonical42397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42397 raw42397Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw42397 raw42397Labels = mixedMoment B raw42397step0 raw42397step0Labels := by
      have hz : ∀ j, raw42397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42397step0 = (fun i j => raw42397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42397step0 raw42397; decide +kernel
      have hl : raw42397step0Labels = raw42397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42397 raw42397Labels permutation346 hz
    mixedMoment B raw42397step0 raw42397step0Labels = mixedMoment B raw42397step1 raw42397step1Labels := by
      have ha : raw42397step1 = (fun i j => raw42397step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42397step1 raw42397step0; decide +kernel
      have hl : raw42397step1Labels = raw42397step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42397step0 raw42397step0Labels permutation54 permutation7
    mixedMoment B raw42397step1 raw42397step1Labels = mixedMoment B raw42397step2 raw42397step2Labels := by
      have ha : raw42397step2 = -raw42397step1 := by apply Matrix.ext; change ∀ i j, raw42397step2 i j = -(raw42397step1 i j); unfold raw42397step2 raw42397step1; decide +kernel
      have hl : raw42397step2Labels = raw42397step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42397step2 raw42397step2Labels = mixedMoment B raw42397step3 raw42397step3Labels := by
      have ha : raw42397step3 = raw42397step2 := by apply Matrix.ext; unfold raw42397step3 raw42397step2; decide +kernel
      have hl : raw42397step2Labels = labelEmbedding6 ∘ raw42397step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42397step2 raw42397step2Labels raw42397step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

theorem canonical42398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42398 raw42398Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw42398 raw42398Labels = mixedMoment B raw42398step0 raw42398step0Labels := by
      have ha : raw42398step0 = (fun i j => raw42398 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42398step0 raw42398; decide +kernel
      have hl : raw42398step0Labels = raw42398Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42398 raw42398Labels permutation682 permutation2
    mixedMoment B raw42398step0 raw42398step0Labels = mixedMoment B raw42398step1 raw42398step1Labels := by
      have ha : raw42398step1 = -raw42398step0 := by apply Matrix.ext; change ∀ i j, raw42398step1 i j = -(raw42398step0 i j); unfold raw42398step1 raw42398step0; decide +kernel
      have hl : raw42398step1Labels = raw42398step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42398step1 raw42398step1Labels = mixedMoment B raw42398step2 raw42398step2Labels := by
      have ha : raw42398step2 = raw42398step1 := by apply Matrix.ext; unfold raw42398step2 raw42398step1; decide +kernel
      have hl : raw42398step1Labels = labelEmbedding1 ∘ raw42398step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42398step1 raw42398step1Labels raw42398step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

theorem canonical42399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42399 raw42399Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw42399 raw42399Labels = mixedMoment B raw42399step0 raw42399step0Labels := by
      have ha : raw42399step0 = (fun i j => raw42399 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42399step0 raw42399; decide +kernel
      have hl : raw42399step0Labels = raw42399Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42399 raw42399Labels permutation620 permutation7
    mixedMoment B raw42399step0 raw42399step0Labels = mixedMoment B raw42399step1 raw42399step1Labels := by
      have ha : raw42399step1 = raw42399step0 := by apply Matrix.ext; unfold raw42399step1 raw42399step0; decide +kernel
      have hl : raw42399step0Labels = labelEmbedding6 ∘ raw42399step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42399step0 raw42399step0Labels raw42399step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5184 node5184Labels := by rfl

theorem canonical42400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42400 raw42400Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw42400 raw42400Labels = mixedMoment B raw42400step0 raw42400step0Labels := by
      have ha : raw42400step0 = (fun i j => raw42400 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42400step0 raw42400; decide +kernel
      have hl : raw42400step0Labels = raw42400Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42400 raw42400Labels permutation157 permutation2
    mixedMoment B raw42400step0 raw42400step0Labels = mixedMoment B raw42400step1 raw42400step1Labels := by
      have ha : raw42400step1 = raw42400step0 := by apply Matrix.ext; unfold raw42400step1 raw42400step0; decide +kernel
      have hl : raw42400step0Labels = labelEmbedding1 ∘ raw42400step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42400step0 raw42400step0Labels raw42400step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3873 node3873Labels := by rfl

theorem canonical42401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42401 raw42401Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw42401 raw42401Labels = mixedMoment B raw42401step0 raw42401step0Labels := by
      have ha : raw42401step0 = (fun i j => raw42401 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42401step0 raw42401; decide +kernel
      have hl : raw42401step0Labels = raw42401Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42401 raw42401Labels permutation195 permutation7
    mixedMoment B raw42401step0 raw42401step0Labels = mixedMoment B raw42401step1 raw42401step1Labels := by
      have ha : raw42401step1 = -raw42401step0 := by apply Matrix.ext; change ∀ i j, raw42401step1 i j = -(raw42401step0 i j); unfold raw42401step1 raw42401step0; decide +kernel
      have hl : raw42401step1Labels = raw42401step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42401step1 raw42401step1Labels = mixedMoment B raw42401step2 raw42401step2Labels := by
      have ha : raw42401step2 = raw42401step1 := by apply Matrix.ext; unfold raw42401step2 raw42401step1; decide +kernel
      have hl : raw42401step1Labels = labelEmbedding6 ∘ raw42401step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42401step1 raw42401step1Labels raw42401step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

theorem canonical42402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42402 raw42402Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw42402 raw42402Labels = mixedMoment B raw42402step0 raw42402step0Labels := by
      have ha : raw42402step0 = (fun i j => raw42402 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42402step0 raw42402; decide +kernel
      have hl : raw42402step0Labels = raw42402Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42402 raw42402Labels permutation155 permutation2
    mixedMoment B raw42402step0 raw42402step0Labels = mixedMoment B raw42402step1 raw42402step1Labels := by
      have ha : raw42402step1 = raw42402step0 := by apply Matrix.ext; unfold raw42402step1 raw42402step0; decide +kernel
      have hl : raw42402step0Labels = labelEmbedding1 ∘ raw42402step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42402step0 raw42402step0Labels raw42402step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

theorem canonical42403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42403 raw42403Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42403 raw42403Labels = mixedMoment B raw42403step0 raw42403step0Labels := by
      have ha : raw42403step0 = (fun i j => raw42403 (permutation192 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42403step0 raw42403; decide +kernel
      have hl : raw42403step0Labels = raw42403Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42403 raw42403Labels permutation192 permutation7
    mixedMoment B raw42403step0 raw42403step0Labels = mixedMoment B raw42403step1 raw42403step1Labels := by
      have ha : raw42403step1 = -raw42403step0 := by apply Matrix.ext; change ∀ i j, raw42403step1 i j = -(raw42403step0 i j); unfold raw42403step1 raw42403step0; decide +kernel
      have hl : raw42403step1Labels = raw42403step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42403step1 raw42403step1Labels = mixedMoment B raw42403step2 raw42403step2Labels := by
      have ha : raw42403step2 = raw42403step1 := by apply Matrix.ext; unfold raw42403step2 raw42403step1; decide +kernel
      have hl : raw42403step1Labels = labelEmbedding6 ∘ raw42403step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42403step1 raw42403step1Labels raw42403step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical42404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42404 raw42404Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw42404 raw42404Labels = mixedMoment B raw42404step0 raw42404step0Labels := by
      have ha : raw42404step0 = (fun i j => raw42404 (permutation418 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42404step0 raw42404; decide +kernel
      have hl : raw42404step0Labels = raw42404Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42404 raw42404Labels permutation418 permutation4
    mixedMoment B raw42404step0 raw42404step0Labels = mixedMoment B raw42404step1 raw42404step1Labels := by
      have ha : raw42404step1 = raw42404step0 := by apply Matrix.ext; unfold raw42404step1 raw42404step0; decide +kernel
      have hl : raw42404step0Labels = labelEmbedding1 ∘ raw42404step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42404step0 raw42404step0Labels raw42404step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

theorem canonical42405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42405 raw42405Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw42405 raw42405Labels = mixedMoment B raw42405step0 raw42405step0Labels := by
      have ha : raw42405step0 = (fun i j => raw42405 (permutation365 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42405step0 raw42405; decide +kernel
      have hl : raw42405step0Labels = raw42405Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42405 raw42405Labels permutation365 permutation6
    mixedMoment B raw42405step0 raw42405step0Labels = mixedMoment B raw42405step1 raw42405step1Labels := by
      have ha : raw42405step1 = -raw42405step0 := by apply Matrix.ext; change ∀ i j, raw42405step1 i j = -(raw42405step0 i j); unfold raw42405step1 raw42405step0; decide +kernel
      have hl : raw42405step1Labels = raw42405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5379 node5379Labels := by rfl

theorem canonical42406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42406 raw42406Labels = mixedMoment B node3224 node3224Labels := by
  calc
    mixedMoment B raw42406 raw42406Labels = mixedMoment B raw42406step0 raw42406step0Labels := by
      have hz : ∀ j, raw42406 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42406step0 = (fun i j => raw42406 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42406step0 raw42406; decide +kernel
      have hl : raw42406step0Labels = raw42406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42406 raw42406Labels permutation520 hz
    mixedMoment B raw42406step0 raw42406step0Labels = mixedMoment B raw42406step1 raw42406step1Labels := by
      have hz : ∀ j, raw42406step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42406step1 = (fun i j => raw42406step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42406step1 raw42406step0; decide +kernel
      have hl : raw42406step1Labels = raw42406step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42406step0 raw42406step0Labels permutation104 hz
    mixedMoment B raw42406step1 raw42406step1Labels = mixedMoment B raw42406step2 raw42406step2Labels := by
      have ha : raw42406step2 = (fun i j => raw42406step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42406step2 raw42406step1; decide +kernel
      have hl : raw42406step2Labels = raw42406step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42406step1 raw42406step1Labels permutation31 permutation2
    mixedMoment B raw42406step2 raw42406step2Labels = mixedMoment B raw42406step3 raw42406step3Labels := by
      have ha : raw42406step3 = -raw42406step2 := by apply Matrix.ext; change ∀ i j, raw42406step3 i j = -(raw42406step2 i j); unfold raw42406step3 raw42406step2; decide +kernel
      have hl : raw42406step3Labels = raw42406step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42406step3 raw42406step3Labels = mixedMoment B raw42406step4 raw42406step4Labels := by
      have ha : raw42406step4 = raw42406step3 := by apply Matrix.ext; unfold raw42406step4 raw42406step3; decide +kernel
      have hl : raw42406step3Labels = labelEmbedding1 ∘ raw42406step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42406step3 raw42406step3Labels raw42406step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3224 node3224Labels := by rfl

theorem canonical42407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42407 raw42407Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw42407 raw42407Labels = mixedMoment B raw42407step0 raw42407step0Labels := by
      have hz : ∀ j, raw42407 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42407step0 = (fun i j => raw42407 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42407step0 raw42407; decide +kernel
      have hl : raw42407step0Labels = raw42407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42407 raw42407Labels permutation520 hz
    mixedMoment B raw42407step0 raw42407step0Labels = mixedMoment B raw42407step1 raw42407step1Labels := by
      have hz : ∀ j, raw42407step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42407step1 = (fun i j => raw42407step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42407step1 raw42407step0; decide +kernel
      have hl : raw42407step1Labels = raw42407step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42407step0 raw42407step0Labels permutation104 hz
    mixedMoment B raw42407step1 raw42407step1Labels = mixedMoment B raw42407step2 raw42407step2Labels := by
      have ha : raw42407step2 = (fun i j => raw42407step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42407step2 raw42407step1; decide +kernel
      have hl : raw42407step2Labels = raw42407step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42407step1 raw42407step1Labels permutation31 permutation3
    mixedMoment B raw42407step2 raw42407step2Labels = mixedMoment B raw42407step3 raw42407step3Labels := by
      have ha : raw42407step3 = -raw42407step2 := by apply Matrix.ext; change ∀ i j, raw42407step3 i j = -(raw42407step2 i j); unfold raw42407step3 raw42407step2; decide +kernel
      have hl : raw42407step3Labels = raw42407step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42407step3 raw42407step3Labels = mixedMoment B raw42407step4 raw42407step4Labels := by
      have ha : raw42407step4 = raw42407step3 := by apply Matrix.ext; unfold raw42407step4 raw42407step3; decide +kernel
      have hl : raw42407step3Labels = labelEmbedding7 ∘ raw42407step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42407step3 raw42407step3Labels raw42407step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

theorem canonical42408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42408 raw42408Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw42408 raw42408Labels = mixedMoment B raw42408step0 raw42408step0Labels := by
      have hz : ∀ j, raw42408 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42408step0 = (fun i j => raw42408 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42408step0 raw42408; decide +kernel
      have hl : raw42408step0Labels = raw42408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42408 raw42408Labels permutation434 hz
    mixedMoment B raw42408step0 raw42408step0Labels = mixedMoment B raw42408step1 raw42408step1Labels := by
      have ha : raw42408step1 = (fun i j => raw42408step0 (permutation132 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42408step1 raw42408step0; decide +kernel
      have hl : raw42408step1Labels = raw42408step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42408step0 raw42408step0Labels permutation132 permutation4
    mixedMoment B raw42408step1 raw42408step1Labels = mixedMoment B raw42408step2 raw42408step2Labels := by
      have ha : raw42408step2 = raw42408step1 := by apply Matrix.ext; unfold raw42408step2 raw42408step1; decide +kernel
      have hl : raw42408step1Labels = labelEmbedding1 ∘ raw42408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42408step1 raw42408step1Labels raw42408step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3038 node3038Labels := by rfl

theorem canonical42409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42409 raw42409Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw42409 raw42409Labels = mixedMoment B raw42409step0 raw42409step0Labels := by
      have hz : ∀ j, raw42409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42409step0 = (fun i j => raw42409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42409step0 raw42409; decide +kernel
      have hl : raw42409step0Labels = raw42409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42409 raw42409Labels permutation434 hz
    mixedMoment B raw42409step0 raw42409step0Labels = mixedMoment B raw42409step1 raw42409step1Labels := by
      have ha : raw42409step1 = (fun i j => raw42409step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42409step1 raw42409step0; decide +kernel
      have hl : raw42409step1Labels = raw42409step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42409step0 raw42409step0Labels permutation146 permutation5
    mixedMoment B raw42409step1 raw42409step1Labels = mixedMoment B raw42409step2 raw42409step2Labels := by
      have ha : raw42409step2 = raw42409step1 := by apply Matrix.ext; unfold raw42409step2 raw42409step1; decide +kernel
      have hl : raw42409step1Labels = labelEmbedding9 ∘ raw42409step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42409step1 raw42409step1Labels raw42409step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

theorem canonical42410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42410 raw42410Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw42410 raw42410Labels = mixedMoment B raw42410step0 raw42410step0Labels := by
      have hz : ∀ j, raw42410 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42410step0 = (fun i j => raw42410 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42410step0 raw42410; decide +kernel
      have hl : raw42410step0Labels = raw42410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42410 raw42410Labels permutation434 hz
    mixedMoment B raw42410step0 raw42410step0Labels = mixedMoment B raw42410step1 raw42410step1Labels := by
      have ha : raw42410step1 = raw42410step0 := by apply Matrix.ext; unfold raw42410step1 raw42410step0; decide +kernel
      have hl : raw42410step0Labels = labelEmbedding1 ∘ raw42410step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42410step0 raw42410step0Labels raw42410step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3856 node3856Labels := by rfl

theorem canonical42411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42411 raw42411Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw42411 raw42411Labels = mixedMoment B raw42411step0 raw42411step0Labels := by
      have hz : ∀ j, raw42411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42411step0 = (fun i j => raw42411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42411step0 raw42411; decide +kernel
      have hl : raw42411step0Labels = raw42411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42411 raw42411Labels permutation434 hz
    mixedMoment B raw42411step0 raw42411step0Labels = mixedMoment B raw42411step1 raw42411step1Labels := by
      have ha : raw42411step1 = (fun i j => raw42411step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42411step1 raw42411step0; decide +kernel
      have hl : raw42411step1Labels = raw42411step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42411step0 raw42411step0Labels permutation151 permutation3
    mixedMoment B raw42411step1 raw42411step1Labels = mixedMoment B raw42411step2 raw42411step2Labels := by
      have ha : raw42411step2 = -raw42411step1 := by apply Matrix.ext; change ∀ i j, raw42411step2 i j = -(raw42411step1 i j); unfold raw42411step2 raw42411step1; decide +kernel
      have hl : raw42411step2Labels = raw42411step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42411step2 raw42411step2Labels = mixedMoment B raw42411step3 raw42411step3Labels := by
      have ha : raw42411step3 = raw42411step2 := by apply Matrix.ext; unfold raw42411step3 raw42411step2; decide +kernel
      have hl : raw42411step2Labels = labelEmbedding7 ∘ raw42411step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42411step2 raw42411step2Labels raw42411step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical42412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42412 raw42412Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw42412 raw42412Labels = mixedMoment B raw42412step0 raw42412step0Labels := by
      have hz : ∀ j, raw42412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42412step0 = (fun i j => raw42412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42412step0 raw42412; decide +kernel
      have hl : raw42412step0Labels = raw42412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42412 raw42412Labels permutation434 hz
    mixedMoment B raw42412step0 raw42412step0Labels = mixedMoment B raw42412step1 raw42412step1Labels := by
      have ha : raw42412step1 = raw42412step0 := by apply Matrix.ext; unfold raw42412step1 raw42412step0; decide +kernel
      have hl : raw42412step0Labels = labelEmbedding1 ∘ raw42412step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42412step0 raw42412step0Labels raw42412step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3854 node3854Labels := by rfl

theorem canonical42413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42413 raw42413Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw42413 raw42413Labels = mixedMoment B raw42413step0 raw42413step0Labels := by
      have hz : ∀ j, raw42413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42413step0 = (fun i j => raw42413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42413step0 raw42413; decide +kernel
      have hl : raw42413step0Labels = raw42413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42413 raw42413Labels permutation434 hz
    mixedMoment B raw42413step0 raw42413step0Labels = mixedMoment B raw42413step1 raw42413step1Labels := by
      have ha : raw42413step1 = raw42413step0 := by apply Matrix.ext; unfold raw42413step1 raw42413step0; decide +kernel
      have hl : raw42413step0Labels = labelEmbedding8 ∘ raw42413step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42413step0 raw42413step0Labels raw42413step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

theorem canonical42414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42414 raw42414Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw42414 raw42414Labels = mixedMoment B raw42414step0 raw42414step0Labels := by
      have hz : ∀ j, raw42414 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42414step0 = (fun i j => raw42414 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42414step0 raw42414; decide +kernel
      have hl : raw42414step0Labels = raw42414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42414 raw42414Labels permutation434 hz
    mixedMoment B raw42414step0 raw42414step0Labels = mixedMoment B raw42414step1 raw42414step1Labels := by
      have ha : raw42414step1 = (fun i j => raw42414step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42414step1 raw42414step0; decide +kernel
      have hl : raw42414step1Labels = raw42414step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42414step0 raw42414step0Labels permutation108 permutation4
    mixedMoment B raw42414step1 raw42414step1Labels = mixedMoment B raw42414step2 raw42414step2Labels := by
      have ha : raw42414step2 = raw42414step1 := by apply Matrix.ext; unfold raw42414step2 raw42414step1; decide +kernel
      have hl : raw42414step1Labels = labelEmbedding1 ∘ raw42414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42414step1 raw42414step1Labels raw42414step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2677 node2677Labels := by rfl

theorem canonical42415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42415 raw42415Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw42415 raw42415Labels = mixedMoment B raw42415step0 raw42415step0Labels := by
      have hz : ∀ j, raw42415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42415step0 = (fun i j => raw42415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42415step0 raw42415; decide +kernel
      have hl : raw42415step0Labels = raw42415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42415 raw42415Labels permutation434 hz
    mixedMoment B raw42415step0 raw42415step0Labels = mixedMoment B raw42415step1 raw42415step1Labels := by
      have ha : raw42415step1 = (fun i j => raw42415step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42415step1 raw42415step0; decide +kernel
      have hl : raw42415step1Labels = raw42415step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42415step0 raw42415step0Labels permutation108 permutation4
    mixedMoment B raw42415step1 raw42415step1Labels = mixedMoment B raw42415step2 raw42415step2Labels := by
      have ha : raw42415step2 = raw42415step1 := by apply Matrix.ext; unfold raw42415step2 raw42415step1; decide +kernel
      have hl : raw42415step1Labels = labelEmbedding10 ∘ raw42415step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42415step1 raw42415step1Labels raw42415step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

theorem canonical42416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42416 raw42416Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw42416 raw42416Labels = mixedMoment B raw42416step0 raw42416step0Labels := by
      have ha : raw42416step0 = (fun i j => raw42416 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42416step0 raw42416; decide +kernel
      have hl : raw42416step0Labels = raw42416Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42416 raw42416Labels permutation158 permutation2
    mixedMoment B raw42416step0 raw42416step0Labels = mixedMoment B raw42416step1 raw42416step1Labels := by
      have ha : raw42416step1 = raw42416step0 := by apply Matrix.ext; unfold raw42416step1 raw42416step0; decide +kernel
      have hl : raw42416step0Labels = labelEmbedding1 ∘ raw42416step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42416step0 raw42416step0Labels raw42416step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3841 node3841Labels := by rfl

theorem canonical42417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42417 raw42417Labels = mixedMoment B node5426 node5426Labels := by
  calc
    mixedMoment B raw42417 raw42417Labels = mixedMoment B raw42417step0 raw42417step0Labels := by
      have ha : raw42417step0 = (fun i j => raw42417 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42417step0 raw42417; decide +kernel
      have hl : raw42417step0Labels = raw42417Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42417 raw42417Labels permutation158 permutation2
    mixedMoment B raw42417step0 raw42417step0Labels = mixedMoment B raw42417step1 raw42417step1Labels := by
      have ha : raw42417step1 = raw42417step0 := by apply Matrix.ext; unfold raw42417step1 raw42417step0; decide +kernel
      have hl : raw42417step0Labels = labelEmbedding8 ∘ raw42417step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42417step0 raw42417step0Labels raw42417step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5426 node5426Labels := by rfl

theorem canonical42418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42418 raw42418Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw42418 raw42418Labels = mixedMoment B raw42418step0 raw42418step0Labels := by
      have ha : raw42418step0 = (fun i j => raw42418 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42418step0 raw42418; decide +kernel
      have hl : raw42418step0Labels = raw42418Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42418 raw42418Labels permutation158 permutation2
    mixedMoment B raw42418step0 raw42418step0Labels = mixedMoment B raw42418step1 raw42418step1Labels := by
      have ha : raw42418step1 = raw42418step0 := by apply Matrix.ext; unfold raw42418step1 raw42418step0; decide +kernel
      have hl : raw42418step0Labels = labelEmbedding1 ∘ raw42418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42418step0 raw42418step0Labels raw42418step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical42419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42419 raw42419Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42419 raw42419Labels = mixedMoment B raw42419step0 raw42419step0Labels := by
      have ha : raw42419step0 = (fun i j => raw42419 (permutation203 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42419step0 raw42419; decide +kernel
      have hl : raw42419step0Labels = raw42419Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42419 raw42419Labels permutation203 permutation7
    mixedMoment B raw42419step0 raw42419step0Labels = mixedMoment B raw42419step1 raw42419step1Labels := by
      have ha : raw42419step1 = -raw42419step0 := by apply Matrix.ext; change ∀ i j, raw42419step1 i j = -(raw42419step0 i j); unfold raw42419step1 raw42419step0; decide +kernel
      have hl : raw42419step1Labels = raw42419step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42419step1 raw42419step1Labels = mixedMoment B raw42419step2 raw42419step2Labels := by
      have ha : raw42419step2 = raw42419step1 := by apply Matrix.ext; unfold raw42419step2 raw42419step1; decide +kernel
      have hl : raw42419step1Labels = labelEmbedding6 ∘ raw42419step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42419step1 raw42419step1Labels raw42419step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical42420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42420 raw42420Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw42420 raw42420Labels = mixedMoment B raw42420step0 raw42420step0Labels := by
      have ha : raw42420step0 = (fun i j => raw42420 (permutation379 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42420step0 raw42420; decide +kernel
      have hl : raw42420step0Labels = raw42420Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42420 raw42420Labels permutation379 permutation4
    mixedMoment B raw42420step0 raw42420step0Labels = mixedMoment B raw42420step1 raw42420step1Labels := by
      have ha : raw42420step1 = -raw42420step0 := by apply Matrix.ext; change ∀ i j, raw42420step1 i j = -(raw42420step0 i j); unfold raw42420step1 raw42420step0; decide +kernel
      have hl : raw42420step1Labels = raw42420step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42420step1 raw42420step1Labels = mixedMoment B raw42420step2 raw42420step2Labels := by
      have ha : raw42420step2 = raw42420step1 := by apply Matrix.ext; unfold raw42420step2 raw42420step1; decide +kernel
      have hl : raw42420step1Labels = labelEmbedding1 ∘ raw42420step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42420step1 raw42420step1Labels raw42420step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

theorem canonical42421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42421 raw42421Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw42421 raw42421Labels = mixedMoment B raw42421step0 raw42421step0Labels := by
      have ha : raw42421step0 = (fun i j => raw42421 (permutation421 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42421step0 raw42421; decide +kernel
      have hl : raw42421step0Labels = raw42421Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42421 raw42421Labels permutation421 permutation6
    _ = mixedMoment B node5381 node5381Labels := by rfl

theorem canonical42422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42422 raw42422Labels = mixedMoment B node3833 node3833Labels := by
  calc
    mixedMoment B raw42422 raw42422Labels = mixedMoment B raw42422step0 raw42422step0Labels := by
      have ha : raw42422step0 = (fun i j => raw42422 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42422step0 raw42422; decide +kernel
      have hl : raw42422step0Labels = raw42422Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42422 raw42422Labels permutation158 permutation2
    mixedMoment B raw42422step0 raw42422step0Labels = mixedMoment B raw42422step1 raw42422step1Labels := by
      have ha : raw42422step1 = raw42422step0 := by apply Matrix.ext; unfold raw42422step1 raw42422step0; decide +kernel
      have hl : raw42422step0Labels = labelEmbedding1 ∘ raw42422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42422step0 raw42422step0Labels raw42422step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3833 node3833Labels := by rfl

theorem canonical42423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42423 raw42423Labels = mixedMoment B node5376 node5376Labels := by
  calc
    mixedMoment B raw42423 raw42423Labels = mixedMoment B raw42423step0 raw42423step0Labels := by
      have ha : raw42423step0 = (fun i j => raw42423 (permutation422 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42423step0 raw42423; decide +kernel
      have hl : raw42423step0Labels = raw42423Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42423 raw42423Labels permutation422 permutation6
    _ = mixedMoment B node5376 node5376Labels := by rfl

theorem canonical42424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42424 raw42424Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw42424 raw42424Labels = mixedMoment B raw42424step0 raw42424step0Labels := by
      have ha : raw42424step0 = (fun i j => raw42424 (permutation597 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42424step0 raw42424; decide +kernel
      have hl : raw42424step0Labels = raw42424Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42424 raw42424Labels permutation597 permutation4
    mixedMoment B raw42424step0 raw42424step0Labels = mixedMoment B raw42424step1 raw42424step1Labels := by
      have ha : raw42424step1 = raw42424step0 := by apply Matrix.ext; unfold raw42424step1 raw42424step0; decide +kernel
      have hl : raw42424step0Labels = labelEmbedding1 ∘ raw42424step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42424step0 raw42424step0Labels raw42424step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2661 node2661Labels := by rfl

theorem canonical42425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42425 raw42425Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw42425 raw42425Labels = mixedMoment B raw42425step0 raw42425step0Labels := by
      have ha : raw42425step0 = (fun i j => raw42425 (permutation597 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42425step0 raw42425; decide +kernel
      have hl : raw42425step0Labels = raw42425Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42425 raw42425Labels permutation597 permutation4
    mixedMoment B raw42425step0 raw42425step0Labels = mixedMoment B raw42425step1 raw42425step1Labels := by
      have ha : raw42425step1 = raw42425step0 := by apply Matrix.ext; unfold raw42425step1 raw42425step0; decide +kernel
      have hl : raw42425step0Labels = labelEmbedding10 ∘ raw42425step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42425step0 raw42425step0Labels raw42425step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

theorem canonical42426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42426 raw42426Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw42426 raw42426Labels = mixedMoment B raw42426step0 raw42426step0Labels := by
      have ha : raw42426step0 = (fun i j => raw42426 (permutation372 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42426step0 raw42426; decide +kernel
      have hl : raw42426step0Labels = raw42426Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42426 raw42426Labels permutation372 permutation4
    mixedMoment B raw42426step0 raw42426step0Labels = mixedMoment B raw42426step1 raw42426step1Labels := by
      have ha : raw42426step1 = -raw42426step0 := by apply Matrix.ext; change ∀ i j, raw42426step1 i j = -(raw42426step0 i j); unfold raw42426step1 raw42426step0; decide +kernel
      have hl : raw42426step1Labels = raw42426step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42426step1 raw42426step1Labels = mixedMoment B raw42426step2 raw42426step2Labels := by
      have ha : raw42426step2 = raw42426step1 := by apply Matrix.ext; unfold raw42426step2 raw42426step1; decide +kernel
      have hl : raw42426step1Labels = labelEmbedding1 ∘ raw42426step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42426step1 raw42426step1Labels raw42426step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical42427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42427 raw42427Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42427 raw42427Labels = mixedMoment B raw42427step0 raw42427step0Labels := by
      have ha : raw42427step0 = (fun i j => raw42427 (permutation387 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42427step0 raw42427; decide +kernel
      have hl : raw42427step0Labels = raw42427Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42427 raw42427Labels permutation387 permutation6
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical42428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42428 raw42428Labels = mixedMoment B node3855 node3855Labels := by
  calc
    mixedMoment B raw42428 raw42428Labels = mixedMoment B raw42428step0 raw42428step0Labels := by
      have ha : raw42428step0 = raw42428 := by apply Matrix.ext; unfold raw42428step0 raw42428; decide +kernel
      have hl : raw42428Labels = labelEmbedding1 ∘ raw42428step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42428 raw42428Labels raw42428step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3855 node3855Labels := by rfl

theorem canonical42429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42429 raw42429Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw42429 raw42429Labels = mixedMoment B raw42429step0 raw42429step0Labels := by
      have ha : raw42429step0 = raw42429 := by apply Matrix.ext; unfold raw42429step0 raw42429; decide +kernel
      have hl : raw42429Labels = labelEmbedding8 ∘ raw42429step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42429 raw42429Labels raw42429step0Labels labelEmbedding8 hl
    _ = mixedMoment B node5437 node5437Labels := by rfl

theorem canonical42430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42430 raw42430Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw42430 raw42430Labels = mixedMoment B raw42430step0 raw42430step0Labels := by
      have hz : ∀ j, raw42430 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42430step0 = (fun i j => raw42430 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42430step0 raw42430; decide +kernel
      have hl : raw42430step0Labels = raw42430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42430 raw42430Labels permutation520 hz
    mixedMoment B raw42430step0 raw42430step0Labels = mixedMoment B raw42430step1 raw42430step1Labels := by
      have ha : raw42430step1 = (fun i j => raw42430step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42430step1 raw42430step0; decide +kernel
      have hl : raw42430step1Labels = raw42430step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42430step0 raw42430step0Labels permutation128 permutation4
    mixedMoment B raw42430step1 raw42430step1Labels = mixedMoment B raw42430step2 raw42430step2Labels := by
      have ha : raw42430step2 = raw42430step1 := by apply Matrix.ext; unfold raw42430step2 raw42430step1; decide +kernel
      have hl : raw42430step1Labels = labelEmbedding1 ∘ raw42430step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42430step1 raw42430step1Labels raw42430step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

theorem canonical42431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42431 raw42431Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw42431 raw42431Labels = mixedMoment B raw42431step0 raw42431step0Labels := by
      have hz : ∀ j, raw42431 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42431step0 = (fun i j => raw42431 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42431step0 raw42431; decide +kernel
      have hl : raw42431step0Labels = raw42431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42431 raw42431Labels permutation520 hz
    mixedMoment B raw42431step0 raw42431step0Labels = mixedMoment B raw42431step1 raw42431step1Labels := by
      have ha : raw42431step1 = (fun i j => raw42431step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42431step1 raw42431step0; decide +kernel
      have hl : raw42431step1Labels = raw42431step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42431step0 raw42431step0Labels permutation145 permutation3
    mixedMoment B raw42431step1 raw42431step1Labels = mixedMoment B raw42431step2 raw42431step2Labels := by
      have ha : raw42431step2 = -raw42431step1 := by apply Matrix.ext; change ∀ i j, raw42431step2 i j = -(raw42431step1 i j); unfold raw42431step2 raw42431step1; decide +kernel
      have hl : raw42431step2Labels = raw42431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42431step2 raw42431step2Labels = mixedMoment B raw42431step3 raw42431step3Labels := by
      have ha : raw42431step3 = raw42431step2 := by apply Matrix.ext; unfold raw42431step3 raw42431step2; decide +kernel
      have hl : raw42431step2Labels = labelEmbedding7 ∘ raw42431step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42431step2 raw42431step2Labels raw42431step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2528 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2528) =
      Integer.Sparse.eval keyMomentRow2528 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2528).leftCharge (GramAssembly.key 2528).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2678) := by
    have ha : gramCharges (GramAssembly.key 2528).leftCharge (GramAssembly.key 2528).rightCharge = raw42368 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42368Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42368 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2528).leftCharge (GramAssembly.key 2528).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5233) := by
    have ha : gramCharges (GramAssembly.key 2528).leftCharge (GramAssembly.key 2528).rightCharge = raw42369 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42369Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42369 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2528).leftCharge (GramAssembly.key 2528).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2528).leftCharge (GramAssembly.key 2528).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2528, Integer.Sparse.eval]
  ring

theorem keyMoment2529 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2529) =
      Integer.Sparse.eval keyMomentRow2529 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2529).leftCharge (GramAssembly.key 2529).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3872) := by
    have ha : gramCharges (GramAssembly.key 2529).leftCharge (GramAssembly.key 2529).rightCharge = raw42370 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42370Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42370 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2529).leftCharge (GramAssembly.key 2529).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2529).leftCharge (GramAssembly.key 2529).rightCharge = raw42371 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42371Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42371 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2529).leftCharge (GramAssembly.key 2529).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2529).leftCharge (GramAssembly.key 2529).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2529, Integer.Sparse.eval]
  ring

theorem keyMoment2530 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2530) =
      Integer.Sparse.eval keyMomentRow2530 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2530).leftCharge (GramAssembly.key 2530).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3871) := by
    have ha : gramCharges (GramAssembly.key 2530).leftCharge (GramAssembly.key 2530).rightCharge = raw42372 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42372Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42372 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2530).leftCharge (GramAssembly.key 2530).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2530).leftCharge (GramAssembly.key 2530).rightCharge = raw42373 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42373Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42373 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2530).leftCharge (GramAssembly.key 2530).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2530).leftCharge (GramAssembly.key 2530).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2530, Integer.Sparse.eval]
  ring

theorem keyMoment2531 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2531) =
      Integer.Sparse.eval keyMomentRow2531 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2531).leftCharge (GramAssembly.key 2531).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3870) := by
    have ha : gramCharges (GramAssembly.key 2531).leftCharge (GramAssembly.key 2531).rightCharge = raw42374 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42374Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42374 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2531).leftCharge (GramAssembly.key 2531).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5420) := by
    have ha : gramCharges (GramAssembly.key 2531).leftCharge (GramAssembly.key 2531).rightCharge = raw42375 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42375Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42375 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2531).leftCharge (GramAssembly.key 2531).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2531).leftCharge (GramAssembly.key 2531).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2531, Integer.Sparse.eval]
  ring

theorem keyMoment2532 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2532) =
      Integer.Sparse.eval keyMomentRow2532 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2532).leftCharge (GramAssembly.key 2532).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3834) := by
    have ha : gramCharges (GramAssembly.key 2532).leftCharge (GramAssembly.key 2532).rightCharge = raw42376 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42376Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42376 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2532).leftCharge (GramAssembly.key 2532).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5381) := by
    have ha : gramCharges (GramAssembly.key 2532).leftCharge (GramAssembly.key 2532).rightCharge = raw42377 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42377Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42377 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2532).leftCharge (GramAssembly.key 2532).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2532).leftCharge (GramAssembly.key 2532).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2532, Integer.Sparse.eval]
  ring

theorem keyMoment2533 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2533) =
      Integer.Sparse.eval keyMomentRow2533 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2533).leftCharge (GramAssembly.key 2533).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2662) := by
    have ha : gramCharges (GramAssembly.key 2533).leftCharge (GramAssembly.key 2533).rightCharge = raw42378 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42378Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42378 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2533).leftCharge (GramAssembly.key 2533).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5220) := by
    have ha : gramCharges (GramAssembly.key 2533).leftCharge (GramAssembly.key 2533).rightCharge = raw42379 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42379Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42379 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2533).leftCharge (GramAssembly.key 2533).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2533).leftCharge (GramAssembly.key 2533).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2533, Integer.Sparse.eval]
  ring

theorem keyMoment2534 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2534) =
      Integer.Sparse.eval keyMomentRow2534 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2534).leftCharge (GramAssembly.key 2534).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3880) := by
    have ha : gramCharges (GramAssembly.key 2534).leftCharge (GramAssembly.key 2534).rightCharge = raw42380 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42380Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42380 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2534).leftCharge (GramAssembly.key 2534).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5445) := by
    have ha : gramCharges (GramAssembly.key 2534).leftCharge (GramAssembly.key 2534).rightCharge = raw42381 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42381Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42381 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2534).leftCharge (GramAssembly.key 2534).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2534).leftCharge (GramAssembly.key 2534).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2534, Integer.Sparse.eval]
  ring

theorem keyMoment2535 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2535) =
      Integer.Sparse.eval keyMomentRow2535 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2535).leftCharge (GramAssembly.key 2535).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3882) := by
    have ha : gramCharges (GramAssembly.key 2535).leftCharge (GramAssembly.key 2535).rightCharge = raw42382 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42382Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42382 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2535).leftCharge (GramAssembly.key 2535).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5447) := by
    have ha : gramCharges (GramAssembly.key 2535).leftCharge (GramAssembly.key 2535).rightCharge = raw42383 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42383Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42383 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2535).leftCharge (GramAssembly.key 2535).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2535).leftCharge (GramAssembly.key 2535).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2535, Integer.Sparse.eval]
  ring

theorem keyMoment2536 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2536) =
      Integer.Sparse.eval keyMomentRow2536 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2536).leftCharge (GramAssembly.key 2536).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3055) := by
    have ha : gramCharges (GramAssembly.key 2536).leftCharge (GramAssembly.key 2536).rightCharge = raw42384 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42384Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42384 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2536).leftCharge (GramAssembly.key 2536).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5300) := by
    have ha : gramCharges (GramAssembly.key 2536).leftCharge (GramAssembly.key 2536).rightCharge = raw42385 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42385Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42385 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2536).leftCharge (GramAssembly.key 2536).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2536).leftCharge (GramAssembly.key 2536).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2536, Integer.Sparse.eval]
  ring

theorem keyMoment2537 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2537) =
      Integer.Sparse.eval keyMomentRow2537 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2537).leftCharge (GramAssembly.key 2537).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2687) := by
    have ha : gramCharges (GramAssembly.key 2537).leftCharge (GramAssembly.key 2537).rightCharge = raw42386 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42386Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42386 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2537).leftCharge (GramAssembly.key 2537).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5206) := by
    have ha : gramCharges (GramAssembly.key 2537).leftCharge (GramAssembly.key 2537).rightCharge = raw42387 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42387Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42387 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2537).leftCharge (GramAssembly.key 2537).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2537).leftCharge (GramAssembly.key 2537).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2537, Integer.Sparse.eval]
  ring

theorem keyMoment2538 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2538) =
      Integer.Sparse.eval keyMomentRow2538 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2538).leftCharge (GramAssembly.key 2538).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3877) := by
    have ha : gramCharges (GramAssembly.key 2538).leftCharge (GramAssembly.key 2538).rightCharge = raw42388 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42388Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42388 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2538).leftCharge (GramAssembly.key 2538).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5436) := by
    have ha : gramCharges (GramAssembly.key 2538).leftCharge (GramAssembly.key 2538).rightCharge = raw42389 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42389Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42389 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2538).leftCharge (GramAssembly.key 2538).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2538).leftCharge (GramAssembly.key 2538).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2538, Integer.Sparse.eval]
  ring

theorem keyMoment2539 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2539) =
      Integer.Sparse.eval keyMomentRow2539 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2539).leftCharge (GramAssembly.key 2539).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3570) := by
    have ha : gramCharges (GramAssembly.key 2539).leftCharge (GramAssembly.key 2539).rightCharge = raw42390 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42390Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42390 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2539).leftCharge (GramAssembly.key 2539).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5198) := by
    have ha : gramCharges (GramAssembly.key 2539).leftCharge (GramAssembly.key 2539).rightCharge = raw42391 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42391Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42391 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2539).leftCharge (GramAssembly.key 2539).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2539).leftCharge (GramAssembly.key 2539).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2539, Integer.Sparse.eval]
  ring

theorem keyMoment2540 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2540) =
      Integer.Sparse.eval keyMomentRow2540 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2540).leftCharge (GramAssembly.key 2540).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3538) := by
    have ha : gramCharges (GramAssembly.key 2540).leftCharge (GramAssembly.key 2540).rightCharge = raw42392 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42392Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42392 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2540).leftCharge (GramAssembly.key 2540).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5188) := by
    have ha : gramCharges (GramAssembly.key 2540).leftCharge (GramAssembly.key 2540).rightCharge = raw42393 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42393Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42393 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2540).leftCharge (GramAssembly.key 2540).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2540).leftCharge (GramAssembly.key 2540).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2540, Integer.Sparse.eval]
  ring

theorem keyMoment2541 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2541) =
      Integer.Sparse.eval keyMomentRow2541 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2541).leftCharge (GramAssembly.key 2541).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2673) := by
    have ha : gramCharges (GramAssembly.key 2541).leftCharge (GramAssembly.key 2541).rightCharge = raw42394 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42394Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42394 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2541).leftCharge (GramAssembly.key 2541).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5229) := by
    have ha : gramCharges (GramAssembly.key 2541).leftCharge (GramAssembly.key 2541).rightCharge = raw42395 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42395Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42395 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2541).leftCharge (GramAssembly.key 2541).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2541).leftCharge (GramAssembly.key 2541).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2541, Integer.Sparse.eval]
  ring

theorem keyMoment2542 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2542) =
      Integer.Sparse.eval keyMomentRow2542 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2542).leftCharge (GramAssembly.key 2542).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3884) := by
    have ha : gramCharges (GramAssembly.key 2542).leftCharge (GramAssembly.key 2542).rightCharge = raw42396 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42396Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42396 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2542).leftCharge (GramAssembly.key 2542).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5446) := by
    have ha : gramCharges (GramAssembly.key 2542).leftCharge (GramAssembly.key 2542).rightCharge = raw42397 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42397Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42397 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2542).leftCharge (GramAssembly.key 2542).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2542).leftCharge (GramAssembly.key 2542).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2542, Integer.Sparse.eval]
  ring

theorem keyMoment2543 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2543) =
      Integer.Sparse.eval keyMomentRow2543 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2543).leftCharge (GramAssembly.key 2543).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3524) := by
    have ha : gramCharges (GramAssembly.key 2543).leftCharge (GramAssembly.key 2543).rightCharge = raw42398 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42398Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42398 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2543).leftCharge (GramAssembly.key 2543).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5184) := by
    have ha : gramCharges (GramAssembly.key 2543).leftCharge (GramAssembly.key 2543).rightCharge = raw42399 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42399Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42399 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2543).leftCharge (GramAssembly.key 2543).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2543).leftCharge (GramAssembly.key 2543).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2543, Integer.Sparse.eval]
  ring

theorem keyMoment2544 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2544) =
      Integer.Sparse.eval keyMomentRow2544 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2544).leftCharge (GramAssembly.key 2544).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3873) := by
    have ha : gramCharges (GramAssembly.key 2544).leftCharge (GramAssembly.key 2544).rightCharge = raw42400 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42400Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42400 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2544).leftCharge (GramAssembly.key 2544).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5421) := by
    have ha : gramCharges (GramAssembly.key 2544).leftCharge (GramAssembly.key 2544).rightCharge = raw42401 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42401Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42401 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2544).leftCharge (GramAssembly.key 2544).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2544).leftCharge (GramAssembly.key 2544).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2544, Integer.Sparse.eval]
  ring

theorem keyMoment2545 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2545) =
      Integer.Sparse.eval keyMomentRow2545 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2545).leftCharge (GramAssembly.key 2545).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3874) := by
    have ha : gramCharges (GramAssembly.key 2545).leftCharge (GramAssembly.key 2545).rightCharge = raw42402 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42402Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42402 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2545).leftCharge (GramAssembly.key 2545).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2545).leftCharge (GramAssembly.key 2545).rightCharge = raw42403 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42403Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42403 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2545).leftCharge (GramAssembly.key 2545).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2545).leftCharge (GramAssembly.key 2545).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2545, Integer.Sparse.eval]
  ring

theorem keyMoment2546 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2546) =
      Integer.Sparse.eval keyMomentRow2546 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2546).leftCharge (GramAssembly.key 2546).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3832) := by
    have ha : gramCharges (GramAssembly.key 2546).leftCharge (GramAssembly.key 2546).rightCharge = raw42404 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42404Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42404 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2546).leftCharge (GramAssembly.key 2546).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5379) := by
    have ha : gramCharges (GramAssembly.key 2546).leftCharge (GramAssembly.key 2546).rightCharge = raw42405 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42405Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42405 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2546).leftCharge (GramAssembly.key 2546).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2546).leftCharge (GramAssembly.key 2546).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2546, Integer.Sparse.eval]
  ring

theorem keyMoment2547 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2547) =
      Integer.Sparse.eval keyMomentRow2547 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2547).leftCharge (GramAssembly.key 2547).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3224) := by
    have ha : gramCharges (GramAssembly.key 2547).leftCharge (GramAssembly.key 2547).rightCharge = raw42406 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42406Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42406 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2547).leftCharge (GramAssembly.key 2547).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4898) := by
    have ha : gramCharges (GramAssembly.key 2547).leftCharge (GramAssembly.key 2547).rightCharge = raw42407 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42407Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42407 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2547).leftCharge (GramAssembly.key 2547).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2547).leftCharge (GramAssembly.key 2547).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2547, Integer.Sparse.eval]
  ring

theorem keyMoment2548 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2548) =
      Integer.Sparse.eval keyMomentRow2548 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2548).leftCharge (GramAssembly.key 2548).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3038) := by
    have ha : gramCharges (GramAssembly.key 2548).leftCharge (GramAssembly.key 2548).rightCharge = raw42408 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42408Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42408 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2548).leftCharge (GramAssembly.key 2548).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2548).leftCharge (GramAssembly.key 2548).rightCharge = raw42409 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42409Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42409 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2548).leftCharge (GramAssembly.key 2548).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2548).leftCharge (GramAssembly.key 2548).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2548, Integer.Sparse.eval]
  ring

theorem keyMoment2549 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2549) =
      Integer.Sparse.eval keyMomentRow2549 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2549).leftCharge (GramAssembly.key 2549).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3856) := by
    have ha : gramCharges (GramAssembly.key 2549).leftCharge (GramAssembly.key 2549).rightCharge = raw42410 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42410Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42410 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2549).leftCharge (GramAssembly.key 2549).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5412) := by
    have ha : gramCharges (GramAssembly.key 2549).leftCharge (GramAssembly.key 2549).rightCharge = raw42411 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42411Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42411 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2549).leftCharge (GramAssembly.key 2549).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2549).leftCharge (GramAssembly.key 2549).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2549, Integer.Sparse.eval]
  ring

theorem keyMoment2550 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2550) =
      Integer.Sparse.eval keyMomentRow2550 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2550).leftCharge (GramAssembly.key 2550).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3854) := by
    have ha : gramCharges (GramAssembly.key 2550).leftCharge (GramAssembly.key 2550).rightCharge = raw42412 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42412Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42412 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2550).leftCharge (GramAssembly.key 2550).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5436) := by
    have ha : gramCharges (GramAssembly.key 2550).leftCharge (GramAssembly.key 2550).rightCharge = raw42413 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42413Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42413 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2550).leftCharge (GramAssembly.key 2550).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2550).leftCharge (GramAssembly.key 2550).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2550, Integer.Sparse.eval]
  ring

theorem keyMoment2551 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2551) =
      Integer.Sparse.eval keyMomentRow2551 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2551).leftCharge (GramAssembly.key 2551).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2677) := by
    have ha : gramCharges (GramAssembly.key 2551).leftCharge (GramAssembly.key 2551).rightCharge = raw42414 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42414Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42414 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2551).leftCharge (GramAssembly.key 2551).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5232) := by
    have ha : gramCharges (GramAssembly.key 2551).leftCharge (GramAssembly.key 2551).rightCharge = raw42415 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42415Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42415 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2551).leftCharge (GramAssembly.key 2551).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2551).leftCharge (GramAssembly.key 2551).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2551, Integer.Sparse.eval]
  ring

theorem keyMoment2552 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2552) =
      Integer.Sparse.eval keyMomentRow2552 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2552).leftCharge (GramAssembly.key 2552).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3841) := by
    have ha : gramCharges (GramAssembly.key 2552).leftCharge (GramAssembly.key 2552).rightCharge = raw42416 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42416Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42416 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2552).leftCharge (GramAssembly.key 2552).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5426) := by
    have ha : gramCharges (GramAssembly.key 2552).leftCharge (GramAssembly.key 2552).rightCharge = raw42417 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42417Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42417 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2552).leftCharge (GramAssembly.key 2552).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2552).leftCharge (GramAssembly.key 2552).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2552, Integer.Sparse.eval]
  ring

theorem keyMoment2553 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2553) =
      Integer.Sparse.eval keyMomentRow2553 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2553).leftCharge (GramAssembly.key 2553).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3840) := by
    have ha : gramCharges (GramAssembly.key 2553).leftCharge (GramAssembly.key 2553).rightCharge = raw42418 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42418Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42418 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2553).leftCharge (GramAssembly.key 2553).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2553).leftCharge (GramAssembly.key 2553).rightCharge = raw42419 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42419Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42419 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2553).leftCharge (GramAssembly.key 2553).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2553).leftCharge (GramAssembly.key 2553).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2553, Integer.Sparse.eval]
  ring

theorem keyMoment2554 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2554) =
      Integer.Sparse.eval keyMomentRow2554 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2554).leftCharge (GramAssembly.key 2554).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3834) := by
    have ha : gramCharges (GramAssembly.key 2554).leftCharge (GramAssembly.key 2554).rightCharge = raw42420 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42420Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42420 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2554).leftCharge (GramAssembly.key 2554).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5381) := by
    have ha : gramCharges (GramAssembly.key 2554).leftCharge (GramAssembly.key 2554).rightCharge = raw42421 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42421Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42421 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2554).leftCharge (GramAssembly.key 2554).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2554).leftCharge (GramAssembly.key 2554).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2554, Integer.Sparse.eval]
  ring

theorem keyMoment2555 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2555) =
      Integer.Sparse.eval keyMomentRow2555 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2555).leftCharge (GramAssembly.key 2555).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3833) := by
    have ha : gramCharges (GramAssembly.key 2555).leftCharge (GramAssembly.key 2555).rightCharge = raw42422 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42422Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42422 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2555).leftCharge (GramAssembly.key 2555).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5376) := by
    have ha : gramCharges (GramAssembly.key 2555).leftCharge (GramAssembly.key 2555).rightCharge = raw42423 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42423Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42423 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2555).leftCharge (GramAssembly.key 2555).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2555).leftCharge (GramAssembly.key 2555).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2555, Integer.Sparse.eval]
  ring

theorem keyMoment2556 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2556) =
      Integer.Sparse.eval keyMomentRow2556 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2556).leftCharge (GramAssembly.key 2556).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2661) := by
    have ha : gramCharges (GramAssembly.key 2556).leftCharge (GramAssembly.key 2556).rightCharge = raw42424 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42424Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42424 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2556).leftCharge (GramAssembly.key 2556).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5219) := by
    have ha : gramCharges (GramAssembly.key 2556).leftCharge (GramAssembly.key 2556).rightCharge = raw42425 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42425Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42425 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2556).leftCharge (GramAssembly.key 2556).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2556).leftCharge (GramAssembly.key 2556).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2556, Integer.Sparse.eval]
  ring

theorem keyMoment2557 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2557) =
      Integer.Sparse.eval keyMomentRow2557 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2557).leftCharge (GramAssembly.key 2557).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3840) := by
    have ha : gramCharges (GramAssembly.key 2557).leftCharge (GramAssembly.key 2557).rightCharge = raw42426 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42426Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42426 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2557).leftCharge (GramAssembly.key 2557).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2557).leftCharge (GramAssembly.key 2557).rightCharge = raw42427 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42427Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42427 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2557).leftCharge (GramAssembly.key 2557).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2557).leftCharge (GramAssembly.key 2557).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2557, Integer.Sparse.eval]
  ring

theorem keyMoment2558 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2558) =
      Integer.Sparse.eval keyMomentRow2558 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2558).leftCharge (GramAssembly.key 2558).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3855) := by
    have ha : gramCharges (GramAssembly.key 2558).leftCharge (GramAssembly.key 2558).rightCharge = raw42428 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42428Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42428 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2558).leftCharge (GramAssembly.key 2558).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5437) := by
    have ha : gramCharges (GramAssembly.key 2558).leftCharge (GramAssembly.key 2558).rightCharge = raw42429 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42429Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42429 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2558).leftCharge (GramAssembly.key 2558).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2558).leftCharge (GramAssembly.key 2558).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2558, Integer.Sparse.eval]
  ring

theorem keyMoment2559 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2559) =
      Integer.Sparse.eval keyMomentRow2559 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2559).leftCharge (GramAssembly.key 2559).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3223) := by
    have ha : gramCharges (GramAssembly.key 2559).leftCharge (GramAssembly.key 2559).rightCharge = raw42430 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42430Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42430 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2559).leftCharge (GramAssembly.key 2559).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4889) := by
    have ha : gramCharges (GramAssembly.key 2559).leftCharge (GramAssembly.key 2559).rightCharge = raw42431 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42431Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42431 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2559).leftCharge (GramAssembly.key 2559).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2559).leftCharge (GramAssembly.key 2559).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2559, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2528 : keyMomentRows (2528 : Fin 2886) =
    keyMomentRow2528 := by decide +kernel

theorem keyMomentRowsAt2529 : keyMomentRows (2529 : Fin 2886) =
    keyMomentRow2529 := by decide +kernel

theorem keyMomentRowsAt2530 : keyMomentRows (2530 : Fin 2886) =
    keyMomentRow2530 := by decide +kernel

theorem keyMomentRowsAt2531 : keyMomentRows (2531 : Fin 2886) =
    keyMomentRow2531 := by decide +kernel

theorem keyMomentRowsAt2532 : keyMomentRows (2532 : Fin 2886) =
    keyMomentRow2532 := by decide +kernel

theorem keyMomentRowsAt2533 : keyMomentRows (2533 : Fin 2886) =
    keyMomentRow2533 := by decide +kernel

theorem keyMomentRowsAt2534 : keyMomentRows (2534 : Fin 2886) =
    keyMomentRow2534 := by decide +kernel

theorem keyMomentRowsAt2535 : keyMomentRows (2535 : Fin 2886) =
    keyMomentRow2535 := by decide +kernel

theorem keyMomentRowsAt2536 : keyMomentRows (2536 : Fin 2886) =
    keyMomentRow2536 := by decide +kernel

theorem keyMomentRowsAt2537 : keyMomentRows (2537 : Fin 2886) =
    keyMomentRow2537 := by decide +kernel

theorem keyMomentRowsAt2538 : keyMomentRows (2538 : Fin 2886) =
    keyMomentRow2538 := by decide +kernel

theorem keyMomentRowsAt2539 : keyMomentRows (2539 : Fin 2886) =
    keyMomentRow2539 := by decide +kernel

theorem keyMomentRowsAt2540 : keyMomentRows (2540 : Fin 2886) =
    keyMomentRow2540 := by decide +kernel

theorem keyMomentRowsAt2541 : keyMomentRows (2541 : Fin 2886) =
    keyMomentRow2541 := by decide +kernel

theorem keyMomentRowsAt2542 : keyMomentRows (2542 : Fin 2886) =
    keyMomentRow2542 := by decide +kernel

theorem keyMomentRowsAt2543 : keyMomentRows (2543 : Fin 2886) =
    keyMomentRow2543 := by decide +kernel

theorem keyMomentRowsAt2544 : keyMomentRows (2544 : Fin 2886) =
    keyMomentRow2544 := by decide +kernel

theorem keyMomentRowsAt2545 : keyMomentRows (2545 : Fin 2886) =
    keyMomentRow2545 := by decide +kernel

theorem keyMomentRowsAt2546 : keyMomentRows (2546 : Fin 2886) =
    keyMomentRow2546 := by decide +kernel

theorem keyMomentRowsAt2547 : keyMomentRows (2547 : Fin 2886) =
    keyMomentRow2547 := by decide +kernel

theorem keyMomentRowsAt2548 : keyMomentRows (2548 : Fin 2886) =
    keyMomentRow2548 := by decide +kernel

theorem keyMomentRowsAt2549 : keyMomentRows (2549 : Fin 2886) =
    keyMomentRow2549 := by decide +kernel

theorem keyMomentRowsAt2550 : keyMomentRows (2550 : Fin 2886) =
    keyMomentRow2550 := by decide +kernel

theorem keyMomentRowsAt2551 : keyMomentRows (2551 : Fin 2886) =
    keyMomentRow2551 := by decide +kernel

theorem keyMomentRowsAt2552 : keyMomentRows (2552 : Fin 2886) =
    keyMomentRow2552 := by decide +kernel

theorem keyMomentRowsAt2553 : keyMomentRows (2553 : Fin 2886) =
    keyMomentRow2553 := by decide +kernel

theorem keyMomentRowsAt2554 : keyMomentRows (2554 : Fin 2886) =
    keyMomentRow2554 := by decide +kernel

theorem keyMomentRowsAt2555 : keyMomentRows (2555 : Fin 2886) =
    keyMomentRow2555 := by decide +kernel

theorem keyMomentRowsAt2556 : keyMomentRows (2556 : Fin 2886) =
    keyMomentRow2556 := by decide +kernel

theorem keyMomentRowsAt2557 : keyMomentRows (2557 : Fin 2886) =
    keyMomentRow2557 := by decide +kernel

theorem keyMomentRowsAt2558 : keyMomentRows (2558 : Fin 2886) =
    keyMomentRow2558 := by decide +kernel

theorem keyMomentRowsAt2559 : keyMomentRows (2559 : Fin 2886) =
    keyMomentRow2559 := by decide +kernel

theorem keyMomentChunkSound79_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 79) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2528 ∨ k.val = 2529 ∨ k.val = 2530 ∨ k.val = 2531 ∨ k.val = 2532 ∨ k.val = 2533 ∨ k.val = 2534 ∨ k.val = 2535 ∨ k.val = 2536 ∨ k.val = 2537 ∨ k.val = 2538 ∨ k.val = 2539 ∨ k.val = 2540 ∨ k.val = 2541 ∨ k.val = 2542 ∨ k.val = 2543 ∨ k.val = 2544 ∨ k.val = 2545 ∨ k.val = 2546 ∨ k.val = 2547 ∨ k.val = 2548 ∨ k.val = 2549 ∨ k.val = 2550 ∨ k.val = 2551 ∨ k.val = 2552 ∨ k.val = 2553 ∨ k.val = 2554 ∨ k.val = 2555 ∨ k.val = 2556 ∨ k.val = 2557 ∨ k.val = 2558 ∨ k.val = 2559 := by omega
  rcases heq with h2528 | h2529 | h2530 | h2531 | h2532 | h2533 | h2534 | h2535 | h2536 | h2537 | h2538 | h2539 | h2540 | h2541 | h2542 | h2543 | h2544 | h2545 | h2546 | h2547 | h2548 | h2549 | h2550 | h2551 | h2552 | h2553 | h2554 | h2555 | h2556 | h2557 | h2558 | h2559
  · have he : k = (2528 : Fin 2886) := Fin.ext h2528
    subst k
    rw [keyMomentRowsAt2528]
    exact keyMoment2528 B hB
  · have he : k = (2529 : Fin 2886) := Fin.ext h2529
    subst k
    rw [keyMomentRowsAt2529]
    exact keyMoment2529 B hB
  · have he : k = (2530 : Fin 2886) := Fin.ext h2530
    subst k
    rw [keyMomentRowsAt2530]
    exact keyMoment2530 B hB
  · have he : k = (2531 : Fin 2886) := Fin.ext h2531
    subst k
    rw [keyMomentRowsAt2531]
    exact keyMoment2531 B hB
  · have he : k = (2532 : Fin 2886) := Fin.ext h2532
    subst k
    rw [keyMomentRowsAt2532]
    exact keyMoment2532 B hB
  · have he : k = (2533 : Fin 2886) := Fin.ext h2533
    subst k
    rw [keyMomentRowsAt2533]
    exact keyMoment2533 B hB
  · have he : k = (2534 : Fin 2886) := Fin.ext h2534
    subst k
    rw [keyMomentRowsAt2534]
    exact keyMoment2534 B hB
  · have he : k = (2535 : Fin 2886) := Fin.ext h2535
    subst k
    rw [keyMomentRowsAt2535]
    exact keyMoment2535 B hB
  · have he : k = (2536 : Fin 2886) := Fin.ext h2536
    subst k
    rw [keyMomentRowsAt2536]
    exact keyMoment2536 B hB
  · have he : k = (2537 : Fin 2886) := Fin.ext h2537
    subst k
    rw [keyMomentRowsAt2537]
    exact keyMoment2537 B hB
  · have he : k = (2538 : Fin 2886) := Fin.ext h2538
    subst k
    rw [keyMomentRowsAt2538]
    exact keyMoment2538 B hB
  · have he : k = (2539 : Fin 2886) := Fin.ext h2539
    subst k
    rw [keyMomentRowsAt2539]
    exact keyMoment2539 B hB
  · have he : k = (2540 : Fin 2886) := Fin.ext h2540
    subst k
    rw [keyMomentRowsAt2540]
    exact keyMoment2540 B hB
  · have he : k = (2541 : Fin 2886) := Fin.ext h2541
    subst k
    rw [keyMomentRowsAt2541]
    exact keyMoment2541 B hB
  · have he : k = (2542 : Fin 2886) := Fin.ext h2542
    subst k
    rw [keyMomentRowsAt2542]
    exact keyMoment2542 B hB
  · have he : k = (2543 : Fin 2886) := Fin.ext h2543
    subst k
    rw [keyMomentRowsAt2543]
    exact keyMoment2543 B hB
  · have he : k = (2544 : Fin 2886) := Fin.ext h2544
    subst k
    rw [keyMomentRowsAt2544]
    exact keyMoment2544 B hB
  · have he : k = (2545 : Fin 2886) := Fin.ext h2545
    subst k
    rw [keyMomentRowsAt2545]
    exact keyMoment2545 B hB
  · have he : k = (2546 : Fin 2886) := Fin.ext h2546
    subst k
    rw [keyMomentRowsAt2546]
    exact keyMoment2546 B hB
  · have he : k = (2547 : Fin 2886) := Fin.ext h2547
    subst k
    rw [keyMomentRowsAt2547]
    exact keyMoment2547 B hB
  · have he : k = (2548 : Fin 2886) := Fin.ext h2548
    subst k
    rw [keyMomentRowsAt2548]
    exact keyMoment2548 B hB
  · have he : k = (2549 : Fin 2886) := Fin.ext h2549
    subst k
    rw [keyMomentRowsAt2549]
    exact keyMoment2549 B hB
  · have he : k = (2550 : Fin 2886) := Fin.ext h2550
    subst k
    rw [keyMomentRowsAt2550]
    exact keyMoment2550 B hB
  · have he : k = (2551 : Fin 2886) := Fin.ext h2551
    subst k
    rw [keyMomentRowsAt2551]
    exact keyMoment2551 B hB
  · have he : k = (2552 : Fin 2886) := Fin.ext h2552
    subst k
    rw [keyMomentRowsAt2552]
    exact keyMoment2552 B hB
  · have he : k = (2553 : Fin 2886) := Fin.ext h2553
    subst k
    rw [keyMomentRowsAt2553]
    exact keyMoment2553 B hB
  · have he : k = (2554 : Fin 2886) := Fin.ext h2554
    subst k
    rw [keyMomentRowsAt2554]
    exact keyMoment2554 B hB
  · have he : k = (2555 : Fin 2886) := Fin.ext h2555
    subst k
    rw [keyMomentRowsAt2555]
    exact keyMoment2555 B hB
  · have he : k = (2556 : Fin 2886) := Fin.ext h2556
    subst k
    rw [keyMomentRowsAt2556]
    exact keyMoment2556 B hB
  · have he : k = (2557 : Fin 2886) := Fin.ext h2557
    subst k
    rw [keyMomentRowsAt2557]
    exact keyMoment2557 B hB
  · have he : k = (2558 : Fin 2886) := Fin.ext h2558
    subst k
    rw [keyMomentRowsAt2558]
    exact keyMoment2558 B hB
  · have he : k = (2559 : Fin 2886) := Fin.ext h2559
    subst k
    rw [keyMomentRowsAt2559]
    exact keyMoment2559 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound79_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound79_e_oai
