-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound83_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:05:00.29133+00:00
-- url     : https://prove2.me/submissions/b0a4f00b-e958-4b9e-9bca-89532fefdec5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E113
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

theorem canonical42624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42624 raw42624Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw42624 raw42624Labels = mixedMoment B raw42624step0 raw42624step0Labels := by
      have hz : ∀ j, raw42624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42624step0 = (fun i j => raw42624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42624step0 raw42624; decide +kernel
      have hl : raw42624step0Labels = raw42624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42624 raw42624Labels permutation346 hz
    mixedMoment B raw42624step0 raw42624step0Labels = mixedMoment B raw42624step1 raw42624step1Labels := by
      have ha : raw42624step1 = (fun i j => raw42624step0 (permutation133 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42624step1 raw42624step0; decide +kernel
      have hl : raw42624step1Labels = raw42624step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42624step0 raw42624step0Labels permutation133 permutation4
    mixedMoment B raw42624step1 raw42624step1Labels = mixedMoment B raw42624step2 raw42624step2Labels := by
      have ha : raw42624step2 = -raw42624step1 := by apply Matrix.ext; change ∀ i j, raw42624step2 i j = -(raw42624step1 i j); unfold raw42624step2 raw42624step1; decide +kernel
      have hl : raw42624step2Labels = raw42624step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42624step2 raw42624step2Labels = mixedMoment B raw42624step3 raw42624step3Labels := by
      have ha : raw42624step3 = raw42624step2 := by apply Matrix.ext; unfold raw42624step3 raw42624step2; decide +kernel
      have hl : raw42624step2Labels = labelEmbedding1 ∘ raw42624step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42624step2 raw42624step2Labels raw42624step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1522 node1522Labels := by rfl

theorem canonical42625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42625 raw42625Labels = mixedMoment B node4158 node4158Labels := by
  calc
    mixedMoment B raw42625 raw42625Labels = mixedMoment B raw42625step0 raw42625step0Labels := by
      have hz : ∀ j, raw42625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42625step0 = (fun i j => raw42625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42625step0 raw42625; decide +kernel
      have hl : raw42625step0Labels = raw42625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42625 raw42625Labels permutation346 hz
    mixedMoment B raw42625step0 raw42625step0Labels = mixedMoment B raw42625step1 raw42625step1Labels := by
      have ha : raw42625step1 = (fun i j => raw42625step0 (permutation150 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42625step1 raw42625step0; decide +kernel
      have hl : raw42625step1Labels = raw42625step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42625step0 raw42625step0Labels permutation150 permutation6
    _ = mixedMoment B node4158 node4158Labels := by rfl

theorem canonical42626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42626 raw42626Labels = mixedMoment B node1682 node1682Labels := by
  calc
    mixedMoment B raw42626 raw42626Labels = mixedMoment B raw42626step0 raw42626step0Labels := by
      have hz : ∀ j, raw42626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42626step0 = (fun i j => raw42626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42626step0 raw42626; decide +kernel
      have hl : raw42626step0Labels = raw42626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42626 raw42626Labels permutation346 hz
    mixedMoment B raw42626step0 raw42626step0Labels = mixedMoment B raw42626step1 raw42626step1Labels := by
      have ha : raw42626step1 = (fun i j => raw42626step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42626step1 raw42626step0; decide +kernel
      have hl : raw42626step1Labels = raw42626step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42626step0 raw42626step0Labels permutation92 permutation4
    mixedMoment B raw42626step1 raw42626step1Labels = mixedMoment B raw42626step2 raw42626step2Labels := by
      have ha : raw42626step2 = -raw42626step1 := by apply Matrix.ext; change ∀ i j, raw42626step2 i j = -(raw42626step1 i j); unfold raw42626step2 raw42626step1; decide +kernel
      have hl : raw42626step2Labels = raw42626step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42626step2 raw42626step2Labels = mixedMoment B raw42626step3 raw42626step3Labels := by
      have ha : raw42626step3 = raw42626step2 := by apply Matrix.ext; unfold raw42626step3 raw42626step2; decide +kernel
      have hl : raw42626step2Labels = labelEmbedding1 ∘ raw42626step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42626step2 raw42626step2Labels raw42626step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1682 node1682Labels := by rfl

theorem canonical42627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42627 raw42627Labels = mixedMoment B node4357 node4357Labels := by
  calc
    mixedMoment B raw42627 raw42627Labels = mixedMoment B raw42627step0 raw42627step0Labels := by
      have hz : ∀ j, raw42627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42627step0 = (fun i j => raw42627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42627step0 raw42627; decide +kernel
      have hl : raw42627step0Labels = raw42627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42627 raw42627Labels permutation346 hz
    mixedMoment B raw42627step0 raw42627step0Labels = mixedMoment B raw42627step1 raw42627step1Labels := by
      have ha : raw42627step1 = (fun i j => raw42627step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42627step1 raw42627step0; decide +kernel
      have hl : raw42627step1Labels = raw42627step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42627step0 raw42627step0Labels permutation96 permutation6
    _ = mixedMoment B node4357 node4357Labels := by rfl

theorem canonical42628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42628 raw42628Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw42628 raw42628Labels = mixedMoment B raw42628step0 raw42628step0Labels := by
      have hz : ∀ j, raw42628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42628step0 = (fun i j => raw42628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42628step0 raw42628; decide +kernel
      have hl : raw42628step0Labels = raw42628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42628 raw42628Labels permutation346 hz
    mixedMoment B raw42628step0 raw42628step0Labels = mixedMoment B raw42628step1 raw42628step1Labels := by
      have ha : raw42628step1 = (fun i j => raw42628step0 (permutation83 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42628step1 raw42628step0; decide +kernel
      have hl : raw42628step1Labels = raw42628step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42628step0 raw42628step0Labels permutation83 permutation4
    mixedMoment B raw42628step1 raw42628step1Labels = mixedMoment B raw42628step2 raw42628step2Labels := by
      have ha : raw42628step2 = -raw42628step1 := by apply Matrix.ext; change ∀ i j, raw42628step2 i j = -(raw42628step1 i j); unfold raw42628step2 raw42628step1; decide +kernel
      have hl : raw42628step2Labels = raw42628step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42628step2 raw42628step2Labels = mixedMoment B raw42628step3 raw42628step3Labels := by
      have ha : raw42628step3 = raw42628step2 := by apply Matrix.ext; unfold raw42628step3 raw42628step2; decide +kernel
      have hl : raw42628step2Labels = labelEmbedding1 ∘ raw42628step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42628step2 raw42628step2Labels raw42628step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

theorem canonical42629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42629 raw42629Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw42629 raw42629Labels = mixedMoment B raw42629step0 raw42629step0Labels := by
      have hz : ∀ j, raw42629 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42629step0 = (fun i j => raw42629 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42629step0 raw42629; decide +kernel
      have hl : raw42629step0Labels = raw42629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42629 raw42629Labels permutation346 hz
    mixedMoment B raw42629step0 raw42629step0Labels = mixedMoment B raw42629step1 raw42629step1Labels := by
      have ha : raw42629step1 = (fun i j => raw42629step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42629step1 raw42629step0; decide +kernel
      have hl : raw42629step1Labels = raw42629step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42629step0 raw42629step0Labels permutation96 permutation6
    _ = mixedMoment B node4444 node4444Labels := by rfl

theorem canonical42630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42630 raw42630Labels = mixedMoment B node3418 node3418Labels := by
  calc
    mixedMoment B raw42630 raw42630Labels = mixedMoment B raw42630step0 raw42630step0Labels := by
      have hz : ∀ j, raw42630 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42630step0 = (fun i j => raw42630 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42630step0 raw42630; decide +kernel
      have hl : raw42630step0Labels = raw42630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42630 raw42630Labels permutation346 hz
    mixedMoment B raw42630step0 raw42630step0Labels = mixedMoment B raw42630step1 raw42630step1Labels := by
      have ha : raw42630step1 = (fun i j => raw42630step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42630step1 raw42630step0; decide +kernel
      have hl : raw42630step1Labels = raw42630step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42630step0 raw42630step0Labels permutation92 permutation4
    mixedMoment B raw42630step1 raw42630step1Labels = mixedMoment B raw42630step2 raw42630step2Labels := by
      have ha : raw42630step2 = -raw42630step1 := by apply Matrix.ext; change ∀ i j, raw42630step2 i j = -(raw42630step1 i j); unfold raw42630step2 raw42630step1; decide +kernel
      have hl : raw42630step2Labels = raw42630step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42630step2 raw42630step2Labels = mixedMoment B raw42630step3 raw42630step3Labels := by
      have ha : raw42630step3 = raw42630step2 := by apply Matrix.ext; unfold raw42630step3 raw42630step2; decide +kernel
      have hl : raw42630step2Labels = labelEmbedding1 ∘ raw42630step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42630step2 raw42630step2Labels raw42630step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3418 node3418Labels := by rfl

theorem canonical42631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42631 raw42631Labels = mixedMoment B node4951 node4951Labels := by
  calc
    mixedMoment B raw42631 raw42631Labels = mixedMoment B raw42631step0 raw42631step0Labels := by
      have hz : ∀ j, raw42631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42631step0 = (fun i j => raw42631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42631step0 raw42631; decide +kernel
      have hl : raw42631step0Labels = raw42631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42631 raw42631Labels permutation346 hz
    mixedMoment B raw42631step0 raw42631step0Labels = mixedMoment B raw42631step1 raw42631step1Labels := by
      have ha : raw42631step1 = (fun i j => raw42631step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42631step1 raw42631step0; decide +kernel
      have hl : raw42631step1Labels = raw42631step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42631step0 raw42631step0Labels permutation96 permutation6
    _ = mixedMoment B node4951 node4951Labels := by rfl

theorem canonical42632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42632 raw42632Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw42632 raw42632Labels = mixedMoment B raw42632step0 raw42632step0Labels := by
      have ha : raw42632step0 = (fun i j => raw42632 (permutation488 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42632step0 raw42632; decide +kernel
      have hl : raw42632step0Labels = raw42632Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42632 raw42632Labels permutation488 permutation4
    mixedMoment B raw42632step0 raw42632step0Labels = mixedMoment B raw42632step1 raw42632step1Labels := by
      have ha : raw42632step1 = -raw42632step0 := by apply Matrix.ext; change ∀ i j, raw42632step1 i j = -(raw42632step0 i j); unfold raw42632step1 raw42632step0; decide +kernel
      have hl : raw42632step1Labels = raw42632step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42632step1 raw42632step1Labels = mixedMoment B raw42632step2 raw42632step2Labels := by
      have ha : raw42632step2 = raw42632step1 := by apply Matrix.ext; unfold raw42632step2 raw42632step1; decide +kernel
      have hl : raw42632step1Labels = labelEmbedding1 ∘ raw42632step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42632step1 raw42632step1Labels raw42632step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

theorem canonical42633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42633 raw42633Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw42633 raw42633Labels = mixedMoment B raw42633step0 raw42633step0Labels := by
      have ha : raw42633step0 = (fun i j => raw42633 (permutation503 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42633step0 raw42633; decide +kernel
      have hl : raw42633step0Labels = raw42633Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42633 raw42633Labels permutation503 permutation6
    _ = mixedMoment B node4332 node4332Labels := by rfl

theorem canonical42634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42634 raw42634Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw42634 raw42634Labels = mixedMoment B raw42634step0 raw42634step0Labels := by
      have ha : raw42634step0 = (fun i j => raw42634 (permutation488 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42634step0 raw42634; decide +kernel
      have hl : raw42634step0Labels = raw42634Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42634 raw42634Labels permutation488 permutation4
    mixedMoment B raw42634step0 raw42634step0Labels = mixedMoment B raw42634step1 raw42634step1Labels := by
      have ha : raw42634step1 = -raw42634step0 := by apply Matrix.ext; change ∀ i j, raw42634step1 i j = -(raw42634step0 i j); unfold raw42634step1 raw42634step0; decide +kernel
      have hl : raw42634step1Labels = raw42634step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42634step1 raw42634step1Labels = mixedMoment B raw42634step2 raw42634step2Labels := by
      have ha : raw42634step2 = raw42634step1 := by apply Matrix.ext; unfold raw42634step2 raw42634step1; decide +kernel
      have hl : raw42634step1Labels = labelEmbedding1 ∘ raw42634step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42634step1 raw42634step1Labels raw42634step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

theorem canonical42635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42635 raw42635Labels = mixedMoment B node4933 node4933Labels := by
  calc
    mixedMoment B raw42635 raw42635Labels = mixedMoment B raw42635step0 raw42635step0Labels := by
      have ha : raw42635step0 = (fun i j => raw42635 (permutation503 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42635step0 raw42635; decide +kernel
      have hl : raw42635step0Labels = raw42635Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42635 raw42635Labels permutation503 permutation6
    _ = mixedMoment B node4933 node4933Labels := by rfl

theorem canonical42636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42636 raw42636Labels = mixedMoment B node2155 node2155Labels := by
  calc
    mixedMoment B raw42636 raw42636Labels = mixedMoment B raw42636step0 raw42636step0Labels := by
      have hz : ∀ j, raw42636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42636step0 = (fun i j => raw42636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42636step0 raw42636; decide +kernel
      have hl : raw42636step0Labels = raw42636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42636 raw42636Labels permutation434 hz
    mixedMoment B raw42636step0 raw42636step0Labels = mixedMoment B raw42636step1 raw42636step1Labels := by
      have ha : raw42636step1 = (fun i j => raw42636step0 (permutation99 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42636step1 raw42636step0; decide +kernel
      have hl : raw42636step1Labels = raw42636step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42636step0 raw42636step0Labels permutation99 permutation4
    mixedMoment B raw42636step1 raw42636step1Labels = mixedMoment B raw42636step2 raw42636step2Labels := by
      have ha : raw42636step2 = -raw42636step1 := by apply Matrix.ext; change ∀ i j, raw42636step2 i j = -(raw42636step1 i j); unfold raw42636step2 raw42636step1; decide +kernel
      have hl : raw42636step2Labels = raw42636step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42636step2 raw42636step2Labels = mixedMoment B raw42636step3 raw42636step3Labels := by
      have ha : raw42636step3 = raw42636step2 := by apply Matrix.ext; unfold raw42636step3 raw42636step2; decide +kernel
      have hl : raw42636step2Labels = labelEmbedding1 ∘ raw42636step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42636step2 raw42636step2Labels raw42636step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2155 node2155Labels := by rfl

theorem canonical42637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42637 raw42637Labels = mixedMoment B node4669 node4669Labels := by
  calc
    mixedMoment B raw42637 raw42637Labels = mixedMoment B raw42637step0 raw42637step0Labels := by
      have hz : ∀ j, raw42637 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42637step0 = (fun i j => raw42637 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42637step0 raw42637; decide +kernel
      have hl : raw42637step0Labels = raw42637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42637 raw42637Labels permutation434 hz
    mixedMoment B raw42637step0 raw42637step0Labels = mixedMoment B raw42637step1 raw42637step1Labels := by
      have ha : raw42637step1 = (fun i j => raw42637step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42637step1 raw42637step0; decide +kernel
      have hl : raw42637step1Labels = raw42637step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42637step0 raw42637step0Labels permutation102 permutation6
    _ = mixedMoment B node4669 node4669Labels := by rfl

theorem canonical42638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42638 raw42638Labels = mixedMoment B node2176 node2176Labels := by
  calc
    mixedMoment B raw42638 raw42638Labels = mixedMoment B raw42638step0 raw42638step0Labels := by
      have ha : raw42638step0 = (fun i j => raw42638 (permutation390 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42638step0 raw42638; decide +kernel
      have hl : raw42638step0Labels = raw42638Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42638 raw42638Labels permutation390 permutation4
    mixedMoment B raw42638step0 raw42638step0Labels = mixedMoment B raw42638step1 raw42638step1Labels := by
      have ha : raw42638step1 = -raw42638step0 := by apply Matrix.ext; change ∀ i j, raw42638step1 i j = -(raw42638step0 i j); unfold raw42638step1 raw42638step0; decide +kernel
      have hl : raw42638step1Labels = raw42638step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42638step1 raw42638step1Labels = mixedMoment B raw42638step2 raw42638step2Labels := by
      have ha : raw42638step2 = raw42638step1 := by apply Matrix.ext; unfold raw42638step2 raw42638step1; decide +kernel
      have hl : raw42638step1Labels = labelEmbedding1 ∘ raw42638step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42638step1 raw42638step1Labels raw42638step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2176 node2176Labels := by rfl

theorem canonical42639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42639 raw42639Labels = mixedMoment B node4756 node4756Labels := by
  calc
    mixedMoment B raw42639 raw42639Labels = mixedMoment B raw42639step0 raw42639step0Labels := by
      have ha : raw42639step0 = (fun i j => raw42639 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42639step0 raw42639; decide +kernel
      have hl : raw42639step0Labels = raw42639Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42639 raw42639Labels permutation393 permutation6
    _ = mixedMoment B node4756 node4756Labels := by rfl

theorem canonical42640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42640 raw42640Labels = mixedMoment B node3509 node3509Labels := by
  calc
    mixedMoment B raw42640 raw42640Labels = mixedMoment B raw42640step0 raw42640step0Labels := by
      have ha : raw42640step0 = (fun i j => raw42640 (permutation325 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42640step0 raw42640; decide +kernel
      have hl : raw42640step0Labels = raw42640Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42640 raw42640Labels permutation325 permutation4
    mixedMoment B raw42640step0 raw42640step0Labels = mixedMoment B raw42640step1 raw42640step1Labels := by
      have ha : raw42640step1 = raw42640step0 := by apply Matrix.ext; unfold raw42640step1 raw42640step0; decide +kernel
      have hl : raw42640step0Labels = labelEmbedding1 ∘ raw42640step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42640step0 raw42640step0Labels raw42640step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3509 node3509Labels := by rfl

theorem canonical42641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42641 raw42641Labels = mixedMoment B node4957 node4957Labels := by
  calc
    mixedMoment B raw42641 raw42641Labels = mixedMoment B raw42641step0 raw42641step0Labels := by
      have ha : raw42641step0 = (fun i j => raw42641 (permutation280 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42641step0 raw42641; decide +kernel
      have hl : raw42641step0Labels = raw42641Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42641 raw42641Labels permutation280 permutation6
    mixedMoment B raw42641step0 raw42641step0Labels = mixedMoment B raw42641step1 raw42641step1Labels := by
      have ha : raw42641step1 = -raw42641step0 := by apply Matrix.ext; change ∀ i j, raw42641step1 i j = -(raw42641step0 i j); unfold raw42641step1 raw42641step0; decide +kernel
      have hl : raw42641step1Labels = raw42641step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4957 node4957Labels := by rfl

theorem canonical42642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42642 raw42642Labels = mixedMoment B node3512 node3512Labels := by
  calc
    mixedMoment B raw42642 raw42642Labels = mixedMoment B raw42642step0 raw42642step0Labels := by
      have hz : ∀ j, raw42642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42642step0 = (fun i j => raw42642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42642step0 raw42642; decide +kernel
      have hl : raw42642step0Labels = raw42642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42642 raw42642Labels permutation434 hz
    mixedMoment B raw42642step0 raw42642step0Labels = mixedMoment B raw42642step1 raw42642step1Labels := by
      have ha : raw42642step1 = (fun i j => raw42642step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42642step1 raw42642step0; decide +kernel
      have hl : raw42642step1Labels = raw42642step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42642step0 raw42642step0Labels permutation151 permutation2
    mixedMoment B raw42642step1 raw42642step1Labels = mixedMoment B raw42642step2 raw42642step2Labels := by
      have ha : raw42642step2 = -raw42642step1 := by apply Matrix.ext; change ∀ i j, raw42642step2 i j = -(raw42642step1 i j); unfold raw42642step2 raw42642step1; decide +kernel
      have hl : raw42642step2Labels = raw42642step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42642step2 raw42642step2Labels = mixedMoment B raw42642step3 raw42642step3Labels := by
      have ha : raw42642step3 = raw42642step2 := by apply Matrix.ext; unfold raw42642step3 raw42642step2; decide +kernel
      have hl : raw42642step2Labels = labelEmbedding1 ∘ raw42642step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42642step2 raw42642step2Labels raw42642step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3512 node3512Labels := by rfl

theorem canonical42643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42643 raw42643Labels = mixedMoment B node4959 node4959Labels := by
  calc
    mixedMoment B raw42643 raw42643Labels = mixedMoment B raw42643step0 raw42643step0Labels := by
      have hz : ∀ j, raw42643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42643step0 = (fun i j => raw42643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42643step0 raw42643; decide +kernel
      have hl : raw42643step0Labels = raw42643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42643 raw42643Labels permutation434 hz
    mixedMoment B raw42643step0 raw42643step0Labels = mixedMoment B raw42643step1 raw42643step1Labels := by
      have ha : raw42643step1 = (fun i j => raw42643step0 (permutation58 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42643step1 raw42643step0; decide +kernel
      have hl : raw42643step1Labels = raw42643step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42643step0 raw42643step0Labels permutation58 permutation6
    mixedMoment B raw42643step1 raw42643step1Labels = mixedMoment B raw42643step2 raw42643step2Labels := by
      have ha : raw42643step2 = -raw42643step1 := by apply Matrix.ext; change ∀ i j, raw42643step2 i j = -(raw42643step1 i j); unfold raw42643step2 raw42643step1; decide +kernel
      have hl : raw42643step2Labels = raw42643step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4959 node4959Labels := by rfl

theorem canonical42644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42644 raw42644Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw42644 raw42644Labels = mixedMoment B raw42644step0 raw42644step0Labels := by
      have ha : raw42644step0 = (fun i j => raw42644 (permutation338 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42644step0 raw42644; decide +kernel
      have hl : raw42644step0Labels = raw42644Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42644 raw42644Labels permutation338 permutation4
    mixedMoment B raw42644step0 raw42644step0Labels = mixedMoment B raw42644step1 raw42644step1Labels := by
      have ha : raw42644step1 = raw42644step0 := by apply Matrix.ext; unfold raw42644step1 raw42644step0; decide +kernel
      have hl : raw42644step0Labels = labelEmbedding1 ∘ raw42644step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42644step0 raw42644step0Labels raw42644step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

theorem canonical42645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42645 raw42645Labels = mixedMoment B node4955 node4955Labels := by
  calc
    mixedMoment B raw42645 raw42645Labels = mixedMoment B raw42645step0 raw42645step0Labels := by
      have ha : raw42645step0 = (fun i j => raw42645 (permutation288 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42645step0 raw42645; decide +kernel
      have hl : raw42645step0Labels = raw42645Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42645 raw42645Labels permutation288 permutation6
    mixedMoment B raw42645step0 raw42645step0Labels = mixedMoment B raw42645step1 raw42645step1Labels := by
      have ha : raw42645step1 = -raw42645step0 := by apply Matrix.ext; change ∀ i j, raw42645step1 i j = -(raw42645step0 i j); unfold raw42645step1 raw42645step0; decide +kernel
      have hl : raw42645step1Labels = raw42645step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4955 node4955Labels := by rfl

theorem canonical42646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42646 raw42646Labels = mixedMoment B node3510 node3510Labels := by
  calc
    mixedMoment B raw42646 raw42646Labels = mixedMoment B raw42646step0 raw42646step0Labels := by
      have ha : raw42646step0 = (fun i j => raw42646 (permutation322 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42646step0 raw42646; decide +kernel
      have hl : raw42646step0Labels = raw42646Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42646 raw42646Labels permutation322 permutation4
    mixedMoment B raw42646step0 raw42646step0Labels = mixedMoment B raw42646step1 raw42646step1Labels := by
      have ha : raw42646step1 = raw42646step0 := by apply Matrix.ext; unfold raw42646step1 raw42646step0; decide +kernel
      have hl : raw42646step0Labels = labelEmbedding1 ∘ raw42646step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42646step0 raw42646step0Labels raw42646step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3510 node3510Labels := by rfl

theorem canonical42647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42647 raw42647Labels = mixedMoment B node4956 node4956Labels := by
  calc
    mixedMoment B raw42647 raw42647Labels = mixedMoment B raw42647step0 raw42647step0Labels := by
      have ha : raw42647step0 = (fun i j => raw42647 (permutation277 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42647step0 raw42647; decide +kernel
      have hl : raw42647step0Labels = raw42647Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42647 raw42647Labels permutation277 permutation6
    mixedMoment B raw42647step0 raw42647step0Labels = mixedMoment B raw42647step1 raw42647step1Labels := by
      have ha : raw42647step1 = -raw42647step0 := by apply Matrix.ext; change ∀ i j, raw42647step1 i j = -(raw42647step0 i j); unfold raw42647step1 raw42647step0; decide +kernel
      have hl : raw42647step1Labels = raw42647step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4956 node4956Labels := by rfl

theorem canonical42648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42648 raw42648Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw42648 raw42648Labels = mixedMoment B raw42648step0 raw42648step0Labels := by
      have hz : ∀ j, raw42648 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42648step0 = (fun i j => raw42648 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42648step0 raw42648; decide +kernel
      have hl : raw42648step0Labels = raw42648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42648 raw42648Labels permutation434 hz
    mixedMoment B raw42648step0 raw42648step0Labels = mixedMoment B raw42648step1 raw42648step1Labels := by
      have ha : raw42648step1 = (fun i j => raw42648step0 (permutation141 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42648step1 raw42648step0; decide +kernel
      have hl : raw42648step1Labels = raw42648step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42648step0 raw42648step0Labels permutation141 permutation4
    mixedMoment B raw42648step1 raw42648step1Labels = mixedMoment B raw42648step2 raw42648step2Labels := by
      have ha : raw42648step2 = -raw42648step1 := by apply Matrix.ext; change ∀ i j, raw42648step2 i j = -(raw42648step1 i j); unfold raw42648step2 raw42648step1; decide +kernel
      have hl : raw42648step2Labels = raw42648step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42648step2 raw42648step2Labels = mixedMoment B raw42648step3 raw42648step3Labels := by
      have ha : raw42648step3 = raw42648step2 := by apply Matrix.ext; unfold raw42648step3 raw42648step2; decide +kernel
      have hl : raw42648step2Labels = labelEmbedding1 ∘ raw42648step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42648step2 raw42648step2Labels raw42648step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3268 node3268Labels := by rfl

theorem canonical42649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42649 raw42649Labels = mixedMoment B node4534 node4534Labels := by
  calc
    mixedMoment B raw42649 raw42649Labels = mixedMoment B raw42649step0 raw42649step0Labels := by
      have hz : ∀ j, raw42649 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42649step0 = (fun i j => raw42649 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42649step0 raw42649; decide +kernel
      have hl : raw42649step0Labels = raw42649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42649 raw42649Labels permutation434 hz
    mixedMoment B raw42649step0 raw42649step0Labels = mixedMoment B raw42649step1 raw42649step1Labels := by
      have ha : raw42649step1 = (fun i j => raw42649step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42649step1 raw42649step0; decide +kernel
      have hl : raw42649step1Labels = raw42649step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42649step0 raw42649step0Labels permutation144 permutation6
    _ = mixedMoment B node4534 node4534Labels := by rfl

theorem canonical42650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42650 raw42650Labels = mixedMoment B node3452 node3452Labels := by
  calc
    mixedMoment B raw42650 raw42650Labels = mixedMoment B raw42650step0 raw42650step0Labels := by
      have ha : raw42650step0 = (fun i j => raw42650 (permutation476 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42650step0 raw42650; decide +kernel
      have hl : raw42650step0Labels = raw42650Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42650 raw42650Labels permutation476 permutation4
    mixedMoment B raw42650step0 raw42650step0Labels = mixedMoment B raw42650step1 raw42650step1Labels := by
      have ha : raw42650step1 = -raw42650step0 := by apply Matrix.ext; change ∀ i j, raw42650step1 i j = -(raw42650step0 i j); unfold raw42650step1 raw42650step0; decide +kernel
      have hl : raw42650step1Labels = raw42650step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42650step1 raw42650step1Labels = mixedMoment B raw42650step2 raw42650step2Labels := by
      have ha : raw42650step2 = raw42650step1 := by apply Matrix.ext; unfold raw42650step2 raw42650step1; decide +kernel
      have hl : raw42650step1Labels = labelEmbedding1 ∘ raw42650step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42650step1 raw42650step1Labels raw42650step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3452 node3452Labels := by rfl

theorem canonical42651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42651 raw42651Labels = mixedMoment B node4954 node4954Labels := by
  calc
    mixedMoment B raw42651 raw42651Labels = mixedMoment B raw42651step0 raw42651step0Labels := by
      have ha : raw42651step0 = (fun i j => raw42651 (permutation287 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42651step0 raw42651; decide +kernel
      have hl : raw42651step0Labels = raw42651Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42651 raw42651Labels permutation287 permutation6
    mixedMoment B raw42651step0 raw42651step0Labels = mixedMoment B raw42651step1 raw42651step1Labels := by
      have ha : raw42651step1 = -raw42651step0 := by apply Matrix.ext; change ∀ i j, raw42651step1 i j = -(raw42651step0 i j); unfold raw42651step1 raw42651step0; decide +kernel
      have hl : raw42651step1Labels = raw42651step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4954 node4954Labels := by rfl

theorem canonical42652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42652 raw42652Labels = mixedMoment B node3511 node3511Labels := by
  calc
    mixedMoment B raw42652 raw42652Labels = mixedMoment B raw42652step0 raw42652step0Labels := by
      have ha : raw42652step0 = (fun i j => raw42652 (permutation333 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42652step0 raw42652; decide +kernel
      have hl : raw42652step0Labels = raw42652Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42652 raw42652Labels permutation333 permutation4
    mixedMoment B raw42652step0 raw42652step0Labels = mixedMoment B raw42652step1 raw42652step1Labels := by
      have ha : raw42652step1 = raw42652step0 := by apply Matrix.ext; unfold raw42652step1 raw42652step0; decide +kernel
      have hl : raw42652step0Labels = labelEmbedding1 ∘ raw42652step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42652step0 raw42652step0Labels raw42652step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3511 node3511Labels := by rfl

theorem canonical42653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42653 raw42653Labels = mixedMoment B node4958 node4958Labels := by
  calc
    mixedMoment B raw42653 raw42653Labels = mixedMoment B raw42653step0 raw42653step0Labels := by
      have ha : raw42653step0 = (fun i j => raw42653 (permutation283 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42653step0 raw42653; decide +kernel
      have hl : raw42653step0Labels = raw42653Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42653 raw42653Labels permutation283 permutation6
    mixedMoment B raw42653step0 raw42653step0Labels = mixedMoment B raw42653step1 raw42653step1Labels := by
      have ha : raw42653step1 = -raw42653step0 := by apply Matrix.ext; change ∀ i j, raw42653step1 i j = -(raw42653step0 i j); unfold raw42653step1 raw42653step0; decide +kernel
      have hl : raw42653step1Labels = raw42653step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4958 node4958Labels := by rfl

theorem canonical42654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42654 raw42654Labels = mixedMoment B node1523 node1523Labels := by
  calc
    mixedMoment B raw42654 raw42654Labels = mixedMoment B raw42654step0 raw42654step0Labels := by
      have hz : ∀ j, raw42654 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42654step0 = (fun i j => raw42654 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42654step0 raw42654; decide +kernel
      have hl : raw42654step0Labels = raw42654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42654 raw42654Labels permutation434 hz
    mixedMoment B raw42654step0 raw42654step0Labels = mixedMoment B raw42654step1 raw42654step1Labels := by
      have hz : ∀ j, raw42654step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42654step1 = (fun i j => raw42654step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42654step1 raw42654step0; decide +kernel
      have hl : raw42654step1Labels = raw42654step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42654step0 raw42654step0Labels permutation80 hz
    mixedMoment B raw42654step1 raw42654step1Labels = mixedMoment B raw42654step2 raw42654step2Labels := by
      have ha : raw42654step2 = (fun i j => raw42654step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42654step2 raw42654step1; decide +kernel
      have hl : raw42654step2Labels = raw42654step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42654step1 raw42654step1Labels permutation27 permutation4
    mixedMoment B raw42654step2 raw42654step2Labels = mixedMoment B raw42654step3 raw42654step3Labels := by
      have ha : raw42654step3 = -raw42654step2 := by apply Matrix.ext; change ∀ i j, raw42654step3 i j = -(raw42654step2 i j); unfold raw42654step3 raw42654step2; decide +kernel
      have hl : raw42654step3Labels = raw42654step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42654step3 raw42654step3Labels = mixedMoment B raw42654step4 raw42654step4Labels := by
      have ha : raw42654step4 = raw42654step3 := by apply Matrix.ext; unfold raw42654step4 raw42654step3; decide +kernel
      have hl : raw42654step3Labels = labelEmbedding1 ∘ raw42654step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42654step3 raw42654step3Labels raw42654step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1523 node1523Labels := by rfl

theorem canonical42655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42655 raw42655Labels = mixedMoment B node4160 node4160Labels := by
  calc
    mixedMoment B raw42655 raw42655Labels = mixedMoment B raw42655step0 raw42655step0Labels := by
      have hz : ∀ j, raw42655 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42655step0 = (fun i j => raw42655 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42655step0 raw42655; decide +kernel
      have hl : raw42655step0Labels = raw42655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42655 raw42655Labels permutation434 hz
    mixedMoment B raw42655step0 raw42655step0Labels = mixedMoment B raw42655step1 raw42655step1Labels := by
      have hz : ∀ j, raw42655step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42655step1 = (fun i j => raw42655step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42655step1 raw42655step0; decide +kernel
      have hl : raw42655step1Labels = raw42655step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42655step0 raw42655step0Labels permutation80 hz
    mixedMoment B raw42655step1 raw42655step1Labels = mixedMoment B raw42655step2 raw42655step2Labels := by
      have ha : raw42655step2 = (fun i j => raw42655step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42655step2 raw42655step1; decide +kernel
      have hl : raw42655step2Labels = raw42655step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42655step1 raw42655step1Labels permutation30 permutation6
    _ = mixedMoment B node4160 node4160Labels := by rfl

theorem canonical42656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42656 raw42656Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw42656 raw42656Labels = mixedMoment B raw42656step0 raw42656step0Labels := by
      have hz : ∀ j, raw42656 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42656step0 = (fun i j => raw42656 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42656step0 raw42656; decide +kernel
      have hl : raw42656step0Labels = raw42656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42656 raw42656Labels permutation346 hz
    mixedMoment B raw42656step0 raw42656step0Labels = mixedMoment B raw42656step1 raw42656step1Labels := by
      have ha : raw42656step1 = (fun i j => raw42656step0 (permutation93 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42656step1 raw42656step0; decide +kernel
      have hl : raw42656step1Labels = raw42656step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42656step0 raw42656step0Labels permutation93 permutation4
    mixedMoment B raw42656step1 raw42656step1Labels = mixedMoment B raw42656step2 raw42656step2Labels := by
      have ha : raw42656step2 = -raw42656step1 := by apply Matrix.ext; change ∀ i j, raw42656step2 i j = -(raw42656step1 i j); unfold raw42656step2 raw42656step1; decide +kernel
      have hl : raw42656step2Labels = raw42656step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42656step2 raw42656step2Labels = mixedMoment B raw42656step3 raw42656step3Labels := by
      have ha : raw42656step3 = raw42656step2 := by apply Matrix.ext; unfold raw42656step3 raw42656step2; decide +kernel
      have hl : raw42656step2Labels = labelEmbedding1 ∘ raw42656step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42656step2 raw42656step2Labels raw42656step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

theorem canonical42657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42657 raw42657Labels = mixedMoment B node4334 node4334Labels := by
  calc
    mixedMoment B raw42657 raw42657Labels = mixedMoment B raw42657step0 raw42657step0Labels := by
      have hz : ∀ j, raw42657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42657step0 = (fun i j => raw42657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42657step0 raw42657; decide +kernel
      have hl : raw42657step0Labels = raw42657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42657 raw42657Labels permutation346 hz
    mixedMoment B raw42657step0 raw42657step0Labels = mixedMoment B raw42657step1 raw42657step1Labels := by
      have ha : raw42657step1 = (fun i j => raw42657step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42657step1 raw42657step0; decide +kernel
      have hl : raw42657step1Labels = raw42657step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42657step0 raw42657step0Labels permutation96 permutation6
    _ = mixedMoment B node4334 node4334Labels := by rfl

theorem canonical42658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42658 raw42658Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw42658 raw42658Labels = mixedMoment B raw42658step0 raw42658step0Labels := by
      have hz : ∀ j, raw42658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42658step0 = (fun i j => raw42658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42658step0 raw42658; decide +kernel
      have hl : raw42658step0Labels = raw42658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42658 raw42658Labels permutation346 hz
    mixedMoment B raw42658step0 raw42658step0Labels = mixedMoment B raw42658step1 raw42658step1Labels := by
      have ha : raw42658step1 = (fun i j => raw42658step0 (permutation93 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42658step1 raw42658step0; decide +kernel
      have hl : raw42658step1Labels = raw42658step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42658step0 raw42658step0Labels permutation93 permutation4
    mixedMoment B raw42658step1 raw42658step1Labels = mixedMoment B raw42658step2 raw42658step2Labels := by
      have ha : raw42658step2 = -raw42658step1 := by apply Matrix.ext; change ∀ i j, raw42658step2 i j = -(raw42658step1 i j); unfold raw42658step2 raw42658step1; decide +kernel
      have hl : raw42658step2Labels = raw42658step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42658step2 raw42658step2Labels = mixedMoment B raw42658step3 raw42658step3Labels := by
      have ha : raw42658step3 = raw42658step2 := by apply Matrix.ext; unfold raw42658step3 raw42658step2; decide +kernel
      have hl : raw42658step2Labels = labelEmbedding1 ∘ raw42658step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42658step2 raw42658step2Labels raw42658step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

theorem canonical42659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42659 raw42659Labels = mixedMoment B node4934 node4934Labels := by
  calc
    mixedMoment B raw42659 raw42659Labels = mixedMoment B raw42659step0 raw42659step0Labels := by
      have hz : ∀ j, raw42659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42659step0 = (fun i j => raw42659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42659step0 raw42659; decide +kernel
      have hl : raw42659step0Labels = raw42659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42659 raw42659Labels permutation346 hz
    mixedMoment B raw42659step0 raw42659step0Labels = mixedMoment B raw42659step1 raw42659step1Labels := by
      have ha : raw42659step1 = (fun i j => raw42659step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42659step1 raw42659step0; decide +kernel
      have hl : raw42659step1Labels = raw42659step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42659step0 raw42659step0Labels permutation96 permutation6
    _ = mixedMoment B node4934 node4934Labels := by rfl

theorem canonical42660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42660 raw42660Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw42660 raw42660Labels = mixedMoment B raw42660step0 raw42660step0Labels := by
      have hz : ∀ j, raw42660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42660step0 = (fun i j => raw42660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42660step0 raw42660; decide +kernel
      have hl : raw42660step0Labels = raw42660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42660 raw42660Labels permutation434 hz
    mixedMoment B raw42660step0 raw42660step0Labels = mixedMoment B raw42660step1 raw42660step1Labels := by
      have hz : ∀ j, raw42660step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42660step1 = (fun i j => raw42660step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42660step1 raw42660step0; decide +kernel
      have hl : raw42660step1Labels = raw42660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42660step0 raw42660step0Labels permutation80 hz
    mixedMoment B raw42660step1 raw42660step1Labels = mixedMoment B raw42660step2 raw42660step2Labels := by
      have ha : raw42660step2 = (fun i j => raw42660step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42660step2 raw42660step1; decide +kernel
      have hl : raw42660step2Labels = raw42660step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42660step1 raw42660step1Labels permutation16 permutation4
    mixedMoment B raw42660step2 raw42660step2Labels = mixedMoment B raw42660step3 raw42660step3Labels := by
      have ha : raw42660step3 = -raw42660step2 := by apply Matrix.ext; change ∀ i j, raw42660step3 i j = -(raw42660step2 i j); unfold raw42660step3 raw42660step2; decide +kernel
      have hl : raw42660step3Labels = raw42660step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42660step3 raw42660step3Labels = mixedMoment B raw42660step4 raw42660step4Labels := by
      have ha : raw42660step4 = raw42660step3 := by apply Matrix.ext; unfold raw42660step4 raw42660step3; decide +kernel
      have hl : raw42660step3Labels = labelEmbedding1 ∘ raw42660step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42660step3 raw42660step3Labels raw42660step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

theorem canonical42661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42661 raw42661Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw42661 raw42661Labels = mixedMoment B raw42661step0 raw42661step0Labels := by
      have hz : ∀ j, raw42661 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42661step0 = (fun i j => raw42661 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42661step0 raw42661; decide +kernel
      have hl : raw42661step0Labels = raw42661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42661 raw42661Labels permutation434 hz
    mixedMoment B raw42661step0 raw42661step0Labels = mixedMoment B raw42661step1 raw42661step1Labels := by
      have hz : ∀ j, raw42661step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42661step1 = (fun i j => raw42661step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42661step1 raw42661step0; decide +kernel
      have hl : raw42661step1Labels = raw42661step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42661step0 raw42661step0Labels permutation80 hz
    mixedMoment B raw42661step1 raw42661step1Labels = mixedMoment B raw42661step2 raw42661step2Labels := by
      have ha : raw42661step2 = (fun i j => raw42661step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42661step2 raw42661step1; decide +kernel
      have hl : raw42661step2Labels = raw42661step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42661step1 raw42661step1Labels permutation16 permutation4
    mixedMoment B raw42661step2 raw42661step2Labels = mixedMoment B raw42661step3 raw42661step3Labels := by
      have ha : raw42661step3 = -raw42661step2 := by apply Matrix.ext; change ∀ i j, raw42661step3 i j = -(raw42661step2 i j); unfold raw42661step3 raw42661step2; decide +kernel
      have hl : raw42661step3Labels = raw42661step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42661step3 raw42661step3Labels = mixedMoment B raw42661step4 raw42661step4Labels := by
      have ha : raw42661step4 = raw42661step3 := by apply Matrix.ext; unfold raw42661step4 raw42661step3; decide +kernel
      have hl : raw42661step3Labels = labelEmbedding10 ∘ raw42661step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42661step3 raw42661step3Labels raw42661step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

theorem canonical42662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42662 raw42662Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw42662 raw42662Labels = mixedMoment B raw42662step0 raw42662step0Labels := by
      have hz : ∀ j, raw42662 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42662step0 = (fun i j => raw42662 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42662step0 raw42662; decide +kernel
      have hl : raw42662step0Labels = raw42662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42662 raw42662Labels permutation434 hz
    mixedMoment B raw42662step0 raw42662step0Labels = mixedMoment B raw42662step1 raw42662step1Labels := by
      have hz : ∀ j, raw42662step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42662step1 = (fun i j => raw42662step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42662step1 raw42662step0; decide +kernel
      have hl : raw42662step1Labels = raw42662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42662step0 raw42662step0Labels permutation80 hz
    mixedMoment B raw42662step1 raw42662step1Labels = mixedMoment B raw42662step2 raw42662step2Labels := by
      have ha : raw42662step2 = (fun i j => raw42662step1 (permutation19 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42662step2 raw42662step1; decide +kernel
      have hl : raw42662step2Labels = raw42662step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42662step1 raw42662step1Labels permutation19 permutation4
    mixedMoment B raw42662step2 raw42662step2Labels = mixedMoment B raw42662step3 raw42662step3Labels := by
      have ha : raw42662step3 = -raw42662step2 := by apply Matrix.ext; change ∀ i j, raw42662step3 i j = -(raw42662step2 i j); unfold raw42662step3 raw42662step2; decide +kernel
      have hl : raw42662step3Labels = raw42662step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42662step3 raw42662step3Labels = mixedMoment B raw42662step4 raw42662step4Labels := by
      have ha : raw42662step4 = raw42662step3 := by apply Matrix.ext; unfold raw42662step4 raw42662step3; decide +kernel
      have hl : raw42662step3Labels = labelEmbedding1 ∘ raw42662step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42662step3 raw42662step3Labels raw42662step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

theorem canonical42663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42663 raw42663Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw42663 raw42663Labels = mixedMoment B raw42663step0 raw42663step0Labels := by
      have hz : ∀ j, raw42663 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42663step0 = (fun i j => raw42663 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42663step0 raw42663; decide +kernel
      have hl : raw42663step0Labels = raw42663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42663 raw42663Labels permutation434 hz
    mixedMoment B raw42663step0 raw42663step0Labels = mixedMoment B raw42663step1 raw42663step1Labels := by
      have hz : ∀ j, raw42663step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42663step1 = (fun i j => raw42663step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42663step1 raw42663step0; decide +kernel
      have hl : raw42663step1Labels = raw42663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42663step0 raw42663step0Labels permutation80 hz
    mixedMoment B raw42663step1 raw42663step1Labels = mixedMoment B raw42663step2 raw42663step2Labels := by
      have ha : raw42663step2 = (fun i j => raw42663step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42663step2 raw42663step1; decide +kernel
      have hl : raw42663step2Labels = raw42663step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42663step1 raw42663step1Labels permutation11 permutation7
    mixedMoment B raw42663step2 raw42663step2Labels = mixedMoment B raw42663step3 raw42663step3Labels := by
      have ha : raw42663step3 = -raw42663step2 := by apply Matrix.ext; change ∀ i j, raw42663step3 i j = -(raw42663step2 i j); unfold raw42663step3 raw42663step2; decide +kernel
      have hl : raw42663step3Labels = raw42663step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42663step3 raw42663step3Labels = mixedMoment B raw42663step4 raw42663step4Labels := by
      have ha : raw42663step4 = raw42663step3 := by apply Matrix.ext; unfold raw42663step4 raw42663step3; decide +kernel
      have hl : raw42663step3Labels = labelEmbedding6 ∘ raw42663step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42663step3 raw42663step3Labels raw42663step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

theorem canonical42664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42664 raw42664Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw42664 raw42664Labels = mixedMoment B raw42664step0 raw42664step0Labels := by
      have hz : ∀ j, raw42664 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42664step0 = (fun i j => raw42664 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42664step0 raw42664; decide +kernel
      have hl : raw42664step0Labels = raw42664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42664 raw42664Labels permutation434 hz
    mixedMoment B raw42664step0 raw42664step0Labels = mixedMoment B raw42664step1 raw42664step1Labels := by
      have hz : ∀ j, raw42664step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42664step1 = (fun i j => raw42664step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42664step1 raw42664step0; decide +kernel
      have hl : raw42664step1Labels = raw42664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42664step0 raw42664step0Labels permutation80 hz
    mixedMoment B raw42664step1 raw42664step1Labels = mixedMoment B raw42664step2 raw42664step2Labels := by
      have ha : raw42664step2 = (fun i j => raw42664step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42664step2 raw42664step1; decide +kernel
      have hl : raw42664step2Labels = raw42664step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42664step1 raw42664step1Labels permutation18 permutation4
    mixedMoment B raw42664step2 raw42664step2Labels = mixedMoment B raw42664step3 raw42664step3Labels := by
      have ha : raw42664step3 = -raw42664step2 := by apply Matrix.ext; change ∀ i j, raw42664step3 i j = -(raw42664step2 i j); unfold raw42664step3 raw42664step2; decide +kernel
      have hl : raw42664step3Labels = raw42664step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42664step3 raw42664step3Labels = mixedMoment B raw42664step4 raw42664step4Labels := by
      have ha : raw42664step4 = raw42664step3 := by apply Matrix.ext; unfold raw42664step4 raw42664step3; decide +kernel
      have hl : raw42664step3Labels = labelEmbedding1 ∘ raw42664step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42664step3 raw42664step3Labels raw42664step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2687 node2687Labels := by rfl

theorem canonical42665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42665 raw42665Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw42665 raw42665Labels = mixedMoment B raw42665step0 raw42665step0Labels := by
      have hz : ∀ j, raw42665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42665step0 = (fun i j => raw42665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42665step0 raw42665; decide +kernel
      have hl : raw42665step0Labels = raw42665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42665 raw42665Labels permutation434 hz
    mixedMoment B raw42665step0 raw42665step0Labels = mixedMoment B raw42665step1 raw42665step1Labels := by
      have hz : ∀ j, raw42665step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42665step1 = (fun i j => raw42665step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42665step1 raw42665step0; decide +kernel
      have hl : raw42665step1Labels = raw42665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42665step0 raw42665step0Labels permutation80 hz
    mixedMoment B raw42665step1 raw42665step1Labels = mixedMoment B raw42665step2 raw42665step2Labels := by
      have ha : raw42665step2 = (fun i j => raw42665step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42665step2 raw42665step1; decide +kernel
      have hl : raw42665step2Labels = raw42665step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42665step1 raw42665step1Labels permutation10 permutation7
    mixedMoment B raw42665step2 raw42665step2Labels = mixedMoment B raw42665step3 raw42665step3Labels := by
      have ha : raw42665step3 = -raw42665step2 := by apply Matrix.ext; change ∀ i j, raw42665step3 i j = -(raw42665step2 i j); unfold raw42665step3 raw42665step2; decide +kernel
      have hl : raw42665step3Labels = raw42665step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42665step3 raw42665step3Labels = mixedMoment B raw42665step4 raw42665step4Labels := by
      have ha : raw42665step4 = raw42665step3 := by apply Matrix.ext; unfold raw42665step4 raw42665step3; decide +kernel
      have hl : raw42665step3Labels = labelEmbedding6 ∘ raw42665step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42665step3 raw42665step3Labels raw42665step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5206 node5206Labels := by rfl

theorem canonical42666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42666 raw42666Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw42666 raw42666Labels = mixedMoment B raw42666step0 raw42666step0Labels := by
      have hz : ∀ j, raw42666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42666step0 = (fun i j => raw42666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42666step0 raw42666; decide +kernel
      have hl : raw42666step0Labels = raw42666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42666 raw42666Labels permutation346 hz
    mixedMoment B raw42666step0 raw42666step0Labels = mixedMoment B raw42666step1 raw42666step1Labels := by
      have ha : raw42666step1 = (fun i j => raw42666step0 (permutation79 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42666step1 raw42666step0; decide +kernel
      have hl : raw42666step1Labels = raw42666step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42666step0 raw42666step0Labels permutation79 permutation4
    mixedMoment B raw42666step1 raw42666step1Labels = mixedMoment B raw42666step2 raw42666step2Labels := by
      have ha : raw42666step2 = -raw42666step1 := by apply Matrix.ext; change ∀ i j, raw42666step2 i j = -(raw42666step1 i j); unfold raw42666step2 raw42666step1; decide +kernel
      have hl : raw42666step2Labels = raw42666step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42666step2 raw42666step2Labels = mixedMoment B raw42666step3 raw42666step3Labels := by
      have ha : raw42666step3 = raw42666step2 := by apply Matrix.ext; unfold raw42666step3 raw42666step2; decide +kernel
      have hl : raw42666step2Labels = labelEmbedding1 ∘ raw42666step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42666step2 raw42666step2Labels raw42666step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

theorem canonical42667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42667 raw42667Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw42667 raw42667Labels = mixedMoment B raw42667step0 raw42667step0Labels := by
      have hz : ∀ j, raw42667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42667step0 = (fun i j => raw42667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42667step0 raw42667; decide +kernel
      have hl : raw42667step0Labels = raw42667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42667 raw42667Labels permutation346 hz
    mixedMoment B raw42667step0 raw42667step0Labels = mixedMoment B raw42667step1 raw42667step1Labels := by
      have ha : raw42667step1 = (fun i j => raw42667step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42667step1 raw42667step0; decide +kernel
      have hl : raw42667step1Labels = raw42667step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42667step0 raw42667step0Labels permutation40 permutation7
    mixedMoment B raw42667step1 raw42667step1Labels = mixedMoment B raw42667step2 raw42667step2Labels := by
      have ha : raw42667step2 = -raw42667step1 := by apply Matrix.ext; change ∀ i j, raw42667step2 i j = -(raw42667step1 i j); unfold raw42667step2 raw42667step1; decide +kernel
      have hl : raw42667step2Labels = raw42667step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42667step2 raw42667step2Labels = mixedMoment B raw42667step3 raw42667step3Labels := by
      have ha : raw42667step3 = raw42667step2 := by apply Matrix.ext; unfold raw42667step3 raw42667step2; decide +kernel
      have hl : raw42667step2Labels = labelEmbedding6 ∘ raw42667step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42667step2 raw42667step2Labels raw42667step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

theorem canonical42668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42668 raw42668Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw42668 raw42668Labels = mixedMoment B raw42668step0 raw42668step0Labels := by
      have hz : ∀ j, raw42668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42668step0 = (fun i j => raw42668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42668step0 raw42668; decide +kernel
      have hl : raw42668step0Labels = raw42668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42668 raw42668Labels permutation346 hz
    mixedMoment B raw42668step0 raw42668step0Labels = mixedMoment B raw42668step1 raw42668step1Labels := by
      have ha : raw42668step1 = (fun i j => raw42668step0 (permutation64 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42668step1 raw42668step0; decide +kernel
      have hl : raw42668step1Labels = raw42668step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42668step0 raw42668step0Labels permutation64 permutation4
    mixedMoment B raw42668step1 raw42668step1Labels = mixedMoment B raw42668step2 raw42668step2Labels := by
      have ha : raw42668step2 = -raw42668step1 := by apply Matrix.ext; change ∀ i j, raw42668step2 i j = -(raw42668step1 i j); unfold raw42668step2 raw42668step1; decide +kernel
      have hl : raw42668step2Labels = raw42668step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42668step2 raw42668step2Labels = mixedMoment B raw42668step3 raw42668step3Labels := by
      have ha : raw42668step3 = raw42668step2 := by apply Matrix.ext; unfold raw42668step3 raw42668step2; decide +kernel
      have hl : raw42668step2Labels = labelEmbedding1 ∘ raw42668step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42668step2 raw42668step2Labels raw42668step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2706 node2706Labels := by rfl

theorem canonical42669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42669 raw42669Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw42669 raw42669Labels = mixedMoment B raw42669step0 raw42669step0Labels := by
      have hz : ∀ j, raw42669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42669step0 = (fun i j => raw42669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42669step0 raw42669; decide +kernel
      have hl : raw42669step0Labels = raw42669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42669 raw42669Labels permutation346 hz
    mixedMoment B raw42669step0 raw42669step0Labels = mixedMoment B raw42669step1 raw42669step1Labels := by
      have ha : raw42669step1 = (fun i j => raw42669step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42669step1 raw42669step0; decide +kernel
      have hl : raw42669step1Labels = raw42669step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42669step0 raw42669step0Labels permutation53 permutation7
    mixedMoment B raw42669step1 raw42669step1Labels = mixedMoment B raw42669step2 raw42669step2Labels := by
      have ha : raw42669step2 = -raw42669step1 := by apply Matrix.ext; change ∀ i j, raw42669step2 i j = -(raw42669step1 i j); unfold raw42669step2 raw42669step1; decide +kernel
      have hl : raw42669step2Labels = raw42669step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42669step2 raw42669step2Labels = mixedMoment B raw42669step3 raw42669step3Labels := by
      have ha : raw42669step3 = raw42669step2 := by apply Matrix.ext; unfold raw42669step3 raw42669step2; decide +kernel
      have hl : raw42669step2Labels = labelEmbedding6 ∘ raw42669step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42669step2 raw42669step2Labels raw42669step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5205 node5205Labels := by rfl

theorem canonical42670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42670 raw42670Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw42670 raw42670Labels = mixedMoment B raw42670step0 raw42670step0Labels := by
      have hz : ∀ j, raw42670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42670step0 = (fun i j => raw42670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42670step0 raw42670; decide +kernel
      have hl : raw42670step0Labels = raw42670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42670 raw42670Labels permutation346 hz
    mixedMoment B raw42670step0 raw42670step0Labels = mixedMoment B raw42670step1 raw42670step1Labels := by
      have ha : raw42670step1 = (fun i j => raw42670step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42670step1 raw42670step0; decide +kernel
      have hl : raw42670step1Labels = raw42670step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42670step0 raw42670step0Labels permutation65 permutation4
    mixedMoment B raw42670step1 raw42670step1Labels = mixedMoment B raw42670step2 raw42670step2Labels := by
      have ha : raw42670step2 = -raw42670step1 := by apply Matrix.ext; change ∀ i j, raw42670step2 i j = -(raw42670step1 i j); unfold raw42670step2 raw42670step1; decide +kernel
      have hl : raw42670step2Labels = raw42670step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42670step2 raw42670step2Labels = mixedMoment B raw42670step3 raw42670step3Labels := by
      have ha : raw42670step3 = raw42670step2 := by apply Matrix.ext; unfold raw42670step3 raw42670step2; decide +kernel
      have hl : raw42670step2Labels = labelEmbedding1 ∘ raw42670step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42670step2 raw42670step2Labels raw42670step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

theorem canonical42671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42671 raw42671Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw42671 raw42671Labels = mixedMoment B raw42671step0 raw42671step0Labels := by
      have hz : ∀ j, raw42671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42671step0 = (fun i j => raw42671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42671step0 raw42671; decide +kernel
      have hl : raw42671step0Labels = raw42671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42671 raw42671Labels permutation346 hz
    mixedMoment B raw42671step0 raw42671step0Labels = mixedMoment B raw42671step1 raw42671step1Labels := by
      have ha : raw42671step1 = (fun i j => raw42671step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42671step1 raw42671step0; decide +kernel
      have hl : raw42671step1Labels = raw42671step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42671step0 raw42671step0Labels permutation65 permutation4
    mixedMoment B raw42671step1 raw42671step1Labels = mixedMoment B raw42671step2 raw42671step2Labels := by
      have ha : raw42671step2 = -raw42671step1 := by apply Matrix.ext; change ∀ i j, raw42671step2 i j = -(raw42671step1 i j); unfold raw42671step2 raw42671step1; decide +kernel
      have hl : raw42671step2Labels = raw42671step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42671step2 raw42671step2Labels = mixedMoment B raw42671step3 raw42671step3Labels := by
      have ha : raw42671step3 = raw42671step2 := by apply Matrix.ext; unfold raw42671step3 raw42671step2; decide +kernel
      have hl : raw42671step2Labels = labelEmbedding10 ∘ raw42671step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42671step2 raw42671step2Labels raw42671step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

theorem canonical42672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42672 raw42672Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw42672 raw42672Labels = mixedMoment B raw42672step0 raw42672step0Labels := by
      have ha : raw42672step0 = (fun i j => raw42672 (permutation317 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42672step0 raw42672; decide +kernel
      have hl : raw42672step0Labels = raw42672Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42672 raw42672Labels permutation317 permutation4
    mixedMoment B raw42672step0 raw42672step0Labels = mixedMoment B raw42672step1 raw42672step1Labels := by
      have ha : raw42672step1 = -raw42672step0 := by apply Matrix.ext; change ∀ i j, raw42672step1 i j = -(raw42672step0 i j); unfold raw42672step1 raw42672step0; decide +kernel
      have hl : raw42672step1Labels = raw42672step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42672step1 raw42672step1Labels = mixedMoment B raw42672step2 raw42672step2Labels := by
      have ha : raw42672step2 = raw42672step1 := by apply Matrix.ext; unfold raw42672step2 raw42672step1; decide +kernel
      have hl : raw42672step1Labels = labelEmbedding1 ∘ raw42672step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42672step1 raw42672step1Labels raw42672step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2700 node2700Labels := by rfl

theorem canonical42673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42673 raw42673Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw42673 raw42673Labels = mixedMoment B raw42673step0 raw42673step0Labels := by
      have ha : raw42673step0 = (fun i j => raw42673 (permutation197 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42673step0 raw42673; decide +kernel
      have hl : raw42673step0Labels = raw42673Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42673 raw42673Labels permutation197 permutation7
    mixedMoment B raw42673step0 raw42673step0Labels = mixedMoment B raw42673step1 raw42673step1Labels := by
      have ha : raw42673step1 = -raw42673step0 := by apply Matrix.ext; change ∀ i j, raw42673step1 i j = -(raw42673step0 i j); unfold raw42673step1 raw42673step0; decide +kernel
      have hl : raw42673step1Labels = raw42673step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42673step1 raw42673step1Labels = mixedMoment B raw42673step2 raw42673step2Labels := by
      have ha : raw42673step2 = raw42673step1 := by apply Matrix.ext; unfold raw42673step2 raw42673step1; decide +kernel
      have hl : raw42673step1Labels = labelEmbedding6 ∘ raw42673step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42673step1 raw42673step1Labels raw42673step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5150 node5150Labels := by rfl

theorem canonical42674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42674 raw42674Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw42674 raw42674Labels = mixedMoment B raw42674step0 raw42674step0Labels := by
      have hz : ∀ j, raw42674 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42674step0 = (fun i j => raw42674 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42674step0 raw42674; decide +kernel
      have hl : raw42674step0Labels = raw42674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42674 raw42674Labels permutation434 hz
    mixedMoment B raw42674step0 raw42674step0Labels = mixedMoment B raw42674step1 raw42674step1Labels := by
      have ha : raw42674step1 = raw42674step0 := by apply Matrix.ext; unfold raw42674step1 raw42674step0; decide +kernel
      have hl : raw42674step0Labels = labelEmbedding1 ∘ raw42674step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42674step0 raw42674step0Labels raw42674step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical42675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42675 raw42675Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw42675 raw42675Labels = mixedMoment B raw42675step0 raw42675step0Labels := by
      have hz : ∀ j, raw42675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42675step0 = (fun i j => raw42675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42675step0 raw42675; decide +kernel
      have hl : raw42675step0Labels = raw42675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42675 raw42675Labels permutation434 hz
    mixedMoment B raw42675step0 raw42675step0Labels = mixedMoment B raw42675step1 raw42675step1Labels := by
      have ha : raw42675step1 = (fun i j => raw42675step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42675step1 raw42675step0; decide +kernel
      have hl : raw42675step1Labels = raw42675step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42675step0 raw42675step0Labels permutation50 permutation7
    mixedMoment B raw42675step1 raw42675step1Labels = mixedMoment B raw42675step2 raw42675step2Labels := by
      have ha : raw42675step2 = -raw42675step1 := by apply Matrix.ext; change ∀ i j, raw42675step2 i j = -(raw42675step1 i j); unfold raw42675step2 raw42675step1; decide +kernel
      have hl : raw42675step2Labels = raw42675step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42675step2 raw42675step2Labels = mixedMoment B raw42675step3 raw42675step3Labels := by
      have ha : raw42675step3 = raw42675step2 := by apply Matrix.ext; unfold raw42675step3 raw42675step2; decide +kernel
      have hl : raw42675step2Labels = labelEmbedding6 ∘ raw42675step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42675step2 raw42675step2Labels raw42675step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical42676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42676 raw42676Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw42676 raw42676Labels = mixedMoment B raw42676step0 raw42676step0Labels := by
      have hz : ∀ j, raw42676 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42676step0 = (fun i j => raw42676 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42676step0 raw42676; decide +kernel
      have hl : raw42676step0Labels = raw42676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42676 raw42676Labels permutation434 hz
    mixedMoment B raw42676step0 raw42676step0Labels = mixedMoment B raw42676step1 raw42676step1Labels := by
      have ha : raw42676step1 = raw42676step0 := by apply Matrix.ext; unfold raw42676step1 raw42676step0; decide +kernel
      have hl : raw42676step0Labels = labelEmbedding1 ∘ raw42676step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42676step0 raw42676step0Labels raw42676step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical42677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42677 raw42677Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw42677 raw42677Labels = mixedMoment B raw42677step0 raw42677step0Labels := by
      have hz : ∀ j, raw42677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42677step0 = (fun i j => raw42677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42677step0 raw42677; decide +kernel
      have hl : raw42677step0Labels = raw42677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42677 raw42677Labels permutation434 hz
    mixedMoment B raw42677step0 raw42677step0Labels = mixedMoment B raw42677step1 raw42677step1Labels := by
      have ha : raw42677step1 = (fun i j => raw42677step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42677step1 raw42677step0; decide +kernel
      have hl : raw42677step1Labels = raw42677step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42677step0 raw42677step0Labels permutation44 permutation7
    mixedMoment B raw42677step1 raw42677step1Labels = mixedMoment B raw42677step2 raw42677step2Labels := by
      have ha : raw42677step2 = -raw42677step1 := by apply Matrix.ext; change ∀ i j, raw42677step2 i j = -(raw42677step1 i j); unfold raw42677step2 raw42677step1; decide +kernel
      have hl : raw42677step2Labels = raw42677step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42677step2 raw42677step2Labels = mixedMoment B raw42677step3 raw42677step3Labels := by
      have ha : raw42677step3 = raw42677step2 := by apply Matrix.ext; unfold raw42677step3 raw42677step2; decide +kernel
      have hl : raw42677step2Labels = labelEmbedding6 ∘ raw42677step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42677step2 raw42677step2Labels raw42677step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical42678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42678 raw42678Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw42678 raw42678Labels = mixedMoment B raw42678step0 raw42678step0Labels := by
      have hz : ∀ j, raw42678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42678step0 = (fun i j => raw42678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42678step0 raw42678; decide +kernel
      have hl : raw42678step0Labels = raw42678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42678 raw42678Labels permutation434 hz
    mixedMoment B raw42678step0 raw42678step0Labels = mixedMoment B raw42678step1 raw42678step1Labels := by
      have ha : raw42678step1 = raw42678step0 := by apply Matrix.ext; unfold raw42678step1 raw42678step0; decide +kernel
      have hl : raw42678step0Labels = labelEmbedding1 ∘ raw42678step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42678step0 raw42678step0Labels raw42678step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

theorem canonical42679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42679 raw42679Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw42679 raw42679Labels = mixedMoment B raw42679step0 raw42679step0Labels := by
      have hz : ∀ j, raw42679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42679step0 = (fun i j => raw42679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42679step0 raw42679; decide +kernel
      have hl : raw42679step0Labels = raw42679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42679 raw42679Labels permutation434 hz
    mixedMoment B raw42679step0 raw42679step0Labels = mixedMoment B raw42679step1 raw42679step1Labels := by
      have ha : raw42679step1 = (fun i j => raw42679step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42679step1 raw42679step0; decide +kernel
      have hl : raw42679step1Labels = raw42679step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42679step0 raw42679step0Labels permutation44 permutation7
    mixedMoment B raw42679step1 raw42679step1Labels = mixedMoment B raw42679step2 raw42679step2Labels := by
      have ha : raw42679step2 = -raw42679step1 := by apply Matrix.ext; change ∀ i j, raw42679step2 i j = -(raw42679step1 i j); unfold raw42679step2 raw42679step1; decide +kernel
      have hl : raw42679step2Labels = raw42679step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42679step2 raw42679step2Labels = mixedMoment B raw42679step3 raw42679step3Labels := by
      have ha : raw42679step3 = raw42679step2 := by apply Matrix.ext; unfold raw42679step3 raw42679step2; decide +kernel
      have hl : raw42679step2Labels = labelEmbedding6 ∘ raw42679step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42679step2 raw42679step2Labels raw42679step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

theorem canonical42680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42680 raw42680Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw42680 raw42680Labels = mixedMoment B raw42680step0 raw42680step0Labels := by
      have ha : raw42680step0 = (fun i j => raw42680 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42680step0 raw42680; decide +kernel
      have hl : raw42680step0Labels = raw42680Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42680 raw42680Labels permutation158 permutation2
    mixedMoment B raw42680step0 raw42680step0Labels = mixedMoment B raw42680step1 raw42680step1Labels := by
      have ha : raw42680step1 = raw42680step0 := by apply Matrix.ext; unfold raw42680step1 raw42680step0; decide +kernel
      have hl : raw42680step0Labels = labelEmbedding1 ∘ raw42680step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42680step0 raw42680step0Labels raw42680step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

theorem canonical42681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42681 raw42681Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw42681 raw42681Labels = mixedMoment B raw42681step0 raw42681step0Labels := by
      have ha : raw42681step0 = (fun i j => raw42681 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42681step0 raw42681; decide +kernel
      have hl : raw42681step0Labels = raw42681Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42681 raw42681Labels permutation212 permutation7
    mixedMoment B raw42681step0 raw42681step0Labels = mixedMoment B raw42681step1 raw42681step1Labels := by
      have ha : raw42681step1 = -raw42681step0 := by apply Matrix.ext; change ∀ i j, raw42681step1 i j = -(raw42681step0 i j); unfold raw42681step1 raw42681step0; decide +kernel
      have hl : raw42681step1Labels = raw42681step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42681step1 raw42681step1Labels = mixedMoment B raw42681step2 raw42681step2Labels := by
      have ha : raw42681step2 = raw42681step1 := by apply Matrix.ext; unfold raw42681step2 raw42681step1; decide +kernel
      have hl : raw42681step1Labels = labelEmbedding6 ∘ raw42681step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42681step1 raw42681step1Labels raw42681step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5144 node5144Labels := by rfl

theorem canonical42682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42682 raw42682Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw42682 raw42682Labels = mixedMoment B raw42682step0 raw42682step0Labels := by
      have ha : raw42682step0 = (fun i j => raw42682 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42682step0 raw42682; decide +kernel
      have hl : raw42682step0Labels = raw42682Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42682 raw42682Labels permutation156 permutation2
    mixedMoment B raw42682step0 raw42682step0Labels = mixedMoment B raw42682step1 raw42682step1Labels := by
      have ha : raw42682step1 = raw42682step0 := by apply Matrix.ext; unfold raw42682step1 raw42682step0; decide +kernel
      have hl : raw42682step0Labels = labelEmbedding1 ∘ raw42682step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42682step0 raw42682step0Labels raw42682step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3569 node3569Labels := by rfl

theorem canonical42683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42683 raw42683Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw42683 raw42683Labels = mixedMoment B raw42683step0 raw42683step0Labels := by
      have ha : raw42683step0 = (fun i j => raw42683 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42683step0 raw42683; decide +kernel
      have hl : raw42683step0Labels = raw42683Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42683 raw42683Labels permutation246 permutation7
    mixedMoment B raw42683step0 raw42683step0Labels = mixedMoment B raw42683step1 raw42683step1Labels := by
      have ha : raw42683step1 = -raw42683step0 := by apply Matrix.ext; change ∀ i j, raw42683step1 i j = -(raw42683step0 i j); unfold raw42683step1 raw42683step0; decide +kernel
      have hl : raw42683step1Labels = raw42683step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42683step1 raw42683step1Labels = mixedMoment B raw42683step2 raw42683step2Labels := by
      have ha : raw42683step2 = raw42683step1 := by apply Matrix.ext; unfold raw42683step2 raw42683step1; decide +kernel
      have hl : raw42683step1Labels = labelEmbedding6 ∘ raw42683step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42683step1 raw42683step1Labels raw42683step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

theorem canonical42684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42684 raw42684Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw42684 raw42684Labels = mixedMoment B raw42684step0 raw42684step0Labels := by
      have ha : raw42684step0 = (fun i j => raw42684 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42684step0 raw42684; decide +kernel
      have hl : raw42684step0Labels = raw42684Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42684 raw42684Labels permutation155 permutation2
    mixedMoment B raw42684step0 raw42684step0Labels = mixedMoment B raw42684step1 raw42684step1Labels := by
      have ha : raw42684step1 = raw42684step0 := by apply Matrix.ext; unfold raw42684step1 raw42684step0; decide +kernel
      have hl : raw42684step0Labels = labelEmbedding1 ∘ raw42684step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42684step0 raw42684step0Labels raw42684step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

theorem canonical42685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42685 raw42685Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw42685 raw42685Labels = mixedMoment B raw42685step0 raw42685step0Labels := by
      have ha : raw42685step0 = (fun i j => raw42685 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42685step0 raw42685; decide +kernel
      have hl : raw42685step0Labels = raw42685Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42685 raw42685Labels permutation240 permutation7
    mixedMoment B raw42685step0 raw42685step0Labels = mixedMoment B raw42685step1 raw42685step1Labels := by
      have ha : raw42685step1 = -raw42685step0 := by apply Matrix.ext; change ∀ i j, raw42685step1 i j = -(raw42685step0 i j); unfold raw42685step1 raw42685step0; decide +kernel
      have hl : raw42685step1Labels = raw42685step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42685step1 raw42685step1Labels = mixedMoment B raw42685step2 raw42685step2Labels := by
      have ha : raw42685step2 = raw42685step1 := by apply Matrix.ext; unfold raw42685step2 raw42685step1; decide +kernel
      have hl : raw42685step1Labels = labelEmbedding6 ∘ raw42685step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42685step1 raw42685step1Labels raw42685step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical42686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42686 raw42686Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw42686 raw42686Labels = mixedMoment B raw42686step0 raw42686step0Labels := by
      have hz : ∀ j, raw42686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42686step0 = (fun i j => raw42686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42686step0 raw42686; decide +kernel
      have hl : raw42686step0Labels = raw42686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42686 raw42686Labels permutation434 hz
    mixedMoment B raw42686step0 raw42686step0Labels = mixedMoment B raw42686step1 raw42686step1Labels := by
      have hz : ∀ j, raw42686step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42686step1 = (fun i j => raw42686step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42686step1 raw42686step0; decide +kernel
      have hl : raw42686step1Labels = raw42686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42686step0 raw42686step0Labels permutation80 hz
    mixedMoment B raw42686step1 raw42686step1Labels = mixedMoment B raw42686step2 raw42686step2Labels := by
      have ha : raw42686step2 = raw42686step1 := by apply Matrix.ext; unfold raw42686step2 raw42686step1; decide +kernel
      have hl : raw42686step1Labels = labelEmbedding1 ∘ raw42686step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42686step1 raw42686step1Labels raw42686step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

theorem canonical42687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42687 raw42687Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw42687 raw42687Labels = mixedMoment B raw42687step0 raw42687step0Labels := by
      have hz : ∀ j, raw42687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42687step0 = (fun i j => raw42687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42687step0 raw42687; decide +kernel
      have hl : raw42687step0Labels = raw42687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42687 raw42687Labels permutation434 hz
    mixedMoment B raw42687step0 raw42687step0Labels = mixedMoment B raw42687step1 raw42687step1Labels := by
      have hz : ∀ j, raw42687step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42687step1 = (fun i j => raw42687step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42687step1 raw42687step0; decide +kernel
      have hl : raw42687step1Labels = raw42687step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42687step0 raw42687step0Labels permutation80 hz
    mixedMoment B raw42687step1 raw42687step1Labels = mixedMoment B raw42687step2 raw42687step2Labels := by
      have ha : raw42687step2 = (fun i j => raw42687step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42687step2 raw42687step1; decide +kernel
      have hl : raw42687step2Labels = raw42687step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42687step1 raw42687step1Labels permutation12 permutation7
    mixedMoment B raw42687step2 raw42687step2Labels = mixedMoment B raw42687step3 raw42687step3Labels := by
      have ha : raw42687step3 = -raw42687step2 := by apply Matrix.ext; change ∀ i j, raw42687step3 i j = -(raw42687step2 i j); unfold raw42687step3 raw42687step2; decide +kernel
      have hl : raw42687step3Labels = raw42687step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42687step3 raw42687step3Labels = mixedMoment B raw42687step4 raw42687step4Labels := by
      have ha : raw42687step4 = raw42687step3 := by apply Matrix.ext; unfold raw42687step4 raw42687step3; decide +kernel
      have hl : raw42687step3Labels = labelEmbedding6 ∘ raw42687step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42687step3 raw42687step3Labels raw42687step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2656 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2656) =
      Integer.Sparse.eval keyMomentRow2656 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2656).leftCharge (GramAssembly.key 2656).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1522) := by
    have ha : gramCharges (GramAssembly.key 2656).leftCharge (GramAssembly.key 2656).rightCharge = raw42624 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42624Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42624 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2656).leftCharge (GramAssembly.key 2656).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4158) := by
    have ha : gramCharges (GramAssembly.key 2656).leftCharge (GramAssembly.key 2656).rightCharge = raw42625 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42625Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42625 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2656).leftCharge (GramAssembly.key 2656).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2656).leftCharge (GramAssembly.key 2656).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2656, Integer.Sparse.eval]
  ring

theorem keyMoment2657 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2657) =
      Integer.Sparse.eval keyMomentRow2657 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2657).leftCharge (GramAssembly.key 2657).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1682) := by
    have ha : gramCharges (GramAssembly.key 2657).leftCharge (GramAssembly.key 2657).rightCharge = raw42626 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42626Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42626 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2657).leftCharge (GramAssembly.key 2657).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4357) := by
    have ha : gramCharges (GramAssembly.key 2657).leftCharge (GramAssembly.key 2657).rightCharge = raw42627 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42627Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42627 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2657).leftCharge (GramAssembly.key 2657).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2657).leftCharge (GramAssembly.key 2657).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2657, Integer.Sparse.eval]
  ring

theorem keyMoment2658 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2658) =
      Integer.Sparse.eval keyMomentRow2658 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2658).leftCharge (GramAssembly.key 2658).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1736) := by
    have ha : gramCharges (GramAssembly.key 2658).leftCharge (GramAssembly.key 2658).rightCharge = raw42628 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42628Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42628 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2658).leftCharge (GramAssembly.key 2658).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4444) := by
    have ha : gramCharges (GramAssembly.key 2658).leftCharge (GramAssembly.key 2658).rightCharge = raw42629 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42629Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42629 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2658).leftCharge (GramAssembly.key 2658).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2658).leftCharge (GramAssembly.key 2658).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2658, Integer.Sparse.eval]
  ring

theorem keyMoment2659 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2659) =
      Integer.Sparse.eval keyMomentRow2659 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2659).leftCharge (GramAssembly.key 2659).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3418) := by
    have ha : gramCharges (GramAssembly.key 2659).leftCharge (GramAssembly.key 2659).rightCharge = raw42630 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42630Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42630 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2659).leftCharge (GramAssembly.key 2659).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4951) := by
    have ha : gramCharges (GramAssembly.key 2659).leftCharge (GramAssembly.key 2659).rightCharge = raw42631 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42631Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42631 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2659).leftCharge (GramAssembly.key 2659).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2659).leftCharge (GramAssembly.key 2659).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2659, Integer.Sparse.eval]
  ring

theorem keyMoment2660 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2660) =
      Integer.Sparse.eval keyMomentRow2660 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2660).leftCharge (GramAssembly.key 2660).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1678) := by
    have ha : gramCharges (GramAssembly.key 2660).leftCharge (GramAssembly.key 2660).rightCharge = raw42632 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42632Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42632 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2660).leftCharge (GramAssembly.key 2660).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4332) := by
    have ha : gramCharges (GramAssembly.key 2660).leftCharge (GramAssembly.key 2660).rightCharge = raw42633 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42633Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42633 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2660).leftCharge (GramAssembly.key 2660).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2660).leftCharge (GramAssembly.key 2660).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2660, Integer.Sparse.eval]
  ring

theorem keyMoment2661 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2661) =
      Integer.Sparse.eval keyMomentRow2661 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2661).leftCharge (GramAssembly.key 2661).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3414) := by
    have ha : gramCharges (GramAssembly.key 2661).leftCharge (GramAssembly.key 2661).rightCharge = raw42634 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42634Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42634 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2661).leftCharge (GramAssembly.key 2661).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4933) := by
    have ha : gramCharges (GramAssembly.key 2661).leftCharge (GramAssembly.key 2661).rightCharge = raw42635 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42635Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42635 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2661).leftCharge (GramAssembly.key 2661).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2661).leftCharge (GramAssembly.key 2661).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2661, Integer.Sparse.eval]
  ring

theorem keyMoment2662 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2662) =
      Integer.Sparse.eval keyMomentRow2662 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2662).leftCharge (GramAssembly.key 2662).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2155) := by
    have ha : gramCharges (GramAssembly.key 2662).leftCharge (GramAssembly.key 2662).rightCharge = raw42636 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42636Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42636 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2662).leftCharge (GramAssembly.key 2662).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4669) := by
    have ha : gramCharges (GramAssembly.key 2662).leftCharge (GramAssembly.key 2662).rightCharge = raw42637 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42637Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42637 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2662).leftCharge (GramAssembly.key 2662).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2662).leftCharge (GramAssembly.key 2662).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2662, Integer.Sparse.eval]
  ring

theorem keyMoment2663 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2663) =
      Integer.Sparse.eval keyMomentRow2663 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2663).leftCharge (GramAssembly.key 2663).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2176) := by
    have ha : gramCharges (GramAssembly.key 2663).leftCharge (GramAssembly.key 2663).rightCharge = raw42638 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42638Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42638 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2663).leftCharge (GramAssembly.key 2663).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4756) := by
    have ha : gramCharges (GramAssembly.key 2663).leftCharge (GramAssembly.key 2663).rightCharge = raw42639 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42639Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42639 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2663).leftCharge (GramAssembly.key 2663).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2663).leftCharge (GramAssembly.key 2663).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2663, Integer.Sparse.eval]
  ring

theorem keyMoment2664 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2664) =
      Integer.Sparse.eval keyMomentRow2664 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2664).leftCharge (GramAssembly.key 2664).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3509) := by
    have ha : gramCharges (GramAssembly.key 2664).leftCharge (GramAssembly.key 2664).rightCharge = raw42640 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42640Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42640 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2664).leftCharge (GramAssembly.key 2664).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4957) := by
    have ha : gramCharges (GramAssembly.key 2664).leftCharge (GramAssembly.key 2664).rightCharge = raw42641 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42641Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42641 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2664).leftCharge (GramAssembly.key 2664).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2664).leftCharge (GramAssembly.key 2664).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2664, Integer.Sparse.eval]
  ring

theorem keyMoment2665 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2665) =
      Integer.Sparse.eval keyMomentRow2665 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2665).leftCharge (GramAssembly.key 2665).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3512) := by
    have ha : gramCharges (GramAssembly.key 2665).leftCharge (GramAssembly.key 2665).rightCharge = raw42642 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42642Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42642 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2665).leftCharge (GramAssembly.key 2665).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4959) := by
    have ha : gramCharges (GramAssembly.key 2665).leftCharge (GramAssembly.key 2665).rightCharge = raw42643 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42643Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42643 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2665).leftCharge (GramAssembly.key 2665).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2665).leftCharge (GramAssembly.key 2665).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2665, Integer.Sparse.eval]
  ring

theorem keyMoment2666 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2666) =
      Integer.Sparse.eval keyMomentRow2666 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2666).leftCharge (GramAssembly.key 2666).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3508) := by
    have ha : gramCharges (GramAssembly.key 2666).leftCharge (GramAssembly.key 2666).rightCharge = raw42644 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42644Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42644 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2666).leftCharge (GramAssembly.key 2666).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4955) := by
    have ha : gramCharges (GramAssembly.key 2666).leftCharge (GramAssembly.key 2666).rightCharge = raw42645 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42645Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42645 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2666).leftCharge (GramAssembly.key 2666).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2666).leftCharge (GramAssembly.key 2666).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2666, Integer.Sparse.eval]
  ring

theorem keyMoment2667 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2667) =
      Integer.Sparse.eval keyMomentRow2667 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2667).leftCharge (GramAssembly.key 2667).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3510) := by
    have ha : gramCharges (GramAssembly.key 2667).leftCharge (GramAssembly.key 2667).rightCharge = raw42646 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42646Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42646 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2667).leftCharge (GramAssembly.key 2667).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4956) := by
    have ha : gramCharges (GramAssembly.key 2667).leftCharge (GramAssembly.key 2667).rightCharge = raw42647 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42647Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42647 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2667).leftCharge (GramAssembly.key 2667).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2667).leftCharge (GramAssembly.key 2667).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2667, Integer.Sparse.eval]
  ring

theorem keyMoment2668 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2668) =
      Integer.Sparse.eval keyMomentRow2668 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2668).leftCharge (GramAssembly.key 2668).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3268) := by
    have ha : gramCharges (GramAssembly.key 2668).leftCharge (GramAssembly.key 2668).rightCharge = raw42648 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42648Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42648 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2668).leftCharge (GramAssembly.key 2668).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4534) := by
    have ha : gramCharges (GramAssembly.key 2668).leftCharge (GramAssembly.key 2668).rightCharge = raw42649 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42649Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42649 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2668).leftCharge (GramAssembly.key 2668).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2668).leftCharge (GramAssembly.key 2668).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2668, Integer.Sparse.eval]
  ring

theorem keyMoment2669 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2669) =
      Integer.Sparse.eval keyMomentRow2669 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2669).leftCharge (GramAssembly.key 2669).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3452) := by
    have ha : gramCharges (GramAssembly.key 2669).leftCharge (GramAssembly.key 2669).rightCharge = raw42650 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42650Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42650 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2669).leftCharge (GramAssembly.key 2669).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4954) := by
    have ha : gramCharges (GramAssembly.key 2669).leftCharge (GramAssembly.key 2669).rightCharge = raw42651 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42651Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42651 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2669).leftCharge (GramAssembly.key 2669).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2669).leftCharge (GramAssembly.key 2669).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2669, Integer.Sparse.eval]
  ring

theorem keyMoment2670 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2670) =
      Integer.Sparse.eval keyMomentRow2670 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2670).leftCharge (GramAssembly.key 2670).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3511) := by
    have ha : gramCharges (GramAssembly.key 2670).leftCharge (GramAssembly.key 2670).rightCharge = raw42652 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42652Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42652 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2670).leftCharge (GramAssembly.key 2670).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4958) := by
    have ha : gramCharges (GramAssembly.key 2670).leftCharge (GramAssembly.key 2670).rightCharge = raw42653 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42653Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42653 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2670).leftCharge (GramAssembly.key 2670).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2670).leftCharge (GramAssembly.key 2670).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2670, Integer.Sparse.eval]
  ring

theorem keyMoment2671 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2671) =
      Integer.Sparse.eval keyMomentRow2671 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2671).leftCharge (GramAssembly.key 2671).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1523) := by
    have ha : gramCharges (GramAssembly.key 2671).leftCharge (GramAssembly.key 2671).rightCharge = raw42654 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42654Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42654 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2671).leftCharge (GramAssembly.key 2671).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4160) := by
    have ha : gramCharges (GramAssembly.key 2671).leftCharge (GramAssembly.key 2671).rightCharge = raw42655 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42655Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42655 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2671).leftCharge (GramAssembly.key 2671).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2671).leftCharge (GramAssembly.key 2671).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2671, Integer.Sparse.eval]
  ring

theorem keyMoment2672 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2672) =
      Integer.Sparse.eval keyMomentRow2672 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2672).leftCharge (GramAssembly.key 2672).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1679) := by
    have ha : gramCharges (GramAssembly.key 2672).leftCharge (GramAssembly.key 2672).rightCharge = raw42656 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42656Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42656 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2672).leftCharge (GramAssembly.key 2672).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4334) := by
    have ha : gramCharges (GramAssembly.key 2672).leftCharge (GramAssembly.key 2672).rightCharge = raw42657 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42657Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42657 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2672).leftCharge (GramAssembly.key 2672).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2672).leftCharge (GramAssembly.key 2672).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2672, Integer.Sparse.eval]
  ring

theorem keyMoment2673 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2673) =
      Integer.Sparse.eval keyMomentRow2673 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2673).leftCharge (GramAssembly.key 2673).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3415) := by
    have ha : gramCharges (GramAssembly.key 2673).leftCharge (GramAssembly.key 2673).rightCharge = raw42658 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42658Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42658 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2673).leftCharge (GramAssembly.key 2673).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4934) := by
    have ha : gramCharges (GramAssembly.key 2673).leftCharge (GramAssembly.key 2673).rightCharge = raw42659 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42659Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42659 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2673).leftCharge (GramAssembly.key 2673).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2673).leftCharge (GramAssembly.key 2673).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2673, Integer.Sparse.eval]
  ring

theorem keyMoment2674 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2674) =
      Integer.Sparse.eval keyMomentRow2674 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2674).leftCharge (GramAssembly.key 2674).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2744) := by
    have ha : gramCharges (GramAssembly.key 2674).leftCharge (GramAssembly.key 2674).rightCharge = raw42660 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42660Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42660 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2674).leftCharge (GramAssembly.key 2674).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5276) := by
    have ha : gramCharges (GramAssembly.key 2674).leftCharge (GramAssembly.key 2674).rightCharge = raw42661 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42661Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42661 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2674).leftCharge (GramAssembly.key 2674).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2674).leftCharge (GramAssembly.key 2674).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2674, Integer.Sparse.eval]
  ring

theorem keyMoment2675 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2675) =
      Integer.Sparse.eval keyMomentRow2675 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2675).leftCharge (GramAssembly.key 2675).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2781) := by
    have ha : gramCharges (GramAssembly.key 2675).leftCharge (GramAssembly.key 2675).rightCharge = raw42662 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42662Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42662 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2675).leftCharge (GramAssembly.key 2675).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5295) := by
    have ha : gramCharges (GramAssembly.key 2675).leftCharge (GramAssembly.key 2675).rightCharge = raw42663 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42663Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42663 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2675).leftCharge (GramAssembly.key 2675).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2675).leftCharge (GramAssembly.key 2675).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2675, Integer.Sparse.eval]
  ring

theorem keyMoment2676 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2676) =
      Integer.Sparse.eval keyMomentRow2676 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2676).leftCharge (GramAssembly.key 2676).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2687) := by
    have ha : gramCharges (GramAssembly.key 2676).leftCharge (GramAssembly.key 2676).rightCharge = raw42664 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42664Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42664 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2676).leftCharge (GramAssembly.key 2676).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5206) := by
    have ha : gramCharges (GramAssembly.key 2676).leftCharge (GramAssembly.key 2676).rightCharge = raw42665 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42665Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42665 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2676).leftCharge (GramAssembly.key 2676).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2676).leftCharge (GramAssembly.key 2676).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2676, Integer.Sparse.eval]
  ring

theorem keyMoment2677 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2677) =
      Integer.Sparse.eval keyMomentRow2677 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2677).leftCharge (GramAssembly.key 2677).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2681) := by
    have ha : gramCharges (GramAssembly.key 2677).leftCharge (GramAssembly.key 2677).rightCharge = raw42666 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42666Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42666 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2677).leftCharge (GramAssembly.key 2677).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5151) := by
    have ha : gramCharges (GramAssembly.key 2677).leftCharge (GramAssembly.key 2677).rightCharge = raw42667 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42667Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42667 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2677).leftCharge (GramAssembly.key 2677).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2677).leftCharge (GramAssembly.key 2677).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2677, Integer.Sparse.eval]
  ring

theorem keyMoment2678 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2678) =
      Integer.Sparse.eval keyMomentRow2678 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2678).leftCharge (GramAssembly.key 2678).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2706) := by
    have ha : gramCharges (GramAssembly.key 2678).leftCharge (GramAssembly.key 2678).rightCharge = raw42668 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42668Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42668 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2678).leftCharge (GramAssembly.key 2678).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5205) := by
    have ha : gramCharges (GramAssembly.key 2678).leftCharge (GramAssembly.key 2678).rightCharge = raw42669 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42669Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42669 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2678).leftCharge (GramAssembly.key 2678).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2678).leftCharge (GramAssembly.key 2678).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2678, Integer.Sparse.eval]
  ring

theorem keyMoment2679 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2679) =
      Integer.Sparse.eval keyMomentRow2679 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2679).leftCharge (GramAssembly.key 2679).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2738) := by
    have ha : gramCharges (GramAssembly.key 2679).leftCharge (GramAssembly.key 2679).rightCharge = raw42670 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42670Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42670 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2679).leftCharge (GramAssembly.key 2679).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5270) := by
    have ha : gramCharges (GramAssembly.key 2679).leftCharge (GramAssembly.key 2679).rightCharge = raw42671 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42671Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42671 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2679).leftCharge (GramAssembly.key 2679).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2679).leftCharge (GramAssembly.key 2679).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2679, Integer.Sparse.eval]
  ring

theorem keyMoment2680 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2680) =
      Integer.Sparse.eval keyMomentRow2680 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2680).leftCharge (GramAssembly.key 2680).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2700) := by
    have ha : gramCharges (GramAssembly.key 2680).leftCharge (GramAssembly.key 2680).rightCharge = raw42672 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42672Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42672 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2680).leftCharge (GramAssembly.key 2680).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5150) := by
    have ha : gramCharges (GramAssembly.key 2680).leftCharge (GramAssembly.key 2680).rightCharge = raw42673 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42673Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42673 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2680).leftCharge (GramAssembly.key 2680).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2680).leftCharge (GramAssembly.key 2680).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2680, Integer.Sparse.eval]
  ring

theorem keyMoment2681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2681) =
      Integer.Sparse.eval keyMomentRow2681 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2681).leftCharge (GramAssembly.key 2681).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3573) := by
    have ha : gramCharges (GramAssembly.key 2681).leftCharge (GramAssembly.key 2681).rightCharge = raw42674 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42674Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42674 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2681).leftCharge (GramAssembly.key 2681).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2681).leftCharge (GramAssembly.key 2681).rightCharge = raw42675 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42675Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42675 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2681).leftCharge (GramAssembly.key 2681).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2681).leftCharge (GramAssembly.key 2681).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2681, Integer.Sparse.eval]
  ring

theorem keyMoment2682 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2682) =
      Integer.Sparse.eval keyMomentRow2682 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2682).leftCharge (GramAssembly.key 2682).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3572) := by
    have ha : gramCharges (GramAssembly.key 2682).leftCharge (GramAssembly.key 2682).rightCharge = raw42676 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42676Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42676 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2682).leftCharge (GramAssembly.key 2682).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5289) := by
    have ha : gramCharges (GramAssembly.key 2682).leftCharge (GramAssembly.key 2682).rightCharge = raw42677 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42677Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42677 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2682).leftCharge (GramAssembly.key 2682).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2682).leftCharge (GramAssembly.key 2682).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2682, Integer.Sparse.eval]
  ring

theorem keyMoment2683 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2683) =
      Integer.Sparse.eval keyMomentRow2683 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2683).leftCharge (GramAssembly.key 2683).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3570) := by
    have ha : gramCharges (GramAssembly.key 2683).leftCharge (GramAssembly.key 2683).rightCharge = raw42678 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42678Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42678 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2683).leftCharge (GramAssembly.key 2683).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5198) := by
    have ha : gramCharges (GramAssembly.key 2683).leftCharge (GramAssembly.key 2683).rightCharge = raw42679 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42679Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42679 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2683).leftCharge (GramAssembly.key 2683).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2683).leftCharge (GramAssembly.key 2683).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2683, Integer.Sparse.eval]
  ring

theorem keyMoment2684 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2684) =
      Integer.Sparse.eval keyMomentRow2684 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2684).leftCharge (GramAssembly.key 2684).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3557) := by
    have ha : gramCharges (GramAssembly.key 2684).leftCharge (GramAssembly.key 2684).rightCharge = raw42680 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42680Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42680 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2684).leftCharge (GramAssembly.key 2684).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5144) := by
    have ha : gramCharges (GramAssembly.key 2684).leftCharge (GramAssembly.key 2684).rightCharge = raw42681 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42681Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42681 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2684).leftCharge (GramAssembly.key 2684).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2684).leftCharge (GramAssembly.key 2684).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2684, Integer.Sparse.eval]
  ring

theorem keyMoment2685 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2685) =
      Integer.Sparse.eval keyMomentRow2685 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2685).leftCharge (GramAssembly.key 2685).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3569) := by
    have ha : gramCharges (GramAssembly.key 2685).leftCharge (GramAssembly.key 2685).rightCharge = raw42682 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42682Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42682 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2685).leftCharge (GramAssembly.key 2685).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5197) := by
    have ha : gramCharges (GramAssembly.key 2685).leftCharge (GramAssembly.key 2685).rightCharge = raw42683 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42683Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42683 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2685).leftCharge (GramAssembly.key 2685).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2685).leftCharge (GramAssembly.key 2685).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2685, Integer.Sparse.eval]
  ring

theorem keyMoment2686 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2686) =
      Integer.Sparse.eval keyMomentRow2686 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2686).leftCharge (GramAssembly.key 2686).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3571) := by
    have ha : gramCharges (GramAssembly.key 2686).leftCharge (GramAssembly.key 2686).rightCharge = raw42684 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42684Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42684 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2686).leftCharge (GramAssembly.key 2686).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5281) := by
    have ha : gramCharges (GramAssembly.key 2686).leftCharge (GramAssembly.key 2686).rightCharge = raw42685 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42685Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42685 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2686).leftCharge (GramAssembly.key 2686).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2686).leftCharge (GramAssembly.key 2686).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2686, Integer.Sparse.eval]
  ring

theorem keyMoment2687 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2687) =
      Integer.Sparse.eval keyMomentRow2687 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2687).leftCharge (GramAssembly.key 2687).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3584) := by
    have ha : gramCharges (GramAssembly.key 2687).leftCharge (GramAssembly.key 2687).rightCharge = raw42686 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42686Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42686 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2687).leftCharge (GramAssembly.key 2687).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5300) := by
    have ha : gramCharges (GramAssembly.key 2687).leftCharge (GramAssembly.key 2687).rightCharge = raw42687 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42687Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42687 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2687).leftCharge (GramAssembly.key 2687).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2687).leftCharge (GramAssembly.key 2687).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2687, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2656 : keyMomentRows (2656 : Fin 2886) =
    keyMomentRow2656 := by decide +kernel

theorem keyMomentRowsAt2657 : keyMomentRows (2657 : Fin 2886) =
    keyMomentRow2657 := by decide +kernel

theorem keyMomentRowsAt2658 : keyMomentRows (2658 : Fin 2886) =
    keyMomentRow2658 := by decide +kernel

theorem keyMomentRowsAt2659 : keyMomentRows (2659 : Fin 2886) =
    keyMomentRow2659 := by decide +kernel

theorem keyMomentRowsAt2660 : keyMomentRows (2660 : Fin 2886) =
    keyMomentRow2660 := by decide +kernel

theorem keyMomentRowsAt2661 : keyMomentRows (2661 : Fin 2886) =
    keyMomentRow2661 := by decide +kernel

theorem keyMomentRowsAt2662 : keyMomentRows (2662 : Fin 2886) =
    keyMomentRow2662 := by decide +kernel

theorem keyMomentRowsAt2663 : keyMomentRows (2663 : Fin 2886) =
    keyMomentRow2663 := by decide +kernel

theorem keyMomentRowsAt2664 : keyMomentRows (2664 : Fin 2886) =
    keyMomentRow2664 := by decide +kernel

theorem keyMomentRowsAt2665 : keyMomentRows (2665 : Fin 2886) =
    keyMomentRow2665 := by decide +kernel

theorem keyMomentRowsAt2666 : keyMomentRows (2666 : Fin 2886) =
    keyMomentRow2666 := by decide +kernel

theorem keyMomentRowsAt2667 : keyMomentRows (2667 : Fin 2886) =
    keyMomentRow2667 := by decide +kernel

theorem keyMomentRowsAt2668 : keyMomentRows (2668 : Fin 2886) =
    keyMomentRow2668 := by decide +kernel

theorem keyMomentRowsAt2669 : keyMomentRows (2669 : Fin 2886) =
    keyMomentRow2669 := by decide +kernel

theorem keyMomentRowsAt2670 : keyMomentRows (2670 : Fin 2886) =
    keyMomentRow2670 := by decide +kernel

theorem keyMomentRowsAt2671 : keyMomentRows (2671 : Fin 2886) =
    keyMomentRow2671 := by decide +kernel

theorem keyMomentRowsAt2672 : keyMomentRows (2672 : Fin 2886) =
    keyMomentRow2672 := by decide +kernel

theorem keyMomentRowsAt2673 : keyMomentRows (2673 : Fin 2886) =
    keyMomentRow2673 := by decide +kernel

theorem keyMomentRowsAt2674 : keyMomentRows (2674 : Fin 2886) =
    keyMomentRow2674 := by decide +kernel

theorem keyMomentRowsAt2675 : keyMomentRows (2675 : Fin 2886) =
    keyMomentRow2675 := by decide +kernel

theorem keyMomentRowsAt2676 : keyMomentRows (2676 : Fin 2886) =
    keyMomentRow2676 := by decide +kernel

theorem keyMomentRowsAt2677 : keyMomentRows (2677 : Fin 2886) =
    keyMomentRow2677 := by decide +kernel

theorem keyMomentRowsAt2678 : keyMomentRows (2678 : Fin 2886) =
    keyMomentRow2678 := by decide +kernel

theorem keyMomentRowsAt2679 : keyMomentRows (2679 : Fin 2886) =
    keyMomentRow2679 := by decide +kernel

theorem keyMomentRowsAt2680 : keyMomentRows (2680 : Fin 2886) =
    keyMomentRow2680 := by decide +kernel

theorem keyMomentRowsAt2681 : keyMomentRows (2681 : Fin 2886) =
    keyMomentRow2681 := by decide +kernel

theorem keyMomentRowsAt2682 : keyMomentRows (2682 : Fin 2886) =
    keyMomentRow2682 := by decide +kernel

theorem keyMomentRowsAt2683 : keyMomentRows (2683 : Fin 2886) =
    keyMomentRow2683 := by decide +kernel

theorem keyMomentRowsAt2684 : keyMomentRows (2684 : Fin 2886) =
    keyMomentRow2684 := by decide +kernel

theorem keyMomentRowsAt2685 : keyMomentRows (2685 : Fin 2886) =
    keyMomentRow2685 := by decide +kernel

theorem keyMomentRowsAt2686 : keyMomentRows (2686 : Fin 2886) =
    keyMomentRow2686 := by decide +kernel

theorem keyMomentRowsAt2687 : keyMomentRows (2687 : Fin 2886) =
    keyMomentRow2687 := by decide +kernel

theorem keyMomentChunkSound83_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 83) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2656 ∨ k.val = 2657 ∨ k.val = 2658 ∨ k.val = 2659 ∨ k.val = 2660 ∨ k.val = 2661 ∨ k.val = 2662 ∨ k.val = 2663 ∨ k.val = 2664 ∨ k.val = 2665 ∨ k.val = 2666 ∨ k.val = 2667 ∨ k.val = 2668 ∨ k.val = 2669 ∨ k.val = 2670 ∨ k.val = 2671 ∨ k.val = 2672 ∨ k.val = 2673 ∨ k.val = 2674 ∨ k.val = 2675 ∨ k.val = 2676 ∨ k.val = 2677 ∨ k.val = 2678 ∨ k.val = 2679 ∨ k.val = 2680 ∨ k.val = 2681 ∨ k.val = 2682 ∨ k.val = 2683 ∨ k.val = 2684 ∨ k.val = 2685 ∨ k.val = 2686 ∨ k.val = 2687 := by omega
  rcases heq with h2656 | h2657 | h2658 | h2659 | h2660 | h2661 | h2662 | h2663 | h2664 | h2665 | h2666 | h2667 | h2668 | h2669 | h2670 | h2671 | h2672 | h2673 | h2674 | h2675 | h2676 | h2677 | h2678 | h2679 | h2680 | h2681 | h2682 | h2683 | h2684 | h2685 | h2686 | h2687
  · have he : k = (2656 : Fin 2886) := Fin.ext h2656
    subst k
    rw [keyMomentRowsAt2656]
    exact keyMoment2656 B hB
  · have he : k = (2657 : Fin 2886) := Fin.ext h2657
    subst k
    rw [keyMomentRowsAt2657]
    exact keyMoment2657 B hB
  · have he : k = (2658 : Fin 2886) := Fin.ext h2658
    subst k
    rw [keyMomentRowsAt2658]
    exact keyMoment2658 B hB
  · have he : k = (2659 : Fin 2886) := Fin.ext h2659
    subst k
    rw [keyMomentRowsAt2659]
    exact keyMoment2659 B hB
  · have he : k = (2660 : Fin 2886) := Fin.ext h2660
    subst k
    rw [keyMomentRowsAt2660]
    exact keyMoment2660 B hB
  · have he : k = (2661 : Fin 2886) := Fin.ext h2661
    subst k
    rw [keyMomentRowsAt2661]
    exact keyMoment2661 B hB
  · have he : k = (2662 : Fin 2886) := Fin.ext h2662
    subst k
    rw [keyMomentRowsAt2662]
    exact keyMoment2662 B hB
  · have he : k = (2663 : Fin 2886) := Fin.ext h2663
    subst k
    rw [keyMomentRowsAt2663]
    exact keyMoment2663 B hB
  · have he : k = (2664 : Fin 2886) := Fin.ext h2664
    subst k
    rw [keyMomentRowsAt2664]
    exact keyMoment2664 B hB
  · have he : k = (2665 : Fin 2886) := Fin.ext h2665
    subst k
    rw [keyMomentRowsAt2665]
    exact keyMoment2665 B hB
  · have he : k = (2666 : Fin 2886) := Fin.ext h2666
    subst k
    rw [keyMomentRowsAt2666]
    exact keyMoment2666 B hB
  · have he : k = (2667 : Fin 2886) := Fin.ext h2667
    subst k
    rw [keyMomentRowsAt2667]
    exact keyMoment2667 B hB
  · have he : k = (2668 : Fin 2886) := Fin.ext h2668
    subst k
    rw [keyMomentRowsAt2668]
    exact keyMoment2668 B hB
  · have he : k = (2669 : Fin 2886) := Fin.ext h2669
    subst k
    rw [keyMomentRowsAt2669]
    exact keyMoment2669 B hB
  · have he : k = (2670 : Fin 2886) := Fin.ext h2670
    subst k
    rw [keyMomentRowsAt2670]
    exact keyMoment2670 B hB
  · have he : k = (2671 : Fin 2886) := Fin.ext h2671
    subst k
    rw [keyMomentRowsAt2671]
    exact keyMoment2671 B hB
  · have he : k = (2672 : Fin 2886) := Fin.ext h2672
    subst k
    rw [keyMomentRowsAt2672]
    exact keyMoment2672 B hB
  · have he : k = (2673 : Fin 2886) := Fin.ext h2673
    subst k
    rw [keyMomentRowsAt2673]
    exact keyMoment2673 B hB
  · have he : k = (2674 : Fin 2886) := Fin.ext h2674
    subst k
    rw [keyMomentRowsAt2674]
    exact keyMoment2674 B hB
  · have he : k = (2675 : Fin 2886) := Fin.ext h2675
    subst k
    rw [keyMomentRowsAt2675]
    exact keyMoment2675 B hB
  · have he : k = (2676 : Fin 2886) := Fin.ext h2676
    subst k
    rw [keyMomentRowsAt2676]
    exact keyMoment2676 B hB
  · have he : k = (2677 : Fin 2886) := Fin.ext h2677
    subst k
    rw [keyMomentRowsAt2677]
    exact keyMoment2677 B hB
  · have he : k = (2678 : Fin 2886) := Fin.ext h2678
    subst k
    rw [keyMomentRowsAt2678]
    exact keyMoment2678 B hB
  · have he : k = (2679 : Fin 2886) := Fin.ext h2679
    subst k
    rw [keyMomentRowsAt2679]
    exact keyMoment2679 B hB
  · have he : k = (2680 : Fin 2886) := Fin.ext h2680
    subst k
    rw [keyMomentRowsAt2680]
    exact keyMoment2680 B hB
  · have he : k = (2681 : Fin 2886) := Fin.ext h2681
    subst k
    rw [keyMomentRowsAt2681]
    exact keyMoment2681 B hB
  · have he : k = (2682 : Fin 2886) := Fin.ext h2682
    subst k
    rw [keyMomentRowsAt2682]
    exact keyMoment2682 B hB
  · have he : k = (2683 : Fin 2886) := Fin.ext h2683
    subst k
    rw [keyMomentRowsAt2683]
    exact keyMoment2683 B hB
  · have he : k = (2684 : Fin 2886) := Fin.ext h2684
    subst k
    rw [keyMomentRowsAt2684]
    exact keyMoment2684 B hB
  · have he : k = (2685 : Fin 2886) := Fin.ext h2685
    subst k
    rw [keyMomentRowsAt2685]
    exact keyMoment2685 B hB
  · have he : k = (2686 : Fin 2886) := Fin.ext h2686
    subst k
    rw [keyMomentRowsAt2686]
    exact keyMoment2686 B hB
  · have he : k = (2687 : Fin 2886) := Fin.ext h2687
    subst k
    rw [keyMomentRowsAt2687]
    exact keyMoment2687 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound83_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound83_e_oai
