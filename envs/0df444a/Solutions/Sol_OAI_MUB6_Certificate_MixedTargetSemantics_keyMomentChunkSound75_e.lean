-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound75_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:02:26.719253+00:00
-- url     : https://prove2.me/submissions/3d5b8f30-21f2-45d9-9beb-b5947b8b97cd

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical329
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical42112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42112 raw42112Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw42112 raw42112Labels = mixedMoment B raw42112step0 raw42112step0Labels := by
      have hz : ∀ j, raw42112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42112step0 = (fun i j => raw42112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42112step0 raw42112; decide +kernel
      have hl : raw42112step0Labels = raw42112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42112 raw42112Labels permutation434 hz
    mixedMoment B raw42112step0 raw42112step0Labels = mixedMoment B raw42112step1 raw42112step1Labels := by
      have hz : ∀ j, raw42112step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42112step1 = (fun i j => raw42112step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42112step1 raw42112step0; decide +kernel
      have hl : raw42112step1Labels = raw42112step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42112step0 raw42112step0Labels permutation80 hz
    mixedMoment B raw42112step1 raw42112step1Labels = mixedMoment B raw42112step2 raw42112step2Labels := by
      have ha : raw42112step2 = (fun i j => raw42112step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42112step2 raw42112step1; decide +kernel
      have hl : raw42112step2Labels = raw42112step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42112step1 raw42112step1Labels permutation31 permutation2
    mixedMoment B raw42112step2 raw42112step2Labels = mixedMoment B raw42112step3 raw42112step3Labels := by
      have ha : raw42112step3 = -raw42112step2 := by apply Matrix.ext; change ∀ i j, raw42112step3 i j = -(raw42112step2 i j); unfold raw42112step3 raw42112step2; decide +kernel
      have hl : raw42112step3Labels = raw42112step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42112step3 raw42112step3Labels = mixedMoment B raw42112step4 raw42112step4Labels := by
      have ha : raw42112step4 = raw42112step3 := by apply Matrix.ext; unfold raw42112step4 raw42112step3; decide +kernel
      have hl : raw42112step3Labels = labelEmbedding1 ∘ raw42112step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42112step3 raw42112step3Labels raw42112step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

theorem canonical42113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42113 raw42113Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw42113 raw42113Labels = mixedMoment B raw42113step0 raw42113step0Labels := by
      have hz : ∀ j, raw42113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42113step0 = (fun i j => raw42113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42113step0 raw42113; decide +kernel
      have hl : raw42113step0Labels = raw42113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42113 raw42113Labels permutation434 hz
    mixedMoment B raw42113step0 raw42113step0Labels = mixedMoment B raw42113step1 raw42113step1Labels := by
      have hz : ∀ j, raw42113step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42113step1 = (fun i j => raw42113step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42113step1 raw42113step0; decide +kernel
      have hl : raw42113step1Labels = raw42113step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42113step0 raw42113step0Labels permutation80 hz
    mixedMoment B raw42113step1 raw42113step1Labels = mixedMoment B raw42113step2 raw42113step2Labels := by
      have ha : raw42113step2 = (fun i j => raw42113step1 (permutation27 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42113step2 raw42113step1; decide +kernel
      have hl : raw42113step2Labels = raw42113step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42113step1 raw42113step1Labels permutation27 permutation7
    mixedMoment B raw42113step2 raw42113step2Labels = mixedMoment B raw42113step3 raw42113step3Labels := by
      have ha : raw42113step3 = raw42113step2 := by apply Matrix.ext; unfold raw42113step3 raw42113step2; decide +kernel
      have hl : raw42113step2Labels = labelEmbedding6 ∘ raw42113step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42113step2 raw42113step2Labels raw42113step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

theorem canonical42114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42114 raw42114Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw42114 raw42114Labels = mixedMoment B raw42114step0 raw42114step0Labels := by
      have hz : ∀ j, raw42114 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42114step0 = (fun i j => raw42114 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42114step0 raw42114; decide +kernel
      have hl : raw42114step0Labels = raw42114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42114 raw42114Labels permutation346 hz
    mixedMoment B raw42114step0 raw42114step0Labels = mixedMoment B raw42114step1 raw42114step1Labels := by
      have ha : raw42114step1 = (fun i j => raw42114step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42114step1 raw42114step0; decide +kernel
      have hl : raw42114step1Labels = raw42114step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42114step0 raw42114step0Labels permutation151 permutation2
    mixedMoment B raw42114step1 raw42114step1Labels = mixedMoment B raw42114step2 raw42114step2Labels := by
      have ha : raw42114step2 = -raw42114step1 := by apply Matrix.ext; change ∀ i j, raw42114step2 i j = -(raw42114step1 i j); unfold raw42114step2 raw42114step1; decide +kernel
      have hl : raw42114step2Labels = raw42114step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42114step2 raw42114step2Labels = mixedMoment B raw42114step3 raw42114step3Labels := by
      have ha : raw42114step3 = raw42114step2 := by apply Matrix.ext; unfold raw42114step3 raw42114step2; decide +kernel
      have hl : raw42114step2Labels = labelEmbedding1 ∘ raw42114step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42114step2 raw42114step2Labels raw42114step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

theorem canonical42115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42115 raw42115Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw42115 raw42115Labels = mixedMoment B raw42115step0 raw42115step0Labels := by
      have hz : ∀ j, raw42115 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42115step0 = (fun i j => raw42115 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42115step0 raw42115; decide +kernel
      have hl : raw42115step0Labels = raw42115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42115 raw42115Labels permutation346 hz
    mixedMoment B raw42115step0 raw42115step0Labels = mixedMoment B raw42115step1 raw42115step1Labels := by
      have ha : raw42115step1 = (fun i j => raw42115step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42115step1 raw42115step0; decide +kernel
      have hl : raw42115step1Labels = raw42115step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42115step0 raw42115step0Labels permutation147 permutation7
    mixedMoment B raw42115step1 raw42115step1Labels = mixedMoment B raw42115step2 raw42115step2Labels := by
      have ha : raw42115step2 = raw42115step1 := by apply Matrix.ext; unfold raw42115step2 raw42115step1; decide +kernel
      have hl : raw42115step1Labels = labelEmbedding6 ∘ raw42115step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42115step1 raw42115step1Labels raw42115step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical42116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42116 raw42116Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw42116 raw42116Labels = mixedMoment B raw42116step0 raw42116step0Labels := by
      have hz : ∀ j, raw42116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42116step0 = (fun i j => raw42116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42116step0 raw42116; decide +kernel
      have hl : raw42116step0Labels = raw42116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42116 raw42116Labels permutation346 hz
    mixedMoment B raw42116step0 raw42116step0Labels = mixedMoment B raw42116step1 raw42116step1Labels := by
      have ha : raw42116step1 = (fun i j => raw42116step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42116step1 raw42116step0; decide +kernel
      have hl : raw42116step1Labels = raw42116step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42116step0 raw42116step0Labels permutation139 permutation4
    mixedMoment B raw42116step1 raw42116step1Labels = mixedMoment B raw42116step2 raw42116step2Labels := by
      have ha : raw42116step2 = raw42116step1 := by apply Matrix.ext; unfold raw42116step2 raw42116step1; decide +kernel
      have hl : raw42116step1Labels = labelEmbedding1 ∘ raw42116step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42116step1 raw42116step1Labels raw42116step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

theorem canonical42117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42117 raw42117Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw42117 raw42117Labels = mixedMoment B raw42117step0 raw42117step0Labels := by
      have hz : ∀ j, raw42117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42117step0 = (fun i j => raw42117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42117step0 raw42117; decide +kernel
      have hl : raw42117step0Labels = raw42117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42117 raw42117Labels permutation346 hz
    mixedMoment B raw42117step0 raw42117step0Labels = mixedMoment B raw42117step1 raw42117step1Labels := by
      have ha : raw42117step1 = (fun i j => raw42117step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42117step1 raw42117step0; decide +kernel
      have hl : raw42117step1Labels = raw42117step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42117step0 raw42117step0Labels permutation40 permutation5
    mixedMoment B raw42117step1 raw42117step1Labels = mixedMoment B raw42117step2 raw42117step2Labels := by
      have ha : raw42117step2 = -raw42117step1 := by apply Matrix.ext; change ∀ i j, raw42117step2 i j = -(raw42117step1 i j); unfold raw42117step2 raw42117step1; decide +kernel
      have hl : raw42117step2Labels = raw42117step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42117step2 raw42117step2Labels = mixedMoment B raw42117step3 raw42117step3Labels := by
      have ha : raw42117step3 = raw42117step2 := by apply Matrix.ext; unfold raw42117step3 raw42117step2; decide +kernel
      have hl : raw42117step2Labels = labelEmbedding9 ∘ raw42117step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42117step2 raw42117step2Labels raw42117step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

theorem canonical42118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42118 raw42118Labels = mixedMoment B node4028 node4028Labels := by
  calc
    mixedMoment B raw42118 raw42118Labels = mixedMoment B raw42118step0 raw42118step0Labels := by
      have hz : ∀ j, raw42118 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42118step0 = (fun i j => raw42118 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42118step0 raw42118; decide +kernel
      have hl : raw42118step0Labels = raw42118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42118 raw42118Labels permutation346 hz
    mixedMoment B raw42118step0 raw42118step0Labels = mixedMoment B raw42118step1 raw42118step1Labels := by
      have ha : raw42118step1 = (fun i j => raw42118step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42118step1 raw42118step0; decide +kernel
      have hl : raw42118step1Labels = raw42118step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42118step0 raw42118step0Labels permutation35 permutation2
    mixedMoment B raw42118step1 raw42118step1Labels = mixedMoment B raw42118step2 raw42118step2Labels := by
      have ha : raw42118step2 = raw42118step1 := by apply Matrix.ext; unfold raw42118step2 raw42118step1; decide +kernel
      have hl : raw42118step1Labels = labelEmbedding1 ∘ raw42118step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42118step1 raw42118step1Labels raw42118step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4028 node4028Labels := by rfl

theorem canonical42119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42119 raw42119Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw42119 raw42119Labels = mixedMoment B raw42119step0 raw42119step0Labels := by
      have hz : ∀ j, raw42119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42119step0 = (fun i j => raw42119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42119step0 raw42119; decide +kernel
      have hl : raw42119step0Labels = raw42119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42119 raw42119Labels permutation346 hz
    mixedMoment B raw42119step0 raw42119step0Labels = mixedMoment B raw42119step1 raw42119step1Labels := by
      have ha : raw42119step1 = (fun i j => raw42119step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42119step1 raw42119step0; decide +kernel
      have hl : raw42119step1Labels = raw42119step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42119step0 raw42119step0Labels permutation32 permutation3
    mixedMoment B raw42119step1 raw42119step1Labels = mixedMoment B raw42119step2 raw42119step2Labels := by
      have ha : raw42119step2 = raw42119step1 := by apply Matrix.ext; unfold raw42119step2 raw42119step1; decide +kernel
      have hl : raw42119step1Labels = labelEmbedding7 ∘ raw42119step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42119step1 raw42119step1Labels raw42119step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

theorem canonical42120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42120 raw42120Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw42120 raw42120Labels = mixedMoment B raw42120step0 raw42120step0Labels := by
      have ha : raw42120step0 = (fun i j => raw42120 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42120step0 raw42120; decide +kernel
      have hl : raw42120step0Labels = raw42120Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42120 raw42120Labels permutation157 permutation2
    mixedMoment B raw42120step0 raw42120step0Labels = mixedMoment B raw42120step1 raw42120step1Labels := by
      have ha : raw42120step1 = raw42120step0 := by apply Matrix.ext; unfold raw42120step1 raw42120step0; decide +kernel
      have hl : raw42120step0Labels = labelEmbedding1 ∘ raw42120step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42120step0 raw42120step0Labels raw42120step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4024 node4024Labels := by rfl

theorem canonical42121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42121 raw42121Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw42121 raw42121Labels = mixedMoment B raw42121step0 raw42121step0Labels := by
      have ha : raw42121step0 = (fun i j => raw42121 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42121step0 raw42121; decide +kernel
      have hl : raw42121step0Labels = raw42121Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42121 raw42121Labels permutation152 permutation3
    mixedMoment B raw42121step0 raw42121step0Labels = mixedMoment B raw42121step1 raw42121step1Labels := by
      have ha : raw42121step1 = raw42121step0 := by apply Matrix.ext; unfold raw42121step1 raw42121step0; decide +kernel
      have hl : raw42121step0Labels = labelEmbedding7 ∘ raw42121step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42121step0 raw42121step0Labels raw42121step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical42122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42122 raw42122Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw42122 raw42122Labels = mixedMoment B raw42122step0 raw42122step0Labels := by
      have hz : ∀ j, raw42122 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42122step0 = (fun i j => raw42122 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42122step0 raw42122; decide +kernel
      have hl : raw42122step0Labels = raw42122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42122 raw42122Labels permutation434 hz
    mixedMoment B raw42122step0 raw42122step0Labels = mixedMoment B raw42122step1 raw42122step1Labels := by
      have ha : raw42122step1 = (fun i j => raw42122step0 (permutation73 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42122step1 raw42122step0; decide +kernel
      have hl : raw42122step1Labels = raw42122step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42122step0 raw42122step0Labels permutation73 permutation4
    mixedMoment B raw42122step1 raw42122step1Labels = mixedMoment B raw42122step2 raw42122step2Labels := by
      have ha : raw42122step2 = raw42122step1 := by apply Matrix.ext; unfold raw42122step2 raw42122step1; decide +kernel
      have hl : raw42122step1Labels = labelEmbedding1 ∘ raw42122step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42122step1 raw42122step1Labels raw42122step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical42123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42123 raw42123Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw42123 raw42123Labels = mixedMoment B raw42123step0 raw42123step0Labels := by
      have hz : ∀ j, raw42123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42123step0 = (fun i j => raw42123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42123step0 raw42123; decide +kernel
      have hl : raw42123step0Labels = raw42123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42123 raw42123Labels permutation434 hz
    mixedMoment B raw42123step0 raw42123step0Labels = mixedMoment B raw42123step1 raw42123step1Labels := by
      have ha : raw42123step1 = (fun i j => raw42123step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42123step1 raw42123step0; decide +kernel
      have hl : raw42123step1Labels = raw42123step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42123step0 raw42123step0Labels permutation68 permutation6
    mixedMoment B raw42123step1 raw42123step1Labels = mixedMoment B raw42123step2 raw42123step2Labels := by
      have ha : raw42123step2 = -raw42123step1 := by apply Matrix.ext; change ∀ i j, raw42123step2 i j = -(raw42123step1 i j); unfold raw42123step2 raw42123step1; decide +kernel
      have hl : raw42123step2Labels = raw42123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5267 node5267Labels := by rfl

theorem canonical42124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42124 raw42124Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw42124 raw42124Labels = mixedMoment B raw42124step0 raw42124step0Labels := by
      have ha : raw42124step0 = (fun i j => raw42124 (permutation343 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42124step0 raw42124; decide +kernel
      have hl : raw42124step0Labels = raw42124Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42124 raw42124Labels permutation343 permutation4
    mixedMoment B raw42124step0 raw42124step0Labels = mixedMoment B raw42124step1 raw42124step1Labels := by
      have ha : raw42124step1 = raw42124step0 := by apply Matrix.ext; unfold raw42124step1 raw42124step0; decide +kernel
      have hl : raw42124step0Labels = labelEmbedding1 ∘ raw42124step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42124step0 raw42124step0Labels raw42124step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

theorem canonical42125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42125 raw42125Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw42125 raw42125Labels = mixedMoment B raw42125step0 raw42125step0Labels := by
      have ha : raw42125step0 = (fun i j => raw42125 (permutation336 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42125step0 raw42125; decide +kernel
      have hl : raw42125step0Labels = raw42125Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42125 raw42125Labels permutation336 permutation6
    mixedMoment B raw42125step0 raw42125step0Labels = mixedMoment B raw42125step1 raw42125step1Labels := by
      have ha : raw42125step1 = -raw42125step0 := by apply Matrix.ext; change ∀ i j, raw42125step1 i j = -(raw42125step0 i j); unfold raw42125step1 raw42125step0; decide +kernel
      have hl : raw42125step1Labels = raw42125step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical42126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42126 raw42126Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw42126 raw42126Labels = mixedMoment B raw42126step0 raw42126step0Labels := by
      have hz : ∀ j, raw42126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42126step0 = (fun i j => raw42126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42126step0 raw42126; decide +kernel
      have hl : raw42126step0Labels = raw42126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42126 raw42126Labels permutation434 hz
    mixedMoment B raw42126step0 raw42126step0Labels = mixedMoment B raw42126step1 raw42126step1Labels := by
      have hz : ∀ j, raw42126step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42126step1 = (fun i j => raw42126step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42126step1 raw42126step0; decide +kernel
      have hl : raw42126step1Labels = raw42126step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42126step0 raw42126step0Labels permutation80 hz
    mixedMoment B raw42126step1 raw42126step1Labels = mixedMoment B raw42126step2 raw42126step2Labels := by
      have ha : raw42126step2 = (fun i j => raw42126step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42126step2 raw42126step1; decide +kernel
      have hl : raw42126step2Labels = raw42126step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42126step1 raw42126step1Labels permutation31 permutation2
    mixedMoment B raw42126step2 raw42126step2Labels = mixedMoment B raw42126step3 raw42126step3Labels := by
      have ha : raw42126step3 = -raw42126step2 := by apply Matrix.ext; change ∀ i j, raw42126step3 i j = -(raw42126step2 i j); unfold raw42126step3 raw42126step2; decide +kernel
      have hl : raw42126step3Labels = raw42126step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42126step3 raw42126step3Labels = mixedMoment B raw42126step4 raw42126step4Labels := by
      have ha : raw42126step4 = raw42126step3 := by apply Matrix.ext; unfold raw42126step4 raw42126step3; decide +kernel
      have hl : raw42126step3Labels = labelEmbedding1 ∘ raw42126step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42126step3 raw42126step3Labels raw42126step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3549 node3549Labels := by rfl

theorem canonical42127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42127 raw42127Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw42127 raw42127Labels = mixedMoment B raw42127step0 raw42127step0Labels := by
      have hz : ∀ j, raw42127 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42127step0 = (fun i j => raw42127 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42127step0 raw42127; decide +kernel
      have hl : raw42127step0Labels = raw42127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42127 raw42127Labels permutation434 hz
    mixedMoment B raw42127step0 raw42127step0Labels = mixedMoment B raw42127step1 raw42127step1Labels := by
      have hz : ∀ j, raw42127step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42127step1 = (fun i j => raw42127step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42127step1 raw42127step0; decide +kernel
      have hl : raw42127step1Labels = raw42127step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42127step0 raw42127step0Labels permutation80 hz
    mixedMoment B raw42127step1 raw42127step1Labels = mixedMoment B raw42127step2 raw42127step2Labels := by
      have ha : raw42127step2 = (fun i j => raw42127step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42127step2 raw42127step1; decide +kernel
      have hl : raw42127step2Labels = raw42127step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42127step1 raw42127step1Labels permutation16 permutation6
    mixedMoment B raw42127step2 raw42127step2Labels = mixedMoment B raw42127step3 raw42127step3Labels := by
      have ha : raw42127step3 = -raw42127step2 := by apply Matrix.ext; change ∀ i j, raw42127step3 i j = -(raw42127step2 i j); unfold raw42127step3 raw42127step2; decide +kernel
      have hl : raw42127step3Labels = raw42127step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5268 node5268Labels := by rfl

theorem canonical42128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42128 raw42128Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw42128 raw42128Labels = mixedMoment B raw42128step0 raw42128step0Labels := by
      have hz : ∀ j, raw42128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42128step0 = (fun i j => raw42128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42128step0 raw42128; decide +kernel
      have hl : raw42128step0Labels = raw42128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42128 raw42128Labels permutation346 hz
    mixedMoment B raw42128step0 raw42128step0Labels = mixedMoment B raw42128step1 raw42128step1Labels := by
      have ha : raw42128step1 = (fun i j => raw42128step0 (permutation79 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42128step1 raw42128step0; decide +kernel
      have hl : raw42128step1Labels = raw42128step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42128step0 raw42128step0Labels permutation79 permutation4
    mixedMoment B raw42128step1 raw42128step1Labels = mixedMoment B raw42128step2 raw42128step2Labels := by
      have ha : raw42128step2 = raw42128step1 := by apply Matrix.ext; unfold raw42128step2 raw42128step1; decide +kernel
      have hl : raw42128step1Labels = labelEmbedding1 ∘ raw42128step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42128step1 raw42128step1Labels raw42128step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

theorem canonical42129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42129 raw42129Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw42129 raw42129Labels = mixedMoment B raw42129step0 raw42129step0Labels := by
      have hz : ∀ j, raw42129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42129step0 = (fun i j => raw42129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42129step0 raw42129; decide +kernel
      have hl : raw42129step0Labels = raw42129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42129 raw42129Labels permutation346 hz
    mixedMoment B raw42129step0 raw42129step0Labels = mixedMoment B raw42129step1 raw42129step1Labels := by
      have ha : raw42129step1 = (fun i j => raw42129step0 (permutation75 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42129step1 raw42129step0; decide +kernel
      have hl : raw42129step1Labels = raw42129step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42129step0 raw42129step0Labels permutation75 permutation6
    mixedMoment B raw42129step1 raw42129step1Labels = mixedMoment B raw42129step2 raw42129step2Labels := by
      have ha : raw42129step2 = -raw42129step1 := by apply Matrix.ext; change ∀ i j, raw42129step2 i j = -(raw42129step1 i j); unfold raw42129step2 raw42129step1; decide +kernel
      have hl : raw42129step2Labels = raw42129step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical42130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42130 raw42130Labels = mixedMoment B node3231 node3231Labels := by
  calc
    mixedMoment B raw42130 raw42130Labels = mixedMoment B raw42130step0 raw42130step0Labels := by
      have hz : ∀ j, raw42130 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42130step0 = (fun i j => raw42130 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42130step0 raw42130; decide +kernel
      have hl : raw42130step0Labels = raw42130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42130 raw42130Labels permutation520 hz
    mixedMoment B raw42130step0 raw42130step0Labels = mixedMoment B raw42130step1 raw42130step1Labels := by
      have hz : ∀ j, raw42130step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42130step1 = (fun i j => raw42130step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42130step1 raw42130step0; decide +kernel
      have hl : raw42130step1Labels = raw42130step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42130step0 raw42130step0Labels permutation104 hz
    mixedMoment B raw42130step1 raw42130step1Labels = mixedMoment B raw42130step2 raw42130step2Labels := by
      have hz : ∀ j, raw42130step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw42130step2 = (fun i j => raw42130step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw42130step2 raw42130step1; decide +kernel
      have hl : raw42130step2Labels = raw42130step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42130step1 raw42130step1Labels permutation20 hz
    mixedMoment B raw42130step2 raw42130step2Labels = mixedMoment B raw42130step3 raw42130step3Labels := by
      have ha : raw42130step3 = (fun i j => raw42130step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42130step3 raw42130step2; decide +kernel
      have hl : raw42130step3Labels = raw42130step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42130step2 raw42130step2Labels permutation7 permutation2
    mixedMoment B raw42130step3 raw42130step3Labels = mixedMoment B raw42130step4 raw42130step4Labels := by
      have ha : raw42130step4 = -raw42130step3 := by apply Matrix.ext; change ∀ i j, raw42130step4 i j = -(raw42130step3 i j); unfold raw42130step4 raw42130step3; decide +kernel
      have hl : raw42130step4Labels = raw42130step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42130step4 raw42130step4Labels = mixedMoment B raw42130step5 raw42130step5Labels := by
      have ha : raw42130step5 = raw42130step4 := by apply Matrix.ext; unfold raw42130step5 raw42130step4; decide +kernel
      have hl : raw42130step4Labels = labelEmbedding1 ∘ raw42130step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42130step4 raw42130step4Labels raw42130step5Labels labelEmbedding1 hl
    _ = mixedMoment B node3231 node3231Labels := by rfl

theorem canonical42131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42131 raw42131Labels = mixedMoment B node4901 node4901Labels := by
  calc
    mixedMoment B raw42131 raw42131Labels = mixedMoment B raw42131step0 raw42131step0Labels := by
      have hz : ∀ j, raw42131 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42131step0 = (fun i j => raw42131 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42131step0 raw42131; decide +kernel
      have hl : raw42131step0Labels = raw42131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42131 raw42131Labels permutation520 hz
    mixedMoment B raw42131step0 raw42131step0Labels = mixedMoment B raw42131step1 raw42131step1Labels := by
      have hz : ∀ j, raw42131step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42131step1 = (fun i j => raw42131step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42131step1 raw42131step0; decide +kernel
      have hl : raw42131step1Labels = raw42131step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42131step0 raw42131step0Labels permutation104 hz
    mixedMoment B raw42131step1 raw42131step1Labels = mixedMoment B raw42131step2 raw42131step2Labels := by
      have hz : ∀ j, raw42131step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw42131step2 = (fun i j => raw42131step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw42131step2 raw42131step1; decide +kernel
      have hl : raw42131step2Labels = raw42131step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42131step1 raw42131step1Labels permutation20 hz
    mixedMoment B raw42131step2 raw42131step2Labels = mixedMoment B raw42131step3 raw42131step3Labels := by
      have ha : raw42131step3 = (fun i j => raw42131step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42131step3 raw42131step2; decide +kernel
      have hl : raw42131step3Labels = raw42131step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42131step2 raw42131step2Labels permutation7 permutation3
    mixedMoment B raw42131step3 raw42131step3Labels = mixedMoment B raw42131step4 raw42131step4Labels := by
      have ha : raw42131step4 = -raw42131step3 := by apply Matrix.ext; change ∀ i j, raw42131step4 i j = -(raw42131step3 i j); unfold raw42131step4 raw42131step3; decide +kernel
      have hl : raw42131step4Labels = raw42131step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42131step4 raw42131step4Labels = mixedMoment B raw42131step5 raw42131step5Labels := by
      have ha : raw42131step5 = raw42131step4 := by apply Matrix.ext; unfold raw42131step5 raw42131step4; decide +kernel
      have hl : raw42131step4Labels = labelEmbedding7 ∘ raw42131step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42131step4 raw42131step4Labels raw42131step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4901 node4901Labels := by rfl

theorem canonical42132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42132 raw42132Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw42132 raw42132Labels = mixedMoment B raw42132step0 raw42132step0Labels := by
      have hz : ∀ j, raw42132 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42132step0 = (fun i j => raw42132 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42132step0 raw42132; decide +kernel
      have hl : raw42132step0Labels = raw42132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42132 raw42132Labels permutation434 hz
    mixedMoment B raw42132step0 raw42132step0Labels = mixedMoment B raw42132step1 raw42132step1Labels := by
      have hz : ∀ j, raw42132step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42132step1 = (fun i j => raw42132step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42132step1 raw42132step0; decide +kernel
      have hl : raw42132step1Labels = raw42132step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42132step0 raw42132step0Labels permutation80 hz
    mixedMoment B raw42132step1 raw42132step1Labels = mixedMoment B raw42132step2 raw42132step2Labels := by
      have ha : raw42132step2 = (fun i j => raw42132step1 (permutation30 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42132step2 raw42132step1; decide +kernel
      have hl : raw42132step2Labels = raw42132step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42132step1 raw42132step1Labels permutation30 permutation4
    mixedMoment B raw42132step2 raw42132step2Labels = mixedMoment B raw42132step3 raw42132step3Labels := by
      have ha : raw42132step3 = raw42132step2 := by apply Matrix.ext; unfold raw42132step3 raw42132step2; decide +kernel
      have hl : raw42132step2Labels = labelEmbedding1 ∘ raw42132step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42132step2 raw42132step2Labels raw42132step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3110 node3110Labels := by rfl

theorem canonical42133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42133 raw42133Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw42133 raw42133Labels = mixedMoment B raw42133step0 raw42133step0Labels := by
      have hz : ∀ j, raw42133 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42133step0 = (fun i j => raw42133 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42133step0 raw42133; decide +kernel
      have hl : raw42133step0Labels = raw42133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42133 raw42133Labels permutation434 hz
    mixedMoment B raw42133step0 raw42133step0Labels = mixedMoment B raw42133step1 raw42133step1Labels := by
      have hz : ∀ j, raw42133step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42133step1 = (fun i j => raw42133step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42133step1 raw42133step0; decide +kernel
      have hl : raw42133step1Labels = raw42133step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42133step0 raw42133step0Labels permutation80 hz
    mixedMoment B raw42133step1 raw42133step1Labels = mixedMoment B raw42133step2 raw42133step2Labels := by
      have ha : raw42133step2 = (fun i j => raw42133step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42133step2 raw42133step1; decide +kernel
      have hl : raw42133step2Labels = raw42133step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42133step1 raw42133step1Labels permutation30 permutation5
    mixedMoment B raw42133step2 raw42133step2Labels = mixedMoment B raw42133step3 raw42133step3Labels := by
      have ha : raw42133step3 = raw42133step2 := by apply Matrix.ext; unfold raw42133step3 raw42133step2; decide +kernel
      have hl : raw42133step2Labels = labelEmbedding9 ∘ raw42133step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42133step2 raw42133step2Labels raw42133step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical42134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42134 raw42134Labels = mixedMoment B node4006 node4006Labels := by
  calc
    mixedMoment B raw42134 raw42134Labels = mixedMoment B raw42134step0 raw42134step0Labels := by
      have hz : ∀ j, raw42134 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42134step0 = (fun i j => raw42134 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42134step0 raw42134; decide +kernel
      have hl : raw42134step0Labels = raw42134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42134 raw42134Labels permutation434 hz
    mixedMoment B raw42134step0 raw42134step0Labels = mixedMoment B raw42134step1 raw42134step1Labels := by
      have hz : ∀ j, raw42134step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42134step1 = (fun i j => raw42134step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42134step1 raw42134step0; decide +kernel
      have hl : raw42134step1Labels = raw42134step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42134step0 raw42134step0Labels permutation80 hz
    mixedMoment B raw42134step1 raw42134step1Labels = mixedMoment B raw42134step2 raw42134step2Labels := by
      have ha : raw42134step2 = raw42134step1 := by apply Matrix.ext; unfold raw42134step2 raw42134step1; decide +kernel
      have hl : raw42134step1Labels = labelEmbedding1 ∘ raw42134step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42134step1 raw42134step1Labels raw42134step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4006 node4006Labels := by rfl

theorem canonical42135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42135 raw42135Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw42135 raw42135Labels = mixedMoment B raw42135step0 raw42135step0Labels := by
      have hz : ∀ j, raw42135 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42135step0 = (fun i j => raw42135 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42135step0 raw42135; decide +kernel
      have hl : raw42135step0Labels = raw42135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42135 raw42135Labels permutation434 hz
    mixedMoment B raw42135step0 raw42135step0Labels = mixedMoment B raw42135step1 raw42135step1Labels := by
      have hz : ∀ j, raw42135step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42135step1 = (fun i j => raw42135step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42135step1 raw42135step0; decide +kernel
      have hl : raw42135step1Labels = raw42135step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42135step0 raw42135step0Labels permutation80 hz
    mixedMoment B raw42135step1 raw42135step1Labels = mixedMoment B raw42135step2 raw42135step2Labels := by
      have ha : raw42135step2 = (fun i j => raw42135step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42135step2 raw42135step1; decide +kernel
      have hl : raw42135step2Labels = raw42135step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42135step1 raw42135step1Labels permutation31 permutation3
    mixedMoment B raw42135step2 raw42135step2Labels = mixedMoment B raw42135step3 raw42135step3Labels := by
      have ha : raw42135step3 = -raw42135step2 := by apply Matrix.ext; change ∀ i j, raw42135step3 i j = -(raw42135step2 i j); unfold raw42135step3 raw42135step2; decide +kernel
      have hl : raw42135step3Labels = raw42135step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42135step3 raw42135step3Labels = mixedMoment B raw42135step4 raw42135step4Labels := by
      have ha : raw42135step4 = raw42135step3 := by apply Matrix.ext; unfold raw42135step4 raw42135step3; decide +kernel
      have hl : raw42135step3Labels = labelEmbedding7 ∘ raw42135step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42135step3 raw42135step3Labels raw42135step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5413 node5413Labels := by rfl

theorem canonical42136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42136 raw42136Labels = mixedMoment B node4004 node4004Labels := by
  calc
    mixedMoment B raw42136 raw42136Labels = mixedMoment B raw42136step0 raw42136step0Labels := by
      have hz : ∀ j, raw42136 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42136step0 = (fun i j => raw42136 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42136step0 raw42136; decide +kernel
      have hl : raw42136step0Labels = raw42136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42136 raw42136Labels permutation434 hz
    mixedMoment B raw42136step0 raw42136step0Labels = mixedMoment B raw42136step1 raw42136step1Labels := by
      have hz : ∀ j, raw42136step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42136step1 = (fun i j => raw42136step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42136step1 raw42136step0; decide +kernel
      have hl : raw42136step1Labels = raw42136step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42136step0 raw42136step0Labels permutation80 hz
    mixedMoment B raw42136step1 raw42136step1Labels = mixedMoment B raw42136step2 raw42136step2Labels := by
      have ha : raw42136step2 = raw42136step1 := by apply Matrix.ext; unfold raw42136step2 raw42136step1; decide +kernel
      have hl : raw42136step1Labels = labelEmbedding1 ∘ raw42136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42136step1 raw42136step1Labels raw42136step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4004 node4004Labels := by rfl

theorem canonical42137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42137 raw42137Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw42137 raw42137Labels = mixedMoment B raw42137step0 raw42137step0Labels := by
      have hz : ∀ j, raw42137 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42137step0 = (fun i j => raw42137 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42137step0 raw42137; decide +kernel
      have hl : raw42137step0Labels = raw42137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42137 raw42137Labels permutation434 hz
    mixedMoment B raw42137step0 raw42137step0Labels = mixedMoment B raw42137step1 raw42137step1Labels := by
      have hz : ∀ j, raw42137step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42137step1 = (fun i j => raw42137step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42137step1 raw42137step0; decide +kernel
      have hl : raw42137step1Labels = raw42137step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42137step0 raw42137step0Labels permutation80 hz
    mixedMoment B raw42137step1 raw42137step1Labels = mixedMoment B raw42137step2 raw42137step2Labels := by
      have ha : raw42137step2 = (fun i j => raw42137step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42137step2 raw42137step1; decide +kernel
      have hl : raw42137step2Labels = raw42137step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42137step1 raw42137step1Labels permutation8 permutation3
    mixedMoment B raw42137step2 raw42137step2Labels = mixedMoment B raw42137step3 raw42137step3Labels := by
      have ha : raw42137step3 = raw42137step2 := by apply Matrix.ext; unfold raw42137step3 raw42137step2; decide +kernel
      have hl : raw42137step2Labels = labelEmbedding7 ∘ raw42137step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42137step2 raw42137step2Labels raw42137step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5475 node5475Labels := by rfl

theorem canonical42138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42138 raw42138Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw42138 raw42138Labels = mixedMoment B raw42138step0 raw42138step0Labels := by
      have hz : ∀ j, raw42138 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42138step0 = (fun i j => raw42138 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42138step0 raw42138; decide +kernel
      have hl : raw42138step0Labels = raw42138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42138 raw42138Labels permutation434 hz
    mixedMoment B raw42138step0 raw42138step0Labels = mixedMoment B raw42138step1 raw42138step1Labels := by
      have hz : ∀ j, raw42138step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42138step1 = (fun i j => raw42138step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42138step1 raw42138step0; decide +kernel
      have hl : raw42138step1Labels = raw42138step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42138step0 raw42138step0Labels permutation80 hz
    mixedMoment B raw42138step1 raw42138step1Labels = mixedMoment B raw42138step2 raw42138step2Labels := by
      have ha : raw42138step2 = (fun i j => raw42138step1 (permutation24 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42138step2 raw42138step1; decide +kernel
      have hl : raw42138step2Labels = raw42138step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42138step1 raw42138step1Labels permutation24 permutation4
    mixedMoment B raw42138step2 raw42138step2Labels = mixedMoment B raw42138step3 raw42138step3Labels := by
      have ha : raw42138step3 = raw42138step2 := by apply Matrix.ext; unfold raw42138step3 raw42138step2; decide +kernel
      have hl : raw42138step2Labels = labelEmbedding1 ∘ raw42138step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42138step2 raw42138step2Labels raw42138step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2774 node2774Labels := by rfl

theorem canonical42139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42139 raw42139Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw42139 raw42139Labels = mixedMoment B raw42139step0 raw42139step0Labels := by
      have hz : ∀ j, raw42139 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42139step0 = (fun i j => raw42139 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42139step0 raw42139; decide +kernel
      have hl : raw42139step0Labels = raw42139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42139 raw42139Labels permutation434 hz
    mixedMoment B raw42139step0 raw42139step0Labels = mixedMoment B raw42139step1 raw42139step1Labels := by
      have hz : ∀ j, raw42139step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42139step1 = (fun i j => raw42139step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42139step1 raw42139step0; decide +kernel
      have hl : raw42139step1Labels = raw42139step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42139step0 raw42139step0Labels permutation80 hz
    mixedMoment B raw42139step1 raw42139step1Labels = mixedMoment B raw42139step2 raw42139step2Labels := by
      have ha : raw42139step2 = (fun i j => raw42139step1 (permutation24 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42139step2 raw42139step1; decide +kernel
      have hl : raw42139step2Labels = raw42139step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42139step1 raw42139step1Labels permutation24 permutation4
    mixedMoment B raw42139step2 raw42139step2Labels = mixedMoment B raw42139step3 raw42139step3Labels := by
      have ha : raw42139step3 = raw42139step2 := by apply Matrix.ext; unfold raw42139step3 raw42139step2; decide +kernel
      have hl : raw42139step2Labels = labelEmbedding10 ∘ raw42139step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42139step2 raw42139step2Labels raw42139step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

theorem canonical42140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42140 raw42140Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw42140 raw42140Labels = mixedMoment B raw42140step0 raw42140step0Labels := by
      have hz : ∀ j, raw42140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42140step0 = (fun i j => raw42140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42140step0 raw42140; decide +kernel
      have hl : raw42140step0Labels = raw42140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42140 raw42140Labels permutation346 hz
    mixedMoment B raw42140step0 raw42140step0Labels = mixedMoment B raw42140step1 raw42140step1Labels := by
      have ha : raw42140step1 = raw42140step0 := by apply Matrix.ext; unfold raw42140step1 raw42140step0; decide +kernel
      have hl : raw42140step0Labels = labelEmbedding1 ∘ raw42140step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42140step0 raw42140step0Labels raw42140step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4003 node4003Labels := by rfl

theorem canonical42141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42141 raw42141Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw42141 raw42141Labels = mixedMoment B raw42141step0 raw42141step0Labels := by
      have hz : ∀ j, raw42141 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42141step0 = (fun i j => raw42141 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42141step0 raw42141; decide +kernel
      have hl : raw42141step0Labels = raw42141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42141 raw42141Labels permutation346 hz
    mixedMoment B raw42141step0 raw42141step0Labels = mixedMoment B raw42141step1 raw42141step1Labels := by
      have ha : raw42141step1 = (fun i j => raw42141step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42141step1 raw42141step0; decide +kernel
      have hl : raw42141step1Labels = raw42141step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42141step0 raw42141step0Labels permutation151 permutation3
    mixedMoment B raw42141step1 raw42141step1Labels = mixedMoment B raw42141step2 raw42141step2Labels := by
      have ha : raw42141step2 = -raw42141step1 := by apply Matrix.ext; change ∀ i j, raw42141step2 i j = -(raw42141step1 i j); unfold raw42141step2 raw42141step1; decide +kernel
      have hl : raw42141step2Labels = raw42141step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42141step2 raw42141step2Labels = mixedMoment B raw42141step3 raw42141step3Labels := by
      have ha : raw42141step3 = raw42141step2 := by apply Matrix.ext; unfold raw42141step3 raw42141step2; decide +kernel
      have hl : raw42141step2Labels = labelEmbedding7 ∘ raw42141step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42141step2 raw42141step2Labels raw42141step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical42142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42142 raw42142Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw42142 raw42142Labels = mixedMoment B raw42142step0 raw42142step0Labels := by
      have hz : ∀ j, raw42142 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42142step0 = (fun i j => raw42142 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42142step0 raw42142; decide +kernel
      have hl : raw42142step0Labels = raw42142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42142 raw42142Labels permutation346 hz
    mixedMoment B raw42142step0 raw42142step0Labels = mixedMoment B raw42142step1 raw42142step1Labels := by
      have ha : raw42142step1 = (fun i j => raw42142step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42142step1 raw42142step0; decide +kernel
      have hl : raw42142step1Labels = raw42142step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42142step0 raw42142step0Labels permutation151 permutation2
    mixedMoment B raw42142step1 raw42142step1Labels = mixedMoment B raw42142step2 raw42142step2Labels := by
      have ha : raw42142step2 = -raw42142step1 := by apply Matrix.ext; change ∀ i j, raw42142step2 i j = -(raw42142step1 i j); unfold raw42142step2 raw42142step1; decide +kernel
      have hl : raw42142step2Labels = raw42142step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42142step2 raw42142step2Labels = mixedMoment B raw42142step3 raw42142step3Labels := by
      have ha : raw42142step3 = raw42142step2 := by apply Matrix.ext; unfold raw42142step3 raw42142step2; decide +kernel
      have hl : raw42142step2Labels = labelEmbedding1 ∘ raw42142step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42142step2 raw42142step2Labels raw42142step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3995 node3995Labels := by rfl

theorem canonical42143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42143 raw42143Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw42143 raw42143Labels = mixedMoment B raw42143step0 raw42143step0Labels := by
      have hz : ∀ j, raw42143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42143step0 = (fun i j => raw42143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42143step0 raw42143; decide +kernel
      have hl : raw42143step0Labels = raw42143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42143 raw42143Labels permutation346 hz
    mixedMoment B raw42143step0 raw42143step0Labels = mixedMoment B raw42143step1 raw42143step1Labels := by
      have ha : raw42143step1 = (fun i j => raw42143step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42143step1 raw42143step0; decide +kernel
      have hl : raw42143step1Labels = raw42143step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42143step0 raw42143step0Labels permutation32 permutation3
    mixedMoment B raw42143step1 raw42143step1Labels = mixedMoment B raw42143step2 raw42143step2Labels := by
      have ha : raw42143step2 = raw42143step1 := by apply Matrix.ext; unfold raw42143step2 raw42143step1; decide +kernel
      have hl : raw42143step1Labels = labelEmbedding7 ∘ raw42143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42143step1 raw42143step1Labels raw42143step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical42144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42144 raw42144Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw42144 raw42144Labels = mixedMoment B raw42144step0 raw42144step0Labels := by
      have hz : ∀ j, raw42144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42144step0 = (fun i j => raw42144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42144step0 raw42144; decide +kernel
      have hl : raw42144step0Labels = raw42144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42144 raw42144Labels permutation346 hz
    mixedMoment B raw42144step0 raw42144step0Labels = mixedMoment B raw42144step1 raw42144step1Labels := by
      have ha : raw42144step1 = (fun i j => raw42144step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42144step1 raw42144step0; decide +kernel
      have hl : raw42144step1Labels = raw42144step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42144step0 raw42144step0Labels permutation151 permutation2
    mixedMoment B raw42144step1 raw42144step1Labels = mixedMoment B raw42144step2 raw42144step2Labels := by
      have ha : raw42144step2 = -raw42144step1 := by apply Matrix.ext; change ∀ i j, raw42144step2 i j = -(raw42144step1 i j); unfold raw42144step2 raw42144step1; decide +kernel
      have hl : raw42144step2Labels = raw42144step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42144step2 raw42144step2Labels = mixedMoment B raw42144step3 raw42144step3Labels := by
      have ha : raw42144step3 = raw42144step2 := by apply Matrix.ext; unfold raw42144step3 raw42144step2; decide +kernel
      have hl : raw42144step2Labels = labelEmbedding1 ∘ raw42144step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42144step2 raw42144step2Labels raw42144step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

theorem canonical42145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42145 raw42145Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw42145 raw42145Labels = mixedMoment B raw42145step0 raw42145step0Labels := by
      have hz : ∀ j, raw42145 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42145step0 = (fun i j => raw42145 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42145step0 raw42145; decide +kernel
      have hl : raw42145step0Labels = raw42145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42145 raw42145Labels permutation346 hz
    mixedMoment B raw42145step0 raw42145step0Labels = mixedMoment B raw42145step1 raw42145step1Labels := by
      have ha : raw42145step1 = (fun i j => raw42145step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42145step1 raw42145step0; decide +kernel
      have hl : raw42145step1Labels = raw42145step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42145step0 raw42145step0Labels permutation151 permutation2
    mixedMoment B raw42145step1 raw42145step1Labels = mixedMoment B raw42145step2 raw42145step2Labels := by
      have ha : raw42145step2 = -raw42145step1 := by apply Matrix.ext; change ∀ i j, raw42145step2 i j = -(raw42145step1 i j); unfold raw42145step2 raw42145step1; decide +kernel
      have hl : raw42145step2Labels = raw42145step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42145step2 raw42145step2Labels = mixedMoment B raw42145step3 raw42145step3Labels := by
      have ha : raw42145step3 = raw42145step2 := by apply Matrix.ext; unfold raw42145step3 raw42145step2; decide +kernel
      have hl : raw42145step2Labels = labelEmbedding8 ∘ raw42145step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42145step2 raw42145step2Labels raw42145step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

theorem canonical42146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42146 raw42146Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw42146 raw42146Labels = mixedMoment B raw42146step0 raw42146step0Labels := by
      have hz : ∀ j, raw42146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42146step0 = (fun i j => raw42146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42146step0 raw42146; decide +kernel
      have hl : raw42146step0Labels = raw42146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42146 raw42146Labels permutation346 hz
    mixedMoment B raw42146step0 raw42146step0Labels = mixedMoment B raw42146step1 raw42146step1Labels := by
      have ha : raw42146step1 = (fun i j => raw42146step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42146step1 raw42146step0; decide +kernel
      have hl : raw42146step1Labels = raw42146step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42146step0 raw42146step0Labels permutation151 permutation2
    mixedMoment B raw42146step1 raw42146step1Labels = mixedMoment B raw42146step2 raw42146step2Labels := by
      have ha : raw42146step2 = -raw42146step1 := by apply Matrix.ext; change ∀ i j, raw42146step2 i j = -(raw42146step1 i j); unfold raw42146step2 raw42146step1; decide +kernel
      have hl : raw42146step2Labels = raw42146step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42146step2 raw42146step2Labels = mixedMoment B raw42146step3 raw42146step3Labels := by
      have ha : raw42146step3 = raw42146step2 := by apply Matrix.ext; unfold raw42146step3 raw42146step2; decide +kernel
      have hl : raw42146step2Labels = labelEmbedding1 ∘ raw42146step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42146step2 raw42146step2Labels raw42146step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3854 node3854Labels := by rfl

theorem canonical42147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42147 raw42147Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw42147 raw42147Labels = mixedMoment B raw42147step0 raw42147step0Labels := by
      have hz : ∀ j, raw42147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42147step0 = (fun i j => raw42147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42147step0 raw42147; decide +kernel
      have hl : raw42147step0Labels = raw42147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42147 raw42147Labels permutation346 hz
    mixedMoment B raw42147step0 raw42147step0Labels = mixedMoment B raw42147step1 raw42147step1Labels := by
      have ha : raw42147step1 = (fun i j => raw42147step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42147step1 raw42147step0; decide +kernel
      have hl : raw42147step1Labels = raw42147step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42147step0 raw42147step0Labels permutation151 permutation2
    mixedMoment B raw42147step1 raw42147step1Labels = mixedMoment B raw42147step2 raw42147step2Labels := by
      have ha : raw42147step2 = -raw42147step1 := by apply Matrix.ext; change ∀ i j, raw42147step2 i j = -(raw42147step1 i j); unfold raw42147step2 raw42147step1; decide +kernel
      have hl : raw42147step2Labels = raw42147step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42147step2 raw42147step2Labels = mixedMoment B raw42147step3 raw42147step3Labels := by
      have ha : raw42147step3 = raw42147step2 := by apply Matrix.ext; unfold raw42147step3 raw42147step2; decide +kernel
      have hl : raw42147step2Labels = labelEmbedding8 ∘ raw42147step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42147step2 raw42147step2Labels raw42147step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

theorem canonical42148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42148 raw42148Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw42148 raw42148Labels = mixedMoment B raw42148step0 raw42148step0Labels := by
      have hz : ∀ j, raw42148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42148step0 = (fun i j => raw42148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42148step0 raw42148; decide +kernel
      have hl : raw42148step0Labels = raw42148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42148 raw42148Labels permutation346 hz
    mixedMoment B raw42148step0 raw42148step0Labels = mixedMoment B raw42148step1 raw42148step1Labels := by
      have ha : raw42148step1 = (fun i j => raw42148step0 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42148step1 raw42148step0; decide +kernel
      have hl : raw42148step1Labels = raw42148step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42148step0 raw42148step0Labels permutation144 permutation4
    mixedMoment B raw42148step1 raw42148step1Labels = mixedMoment B raw42148step2 raw42148step2Labels := by
      have ha : raw42148step2 = raw42148step1 := by apply Matrix.ext; unfold raw42148step2 raw42148step1; decide +kernel
      have hl : raw42148step1Labels = labelEmbedding1 ∘ raw42148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42148step1 raw42148step1Labels raw42148step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2751 node2751Labels := by rfl

theorem canonical42149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42149 raw42149Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw42149 raw42149Labels = mixedMoment B raw42149step0 raw42149step0Labels := by
      have hz : ∀ j, raw42149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42149step0 = (fun i j => raw42149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42149step0 raw42149; decide +kernel
      have hl : raw42149step0Labels = raw42149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42149 raw42149Labels permutation346 hz
    mixedMoment B raw42149step0 raw42149step0Labels = mixedMoment B raw42149step1 raw42149step1Labels := by
      have ha : raw42149step1 = (fun i j => raw42149step0 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42149step1 raw42149step0; decide +kernel
      have hl : raw42149step1Labels = raw42149step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42149step0 raw42149step0Labels permutation144 permutation4
    mixedMoment B raw42149step1 raw42149step1Labels = mixedMoment B raw42149step2 raw42149step2Labels := by
      have ha : raw42149step2 = raw42149step1 := by apply Matrix.ext; unfold raw42149step2 raw42149step1; decide +kernel
      have hl : raw42149step1Labels = labelEmbedding10 ∘ raw42149step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42149step1 raw42149step1Labels raw42149step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

theorem canonical42150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42150 raw42150Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw42150 raw42150Labels = mixedMoment B raw42150step0 raw42150step0Labels := by
      have hz : ∀ j, raw42150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42150step0 = (fun i j => raw42150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42150step0 raw42150; decide +kernel
      have hl : raw42150step0Labels = raw42150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42150 raw42150Labels permutation346 hz
    mixedMoment B raw42150step0 raw42150step0Labels = mixedMoment B raw42150step1 raw42150step1Labels := by
      have ha : raw42150step1 = (fun i j => raw42150step0 (permutation150 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42150step1 raw42150step0; decide +kernel
      have hl : raw42150step1Labels = raw42150step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42150step0 raw42150step0Labels permutation150 permutation4
    mixedMoment B raw42150step1 raw42150step1Labels = mixedMoment B raw42150step2 raw42150step2Labels := by
      have ha : raw42150step2 = raw42150step1 := by apply Matrix.ext; unfold raw42150step2 raw42150step1; decide +kernel
      have hl : raw42150step1Labels = labelEmbedding1 ∘ raw42150step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42150step1 raw42150step1Labels raw42150step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3995 node3995Labels := by rfl

theorem canonical42151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42151 raw42151Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw42151 raw42151Labels = mixedMoment B raw42151step0 raw42151step0Labels := by
      have hz : ∀ j, raw42151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42151step0 = (fun i j => raw42151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42151step0 raw42151; decide +kernel
      have hl : raw42151step0Labels = raw42151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42151 raw42151Labels permutation346 hz
    mixedMoment B raw42151step0 raw42151step0Labels = mixedMoment B raw42151step1 raw42151step1Labels := by
      have ha : raw42151step1 = (fun i j => raw42151step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42151step1 raw42151step0; decide +kernel
      have hl : raw42151step1Labels = raw42151step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42151step0 raw42151step0Labels permutation56 permutation5
    mixedMoment B raw42151step1 raw42151step1Labels = mixedMoment B raw42151step2 raw42151step2Labels := by
      have ha : raw42151step2 = -raw42151step1 := by apply Matrix.ext; change ∀ i j, raw42151step2 i j = -(raw42151step1 i j); unfold raw42151step2 raw42151step1; decide +kernel
      have hl : raw42151step2Labels = raw42151step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42151step2 raw42151step2Labels = mixedMoment B raw42151step3 raw42151step3Labels := by
      have ha : raw42151step3 = raw42151step2 := by apply Matrix.ext; unfold raw42151step3 raw42151step2; decide +kernel
      have hl : raw42151step2Labels = labelEmbedding9 ∘ raw42151step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42151step2 raw42151step2Labels raw42151step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical42152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42152 raw42152Labels = mixedMoment B node4005 node4005Labels := by
  calc
    mixedMoment B raw42152 raw42152Labels = mixedMoment B raw42152step0 raw42152step0Labels := by
      have hz : ∀ j, raw42152 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42152step0 = (fun i j => raw42152 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42152step0 raw42152; decide +kernel
      have hl : raw42152step0Labels = raw42152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42152 raw42152Labels permutation346 hz
    mixedMoment B raw42152step0 raw42152step0Labels = mixedMoment B raw42152step1 raw42152step1Labels := by
      have ha : raw42152step1 = raw42152step0 := by apply Matrix.ext; unfold raw42152step1 raw42152step0; decide +kernel
      have hl : raw42152step0Labels = labelEmbedding1 ∘ raw42152step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42152step0 raw42152step0Labels raw42152step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4005 node4005Labels := by rfl

theorem canonical42153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42153 raw42153Labels = mixedMoment B node5474 node5474Labels := by
  calc
    mixedMoment B raw42153 raw42153Labels = mixedMoment B raw42153step0 raw42153step0Labels := by
      have hz : ∀ j, raw42153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42153step0 = (fun i j => raw42153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42153step0 raw42153; decide +kernel
      have hl : raw42153step0Labels = raw42153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42153 raw42153Labels permutation346 hz
    mixedMoment B raw42153step0 raw42153step0Labels = mixedMoment B raw42153step1 raw42153step1Labels := by
      have ha : raw42153step1 = (fun i j => raw42153step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42153step1 raw42153step0; decide +kernel
      have hl : raw42153step1Labels = raw42153step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42153step0 raw42153step0Labels permutation32 permutation3
    mixedMoment B raw42153step1 raw42153step1Labels = mixedMoment B raw42153step2 raw42153step2Labels := by
      have ha : raw42153step2 = raw42153step1 := by apply Matrix.ext; unfold raw42153step2 raw42153step1; decide +kernel
      have hl : raw42153step1Labels = labelEmbedding7 ∘ raw42153step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42153step1 raw42153step1Labels raw42153step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5474 node5474Labels := by rfl

theorem canonical42154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42154 raw42154Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw42154 raw42154Labels = mixedMoment B raw42154step0 raw42154step0Labels := by
      have ha : raw42154step0 = (fun i j => raw42154 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42154step0 raw42154; decide +kernel
      have hl : raw42154step0Labels = raw42154Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42154 raw42154Labels permutation682 permutation2
    mixedMoment B raw42154step0 raw42154step0Labels = mixedMoment B raw42154step1 raw42154step1Labels := by
      have ha : raw42154step1 = -raw42154step0 := by apply Matrix.ext; change ∀ i j, raw42154step1 i j = -(raw42154step0 i j); unfold raw42154step1 raw42154step0; decide +kernel
      have hl : raw42154step1Labels = raw42154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42154step1 raw42154step1Labels = mixedMoment B raw42154step2 raw42154step2Labels := by
      have ha : raw42154step2 = raw42154step1 := by apply Matrix.ext; unfold raw42154step2 raw42154step1; decide +kernel
      have hl : raw42154step1Labels = labelEmbedding1 ∘ raw42154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42154step1 raw42154step1Labels raw42154step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

theorem canonical42155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42155 raw42155Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42155 raw42155Labels = mixedMoment B raw42155step0 raw42155step0Labels := by
      have ha : raw42155step0 = (fun i j => raw42155 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42155step0 raw42155; decide +kernel
      have hl : raw42155step0Labels = raw42155Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42155 raw42155Labels permutation682 permutation2
    mixedMoment B raw42155step0 raw42155step0Labels = mixedMoment B raw42155step1 raw42155step1Labels := by
      have ha : raw42155step1 = -raw42155step0 := by apply Matrix.ext; change ∀ i j, raw42155step1 i j = -(raw42155step0 i j); unfold raw42155step1 raw42155step0; decide +kernel
      have hl : raw42155step1Labels = raw42155step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42155step1 raw42155step1Labels = mixedMoment B raw42155step2 raw42155step2Labels := by
      have ha : raw42155step2 = raw42155step1 := by apply Matrix.ext; unfold raw42155step2 raw42155step1; decide +kernel
      have hl : raw42155step1Labels = labelEmbedding8 ∘ raw42155step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42155step1 raw42155step1Labels raw42155step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical42156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42156 raw42156Labels = mixedMoment B node3976 node3976Labels := by
  calc
    mixedMoment B raw42156 raw42156Labels = mixedMoment B raw42156step0 raw42156step0Labels := by
      have ha : raw42156step0 = (fun i j => raw42156 (permutation639 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42156step0 raw42156; decide +kernel
      have hl : raw42156step0Labels = raw42156Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42156 raw42156Labels permutation639 permutation4
    mixedMoment B raw42156step0 raw42156step0Labels = mixedMoment B raw42156step1 raw42156step1Labels := by
      have ha : raw42156step1 = raw42156step0 := by apply Matrix.ext; unfold raw42156step1 raw42156step0; decide +kernel
      have hl : raw42156step0Labels = labelEmbedding1 ∘ raw42156step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42156step0 raw42156step0Labels raw42156step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3976 node3976Labels := by rfl

theorem canonical42157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42157 raw42157Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw42157 raw42157Labels = mixedMoment B raw42157step0 raw42157step0Labels := by
      have ha : raw42157step0 = (fun i j => raw42157 (permutation273 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42157step0 raw42157; decide +kernel
      have hl : raw42157step0Labels = raw42157Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42157 raw42157Labels permutation273 permutation5
    mixedMoment B raw42157step0 raw42157step0Labels = mixedMoment B raw42157step1 raw42157step1Labels := by
      have ha : raw42157step1 = -raw42157step0 := by apply Matrix.ext; change ∀ i j, raw42157step1 i j = -(raw42157step0 i j); unfold raw42157step1 raw42157step0; decide +kernel
      have hl : raw42157step1Labels = raw42157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42157step1 raw42157step1Labels = mixedMoment B raw42157step2 raw42157step2Labels := by
      have ha : raw42157step2 = raw42157step1 := by apply Matrix.ext; unfold raw42157step2 raw42157step1; decide +kernel
      have hl : raw42157step1Labels = labelEmbedding9 ∘ raw42157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42157step1 raw42157step1Labels raw42157step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5471 node5471Labels := by rfl

theorem canonical42158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42158 raw42158Labels = mixedMoment B node4002 node4002Labels := by
  calc
    mixedMoment B raw42158 raw42158Labels = mixedMoment B raw42158step0 raw42158step0Labels := by
      have ha : raw42158step0 = (fun i j => raw42158 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42158step0 raw42158; decide +kernel
      have hl : raw42158step0Labels = raw42158Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42158 raw42158Labels permutation155 permutation2
    mixedMoment B raw42158step0 raw42158step0Labels = mixedMoment B raw42158step1 raw42158step1Labels := by
      have ha : raw42158step1 = raw42158step0 := by apply Matrix.ext; unfold raw42158step1 raw42158step0; decide +kernel
      have hl : raw42158step0Labels = labelEmbedding1 ∘ raw42158step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42158step0 raw42158step0Labels raw42158step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4002 node4002Labels := by rfl

theorem canonical42159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42159 raw42159Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw42159 raw42159Labels = mixedMoment B raw42159step0 raw42159step0Labels := by
      have ha : raw42159step0 = (fun i j => raw42159 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42159step0 raw42159; decide +kernel
      have hl : raw42159step0Labels = raw42159Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42159 raw42159Labels permutation152 permutation3
    mixedMoment B raw42159step0 raw42159step0Labels = mixedMoment B raw42159step1 raw42159step1Labels := by
      have ha : raw42159step1 = raw42159step0 := by apply Matrix.ext; unfold raw42159step1 raw42159step0; decide +kernel
      have hl : raw42159step0Labels = labelEmbedding7 ∘ raw42159step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42159step0 raw42159step0Labels raw42159step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5472 node5472Labels := by rfl

theorem canonical42160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42160 raw42160Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw42160 raw42160Labels = mixedMoment B raw42160step0 raw42160step0Labels := by
      have ha : raw42160step0 = (fun i j => raw42160 (permutation426 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42160step0 raw42160; decide +kernel
      have hl : raw42160step0Labels = raw42160Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42160 raw42160Labels permutation426 permutation4
    mixedMoment B raw42160step0 raw42160step0Labels = mixedMoment B raw42160step1 raw42160step1Labels := by
      have ha : raw42160step1 = raw42160step0 := by apply Matrix.ext; unfold raw42160step1 raw42160step0; decide +kernel
      have hl : raw42160step0Labels = labelEmbedding1 ∘ raw42160step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42160step0 raw42160step0Labels raw42160step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

theorem canonical42161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42161 raw42161Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42161 raw42161Labels = mixedMoment B raw42161step0 raw42161step0Labels := by
      have ha : raw42161step0 = (fun i j => raw42161 (permutation426 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42161step0 raw42161; decide +kernel
      have hl : raw42161step0Labels = raw42161Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42161 raw42161Labels permutation426 permutation4
    mixedMoment B raw42161step0 raw42161step0Labels = mixedMoment B raw42161step1 raw42161step1Labels := by
      have ha : raw42161step1 = raw42161step0 := by apply Matrix.ext; unfold raw42161step1 raw42161step0; decide +kernel
      have hl : raw42161step0Labels = labelEmbedding10 ∘ raw42161step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42161step0 raw42161step0Labels raw42161step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical42162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42162 raw42162Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw42162 raw42162Labels = mixedMoment B raw42162step0 raw42162step0Labels := by
      have hz : ∀ j, raw42162 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42162step0 = (fun i j => raw42162 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42162step0 raw42162; decide +kernel
      have hl : raw42162step0Labels = raw42162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42162 raw42162Labels permutation520 hz
    mixedMoment B raw42162step0 raw42162step0Labels = mixedMoment B raw42162step1 raw42162step1Labels := by
      have hz : ∀ j, raw42162step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42162step1 = (fun i j => raw42162step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42162step1 raw42162step0; decide +kernel
      have hl : raw42162step1Labels = raw42162step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42162step0 raw42162step0Labels permutation104 hz
    mixedMoment B raw42162step1 raw42162step1Labels = mixedMoment B raw42162step2 raw42162step2Labels := by
      have ha : raw42162step2 = (fun i j => raw42162step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42162step2 raw42162step1; decide +kernel
      have hl : raw42162step2Labels = raw42162step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42162step1 raw42162step1Labels permutation31 permutation2
    mixedMoment B raw42162step2 raw42162step2Labels = mixedMoment B raw42162step3 raw42162step3Labels := by
      have ha : raw42162step3 = -raw42162step2 := by apply Matrix.ext; change ∀ i j, raw42162step3 i j = -(raw42162step2 i j); unfold raw42162step3 raw42162step2; decide +kernel
      have hl : raw42162step3Labels = raw42162step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42162step3 raw42162step3Labels = mixedMoment B raw42162step4 raw42162step4Labels := by
      have ha : raw42162step4 = raw42162step3 := by apply Matrix.ext; unfold raw42162step4 raw42162step3; decide +kernel
      have hl : raw42162step3Labels = labelEmbedding1 ∘ raw42162step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42162step3 raw42162step3Labels raw42162step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3229 node3229Labels := by rfl

theorem canonical42163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42163 raw42163Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw42163 raw42163Labels = mixedMoment B raw42163step0 raw42163step0Labels := by
      have hz : ∀ j, raw42163 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42163step0 = (fun i j => raw42163 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42163step0 raw42163; decide +kernel
      have hl : raw42163step0Labels = raw42163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42163 raw42163Labels permutation520 hz
    mixedMoment B raw42163step0 raw42163step0Labels = mixedMoment B raw42163step1 raw42163step1Labels := by
      have hz : ∀ j, raw42163step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42163step1 = (fun i j => raw42163step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42163step1 raw42163step0; decide +kernel
      have hl : raw42163step1Labels = raw42163step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42163step0 raw42163step0Labels permutation104 hz
    mixedMoment B raw42163step1 raw42163step1Labels = mixedMoment B raw42163step2 raw42163step2Labels := by
      have ha : raw42163step2 = (fun i j => raw42163step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42163step2 raw42163step1; decide +kernel
      have hl : raw42163step2Labels = raw42163step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42163step1 raw42163step1Labels permutation31 permutation3
    mixedMoment B raw42163step2 raw42163step2Labels = mixedMoment B raw42163step3 raw42163step3Labels := by
      have ha : raw42163step3 = -raw42163step2 := by apply Matrix.ext; change ∀ i j, raw42163step3 i j = -(raw42163step2 i j); unfold raw42163step3 raw42163step2; decide +kernel
      have hl : raw42163step3Labels = raw42163step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42163step3 raw42163step3Labels = mixedMoment B raw42163step4 raw42163step4Labels := by
      have ha : raw42163step4 = raw42163step3 := by apply Matrix.ext; unfold raw42163step4 raw42163step3; decide +kernel
      have hl : raw42163step3Labels = labelEmbedding7 ∘ raw42163step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42163step3 raw42163step3Labels raw42163step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical42164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42164 raw42164Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw42164 raw42164Labels = mixedMoment B raw42164step0 raw42164step0Labels := by
      have hz : ∀ j, raw42164 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42164step0 = (fun i j => raw42164 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42164step0 raw42164; decide +kernel
      have hl : raw42164step0Labels = raw42164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42164 raw42164Labels permutation434 hz
    mixedMoment B raw42164step0 raw42164step0Labels = mixedMoment B raw42164step1 raw42164step1Labels := by
      have ha : raw42164step1 = (fun i j => raw42164step0 (permutation146 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42164step1 raw42164step0; decide +kernel
      have hl : raw42164step1Labels = raw42164step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42164step0 raw42164step0Labels permutation146 permutation4
    mixedMoment B raw42164step1 raw42164step1Labels = mixedMoment B raw42164step2 raw42164step2Labels := by
      have ha : raw42164step2 = raw42164step1 := by apply Matrix.ext; unfold raw42164step2 raw42164step1; decide +kernel
      have hl : raw42164step1Labels = labelEmbedding1 ∘ raw42164step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42164step1 raw42164step1Labels raw42164step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3109 node3109Labels := by rfl

theorem canonical42165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42165 raw42165Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw42165 raw42165Labels = mixedMoment B raw42165step0 raw42165step0Labels := by
      have hz : ∀ j, raw42165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42165step0 = (fun i j => raw42165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42165step0 raw42165; decide +kernel
      have hl : raw42165step0Labels = raw42165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42165 raw42165Labels permutation434 hz
    mixedMoment B raw42165step0 raw42165step0Labels = mixedMoment B raw42165step1 raw42165step1Labels := by
      have ha : raw42165step1 = (fun i j => raw42165step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42165step1 raw42165step0; decide +kernel
      have hl : raw42165step1Labels = raw42165step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42165step0 raw42165step0Labels permutation151 permutation5
    mixedMoment B raw42165step1 raw42165step1Labels = mixedMoment B raw42165step2 raw42165step2Labels := by
      have ha : raw42165step2 = raw42165step1 := by apply Matrix.ext; unfold raw42165step2 raw42165step1; decide +kernel
      have hl : raw42165step1Labels = labelEmbedding9 ∘ raw42165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42165step1 raw42165step1Labels raw42165step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical42166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42166 raw42166Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw42166 raw42166Labels = mixedMoment B raw42166step0 raw42166step0Labels := by
      have hz : ∀ j, raw42166 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42166step0 = (fun i j => raw42166 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42166step0 raw42166; decide +kernel
      have hl : raw42166step0Labels = raw42166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42166 raw42166Labels permutation434 hz
    mixedMoment B raw42166step0 raw42166step0Labels = mixedMoment B raw42166step1 raw42166step1Labels := by
      have ha : raw42166step1 = raw42166step0 := by apply Matrix.ext; unfold raw42166step1 raw42166step0; decide +kernel
      have hl : raw42166step0Labels = labelEmbedding1 ∘ raw42166step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42166step0 raw42166step0Labels raw42166step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3996 node3996Labels := by rfl

theorem canonical42167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42167 raw42167Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw42167 raw42167Labels = mixedMoment B raw42167step0 raw42167step0Labels := by
      have hz : ∀ j, raw42167 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42167step0 = (fun i j => raw42167 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42167step0 raw42167; decide +kernel
      have hl : raw42167step0Labels = raw42167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42167 raw42167Labels permutation434 hz
    mixedMoment B raw42167step0 raw42167step0Labels = mixedMoment B raw42167step1 raw42167step1Labels := by
      have ha : raw42167step1 = (fun i j => raw42167step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42167step1 raw42167step0; decide +kernel
      have hl : raw42167step1Labels = raw42167step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42167step0 raw42167step0Labels permutation151 permutation3
    mixedMoment B raw42167step1 raw42167step1Labels = mixedMoment B raw42167step2 raw42167step2Labels := by
      have ha : raw42167step2 = -raw42167step1 := by apply Matrix.ext; change ∀ i j, raw42167step2 i j = -(raw42167step1 i j); unfold raw42167step2 raw42167step1; decide +kernel
      have hl : raw42167step2Labels = raw42167step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42167step2 raw42167step2Labels = mixedMoment B raw42167step3 raw42167step3Labels := by
      have ha : raw42167step3 = raw42167step2 := by apply Matrix.ext; unfold raw42167step3 raw42167step2; decide +kernel
      have hl : raw42167step2Labels = labelEmbedding7 ∘ raw42167step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42167step2 raw42167step2Labels raw42167step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical42168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42168 raw42168Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw42168 raw42168Labels = mixedMoment B raw42168step0 raw42168step0Labels := by
      have hz : ∀ j, raw42168 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42168step0 = (fun i j => raw42168 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42168step0 raw42168; decide +kernel
      have hl : raw42168step0Labels = raw42168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42168 raw42168Labels permutation434 hz
    mixedMoment B raw42168step0 raw42168step0Labels = mixedMoment B raw42168step1 raw42168step1Labels := by
      have ha : raw42168step1 = raw42168step0 := by apply Matrix.ext; unfold raw42168step1 raw42168step0; decide +kernel
      have hl : raw42168step0Labels = labelEmbedding1 ∘ raw42168step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42168step0 raw42168step0Labels raw42168step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3995 node3995Labels := by rfl

theorem canonical42169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42169 raw42169Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw42169 raw42169Labels = mixedMoment B raw42169step0 raw42169step0Labels := by
      have hz : ∀ j, raw42169 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42169step0 = (fun i j => raw42169 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42169step0 raw42169; decide +kernel
      have hl : raw42169step0Labels = raw42169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42169 raw42169Labels permutation434 hz
    mixedMoment B raw42169step0 raw42169step0Labels = mixedMoment B raw42169step1 raw42169step1Labels := by
      have ha : raw42169step1 = (fun i j => raw42169step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42169step1 raw42169step0; decide +kernel
      have hl : raw42169step1Labels = raw42169step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42169step0 raw42169step0Labels permutation151 permutation3
    mixedMoment B raw42169step1 raw42169step1Labels = mixedMoment B raw42169step2 raw42169step2Labels := by
      have ha : raw42169step2 = -raw42169step1 := by apply Matrix.ext; change ∀ i j, raw42169step2 i j = -(raw42169step1 i j); unfold raw42169step2 raw42169step1; decide +kernel
      have hl : raw42169step2Labels = raw42169step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42169step2 raw42169step2Labels = mixedMoment B raw42169step3 raw42169step3Labels := by
      have ha : raw42169step3 = raw42169step2 := by apply Matrix.ext; unfold raw42169step3 raw42169step2; decide +kernel
      have hl : raw42169step2Labels = labelEmbedding7 ∘ raw42169step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42169step2 raw42169step2Labels raw42169step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical42170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42170 raw42170Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw42170 raw42170Labels = mixedMoment B raw42170step0 raw42170step0Labels := by
      have hz : ∀ j, raw42170 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42170step0 = (fun i j => raw42170 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42170step0 raw42170; decide +kernel
      have hl : raw42170step0Labels = raw42170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42170 raw42170Labels permutation434 hz
    mixedMoment B raw42170step0 raw42170step0Labels = mixedMoment B raw42170step1 raw42170step1Labels := by
      have ha : raw42170step1 = (fun i j => raw42170step0 (permutation122 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42170step1 raw42170step0; decide +kernel
      have hl : raw42170step1Labels = raw42170step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42170step0 raw42170step0Labels permutation122 permutation4
    mixedMoment B raw42170step1 raw42170step1Labels = mixedMoment B raw42170step2 raw42170step2Labels := by
      have ha : raw42170step2 = raw42170step1 := by apply Matrix.ext; unfold raw42170step2 raw42170step1; decide +kernel
      have hl : raw42170step1Labels = labelEmbedding1 ∘ raw42170step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42170step1 raw42170step1Labels raw42170step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical42171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42171 raw42171Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw42171 raw42171Labels = mixedMoment B raw42171step0 raw42171step0Labels := by
      have hz : ∀ j, raw42171 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42171step0 = (fun i j => raw42171 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42171step0 raw42171; decide +kernel
      have hl : raw42171step0Labels = raw42171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42171 raw42171Labels permutation434 hz
    mixedMoment B raw42171step0 raw42171step0Labels = mixedMoment B raw42171step1 raw42171step1Labels := by
      have ha : raw42171step1 = (fun i j => raw42171step0 (permutation122 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42171step1 raw42171step0; decide +kernel
      have hl : raw42171step1Labels = raw42171step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42171step0 raw42171step0Labels permutation122 permutation4
    mixedMoment B raw42171step1 raw42171step1Labels = mixedMoment B raw42171step2 raw42171step2Labels := by
      have ha : raw42171step2 = raw42171step1 := by apply Matrix.ext; unfold raw42171step2 raw42171step1; decide +kernel
      have hl : raw42171step1Labels = labelEmbedding10 ∘ raw42171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42171step1 raw42171step1Labels raw42171step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical42172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42172 raw42172Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw42172 raw42172Labels = mixedMoment B raw42172step0 raw42172step0Labels := by
      have ha : raw42172step0 = (fun i j => raw42172 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42172step0 raw42172; decide +kernel
      have hl : raw42172step0Labels = raw42172Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42172 raw42172Labels permutation158 permutation2
    mixedMoment B raw42172step0 raw42172step0Labels = mixedMoment B raw42172step1 raw42172step1Labels := by
      have ha : raw42172step1 = raw42172step0 := by apply Matrix.ext; unfold raw42172step1 raw42172step0; decide +kernel
      have hl : raw42172step0Labels = labelEmbedding1 ∘ raw42172step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42172step0 raw42172step0Labels raw42172step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3990 node3990Labels := by rfl

theorem canonical42173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42173 raw42173Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw42173 raw42173Labels = mixedMoment B raw42173step0 raw42173step0Labels := by
      have ha : raw42173step0 = (fun i j => raw42173 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42173step0 raw42173; decide +kernel
      have hl : raw42173step0Labels = raw42173Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42173 raw42173Labels permutation688 permutation3
    mixedMoment B raw42173step0 raw42173step0Labels = mixedMoment B raw42173step1 raw42173step1Labels := by
      have ha : raw42173step1 = -raw42173step0 := by apply Matrix.ext; change ∀ i j, raw42173step1 i j = -(raw42173step0 i j); unfold raw42173step1 raw42173step0; decide +kernel
      have hl : raw42173step1Labels = raw42173step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42173step1 raw42173step1Labels = mixedMoment B raw42173step2 raw42173step2Labels := by
      have ha : raw42173step2 = raw42173step1 := by apply Matrix.ext; unfold raw42173step2 raw42173step1; decide +kernel
      have hl : raw42173step1Labels = labelEmbedding7 ∘ raw42173step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42173step1 raw42173step1Labels raw42173step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical42174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42174 raw42174Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw42174 raw42174Labels = mixedMoment B raw42174step0 raw42174step0Labels := by
      have ha : raw42174step0 = (fun i j => raw42174 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42174step0 raw42174; decide +kernel
      have hl : raw42174step0Labels = raw42174Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42174 raw42174Labels permutation682 permutation2
    mixedMoment B raw42174step0 raw42174step0Labels = mixedMoment B raw42174step1 raw42174step1Labels := by
      have ha : raw42174step1 = -raw42174step0 := by apply Matrix.ext; change ∀ i j, raw42174step1 i j = -(raw42174step0 i j); unfold raw42174step1 raw42174step0; decide +kernel
      have hl : raw42174step1Labels = raw42174step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42174step1 raw42174step1Labels = mixedMoment B raw42174step2 raw42174step2Labels := by
      have ha : raw42174step2 = raw42174step1 := by apply Matrix.ext; unfold raw42174step2 raw42174step1; decide +kernel
      have hl : raw42174step1Labels = labelEmbedding1 ∘ raw42174step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42174step1 raw42174step1Labels raw42174step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical42175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42175 raw42175Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42175 raw42175Labels = mixedMoment B raw42175step0 raw42175step0Labels := by
      have ha : raw42175step0 = (fun i j => raw42175 (permutation634 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42175step0 raw42175; decide +kernel
      have hl : raw42175step0Labels = raw42175Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42175 raw42175Labels permutation634 permutation7
    mixedMoment B raw42175step0 raw42175step0Labels = mixedMoment B raw42175step1 raw42175step1Labels := by
      have ha : raw42175step1 = raw42175step0 := by apply Matrix.ext; unfold raw42175step1 raw42175step0; decide +kernel
      have hl : raw42175step0Labels = labelEmbedding6 ∘ raw42175step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42175step0 raw42175step0Labels raw42175step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2400) =
      Integer.Sparse.eval keyMomentRow2400 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2400).leftCharge (GramAssembly.key 2400).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3584) := by
    have ha : gramCharges (GramAssembly.key 2400).leftCharge (GramAssembly.key 2400).rightCharge = raw42112 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42112Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42112 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2400).leftCharge (GramAssembly.key 2400).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5300) := by
    have ha : gramCharges (GramAssembly.key 2400).leftCharge (GramAssembly.key 2400).rightCharge = raw42113 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42113Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42113 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2400).leftCharge (GramAssembly.key 2400).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2400).leftCharge (GramAssembly.key 2400).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2400, Integer.Sparse.eval]
  ring

theorem keyMoment2401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2401) =
      Integer.Sparse.eval keyMomentRow2401 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2401).leftCharge (GramAssembly.key 2401).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3535) := by
    have ha : gramCharges (GramAssembly.key 2401).leftCharge (GramAssembly.key 2401).rightCharge = raw42114 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42114Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42114 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2401).leftCharge (GramAssembly.key 2401).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5266) := by
    have ha : gramCharges (GramAssembly.key 2401).leftCharge (GramAssembly.key 2401).rightCharge = raw42115 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42115Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42115 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2401).leftCharge (GramAssembly.key 2401).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2401).leftCharge (GramAssembly.key 2401).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2401, Integer.Sparse.eval]
  ring

theorem keyMoment2402 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2402) =
      Integer.Sparse.eval keyMomentRow2402 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2402).leftCharge (GramAssembly.key 2402).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3959) := by
    have ha : gramCharges (GramAssembly.key 2402).leftCharge (GramAssembly.key 2402).rightCharge = raw42116 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42116Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42116 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2402).leftCharge (GramAssembly.key 2402).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5446) := by
    have ha : gramCharges (GramAssembly.key 2402).leftCharge (GramAssembly.key 2402).rightCharge = raw42117 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42117Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42117 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2402).leftCharge (GramAssembly.key 2402).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2402).leftCharge (GramAssembly.key 2402).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2402, Integer.Sparse.eval]
  ring

theorem keyMoment2403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2403) =
      Integer.Sparse.eval keyMomentRow2403 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2403).leftCharge (GramAssembly.key 2403).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4028) := by
    have ha : gramCharges (GramAssembly.key 2403).leftCharge (GramAssembly.key 2403).rightCharge = raw42118 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42118Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42118 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2403).leftCharge (GramAssembly.key 2403).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5448) := by
    have ha : gramCharges (GramAssembly.key 2403).leftCharge (GramAssembly.key 2403).rightCharge = raw42119 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42119Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42119 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2403).leftCharge (GramAssembly.key 2403).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2403).leftCharge (GramAssembly.key 2403).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2403, Integer.Sparse.eval]
  ring

theorem keyMoment2404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2404) =
      Integer.Sparse.eval keyMomentRow2404 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2404).leftCharge (GramAssembly.key 2404).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4024) := by
    have ha : gramCharges (GramAssembly.key 2404).leftCharge (GramAssembly.key 2404).rightCharge = raw42120 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42120Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42120 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2404).leftCharge (GramAssembly.key 2404).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5445) := by
    have ha : gramCharges (GramAssembly.key 2404).leftCharge (GramAssembly.key 2404).rightCharge = raw42121 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42121Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42121 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2404).leftCharge (GramAssembly.key 2404).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2404).leftCharge (GramAssembly.key 2404).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2404, Integer.Sparse.eval]
  ring

theorem keyMoment2405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2405) =
      Integer.Sparse.eval keyMomentRow2405 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2405).leftCharge (GramAssembly.key 2405).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3541) := by
    have ha : gramCharges (GramAssembly.key 2405).leftCharge (GramAssembly.key 2405).rightCharge = raw42122 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42122Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42122 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2405).leftCharge (GramAssembly.key 2405).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2405).leftCharge (GramAssembly.key 2405).rightCharge = raw42123 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42123Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42123 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2405).leftCharge (GramAssembly.key 2405).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2405).leftCharge (GramAssembly.key 2405).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2405, Integer.Sparse.eval]
  ring

theorem keyMoment2406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2406) =
      Integer.Sparse.eval keyMomentRow2406 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2406).leftCharge (GramAssembly.key 2406).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3526) := by
    have ha : gramCharges (GramAssembly.key 2406).leftCharge (GramAssembly.key 2406).rightCharge = raw42124 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42124Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42124 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2406).leftCharge (GramAssembly.key 2406).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2406).leftCharge (GramAssembly.key 2406).rightCharge = raw42125 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42125Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42125 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2406).leftCharge (GramAssembly.key 2406).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2406).leftCharge (GramAssembly.key 2406).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2406, Integer.Sparse.eval]
  ring

theorem keyMoment2407 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2407) =
      Integer.Sparse.eval keyMomentRow2407 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2407).leftCharge (GramAssembly.key 2407).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3549) := by
    have ha : gramCharges (GramAssembly.key 2407).leftCharge (GramAssembly.key 2407).rightCharge = raw42126 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42126Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42126 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2407).leftCharge (GramAssembly.key 2407).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5268) := by
    have ha : gramCharges (GramAssembly.key 2407).leftCharge (GramAssembly.key 2407).rightCharge = raw42127 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42127Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42127 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2407).leftCharge (GramAssembly.key 2407).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2407).leftCharge (GramAssembly.key 2407).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2407, Integer.Sparse.eval]
  ring

theorem keyMoment2408 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2408) =
      Integer.Sparse.eval keyMomentRow2408 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2408).leftCharge (GramAssembly.key 2408).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3535) := by
    have ha : gramCharges (GramAssembly.key 2408).leftCharge (GramAssembly.key 2408).rightCharge = raw42128 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42128Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42128 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2408).leftCharge (GramAssembly.key 2408).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5266) := by
    have ha : gramCharges (GramAssembly.key 2408).leftCharge (GramAssembly.key 2408).rightCharge = raw42129 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42129Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42129 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2408).leftCharge (GramAssembly.key 2408).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2408).leftCharge (GramAssembly.key 2408).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2408, Integer.Sparse.eval]
  ring

theorem keyMoment2409 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2409) =
      Integer.Sparse.eval keyMomentRow2409 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2409).leftCharge (GramAssembly.key 2409).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3231) := by
    have ha : gramCharges (GramAssembly.key 2409).leftCharge (GramAssembly.key 2409).rightCharge = raw42130 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42130Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42130 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2409).leftCharge (GramAssembly.key 2409).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4901) := by
    have ha : gramCharges (GramAssembly.key 2409).leftCharge (GramAssembly.key 2409).rightCharge = raw42131 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42131Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42131 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2409).leftCharge (GramAssembly.key 2409).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2409).leftCharge (GramAssembly.key 2409).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2409, Integer.Sparse.eval]
  ring

theorem keyMoment2410 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2410) =
      Integer.Sparse.eval keyMomentRow2410 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2410).leftCharge (GramAssembly.key 2410).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3110) := by
    have ha : gramCharges (GramAssembly.key 2410).leftCharge (GramAssembly.key 2410).rightCharge = raw42132 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42132Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42132 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2410).leftCharge (GramAssembly.key 2410).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5275) := by
    have ha : gramCharges (GramAssembly.key 2410).leftCharge (GramAssembly.key 2410).rightCharge = raw42133 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42133Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42133 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2410).leftCharge (GramAssembly.key 2410).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2410).leftCharge (GramAssembly.key 2410).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2410, Integer.Sparse.eval]
  ring

theorem keyMoment2411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2411) =
      Integer.Sparse.eval keyMomentRow2411 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2411).leftCharge (GramAssembly.key 2411).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4006) := by
    have ha : gramCharges (GramAssembly.key 2411).leftCharge (GramAssembly.key 2411).rightCharge = raw42134 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42134Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42134 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2411).leftCharge (GramAssembly.key 2411).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5413) := by
    have ha : gramCharges (GramAssembly.key 2411).leftCharge (GramAssembly.key 2411).rightCharge = raw42135 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42135Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42135 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2411).leftCharge (GramAssembly.key 2411).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2411).leftCharge (GramAssembly.key 2411).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2411, Integer.Sparse.eval]
  ring

theorem keyMoment2412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2412) =
      Integer.Sparse.eval keyMomentRow2412 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2412).leftCharge (GramAssembly.key 2412).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4004) := by
    have ha : gramCharges (GramAssembly.key 2412).leftCharge (GramAssembly.key 2412).rightCharge = raw42136 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42136Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42136 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2412).leftCharge (GramAssembly.key 2412).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5475) := by
    have ha : gramCharges (GramAssembly.key 2412).leftCharge (GramAssembly.key 2412).rightCharge = raw42137 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42137Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42137 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2412).leftCharge (GramAssembly.key 2412).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2412).leftCharge (GramAssembly.key 2412).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2412, Integer.Sparse.eval]
  ring

theorem keyMoment2413 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2413) =
      Integer.Sparse.eval keyMomentRow2413 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2413).leftCharge (GramAssembly.key 2413).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2774) := by
    have ha : gramCharges (GramAssembly.key 2413).leftCharge (GramAssembly.key 2413).rightCharge = raw42138 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42138Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42138 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2413).leftCharge (GramAssembly.key 2413).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5300) := by
    have ha : gramCharges (GramAssembly.key 2413).leftCharge (GramAssembly.key 2413).rightCharge = raw42139 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42139Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42139 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2413).leftCharge (GramAssembly.key 2413).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2413).leftCharge (GramAssembly.key 2413).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2413, Integer.Sparse.eval]
  ring

theorem keyMoment2414 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2414) =
      Integer.Sparse.eval keyMomentRow2414 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2414).leftCharge (GramAssembly.key 2414).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4003) := by
    have ha : gramCharges (GramAssembly.key 2414).leftCharge (GramAssembly.key 2414).rightCharge = raw42140 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42140Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42140 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2414).leftCharge (GramAssembly.key 2414).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5428) := by
    have ha : gramCharges (GramAssembly.key 2414).leftCharge (GramAssembly.key 2414).rightCharge = raw42141 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42141Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42141 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2414).leftCharge (GramAssembly.key 2414).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2414).leftCharge (GramAssembly.key 2414).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2414, Integer.Sparse.eval]
  ring

theorem keyMoment2415 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2415) =
      Integer.Sparse.eval keyMomentRow2415 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2415).leftCharge (GramAssembly.key 2415).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3995) := by
    have ha : gramCharges (GramAssembly.key 2415).leftCharge (GramAssembly.key 2415).rightCharge = raw42142 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42142Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42142 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2415).leftCharge (GramAssembly.key 2415).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5473) := by
    have ha : gramCharges (GramAssembly.key 2415).leftCharge (GramAssembly.key 2415).rightCharge = raw42143 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42143Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42143 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2415).leftCharge (GramAssembly.key 2415).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2415).leftCharge (GramAssembly.key 2415).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2415, Integer.Sparse.eval]
  ring

theorem keyMoment2416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2416) =
      Integer.Sparse.eval keyMomentRow2416 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2416).leftCharge (GramAssembly.key 2416).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3881) := by
    have ha : gramCharges (GramAssembly.key 2416).leftCharge (GramAssembly.key 2416).rightCharge = raw42144 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42144Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42144 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2416).leftCharge (GramAssembly.key 2416).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5446) := by
    have ha : gramCharges (GramAssembly.key 2416).leftCharge (GramAssembly.key 2416).rightCharge = raw42145 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42145Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42145 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2416).leftCharge (GramAssembly.key 2416).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2416).leftCharge (GramAssembly.key 2416).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2416, Integer.Sparse.eval]
  ring

theorem keyMoment2417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2417) =
      Integer.Sparse.eval keyMomentRow2417 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2417).leftCharge (GramAssembly.key 2417).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3854) := by
    have ha : gramCharges (GramAssembly.key 2417).leftCharge (GramAssembly.key 2417).rightCharge = raw42146 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42146Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42146 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2417).leftCharge (GramAssembly.key 2417).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5436) := by
    have ha : gramCharges (GramAssembly.key 2417).leftCharge (GramAssembly.key 2417).rightCharge = raw42147 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42147Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42147 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2417).leftCharge (GramAssembly.key 2417).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2417).leftCharge (GramAssembly.key 2417).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2417, Integer.Sparse.eval]
  ring

theorem keyMoment2418 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2418) =
      Integer.Sparse.eval keyMomentRow2418 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2418).leftCharge (GramAssembly.key 2418).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2751) := by
    have ha : gramCharges (GramAssembly.key 2418).leftCharge (GramAssembly.key 2418).rightCharge = raw42148 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42148Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42148 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2418).leftCharge (GramAssembly.key 2418).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5282) := by
    have ha : gramCharges (GramAssembly.key 2418).leftCharge (GramAssembly.key 2418).rightCharge = raw42149 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42149Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42149 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2418).leftCharge (GramAssembly.key 2418).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2418).leftCharge (GramAssembly.key 2418).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2418, Integer.Sparse.eval]
  ring

theorem keyMoment2419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2419) =
      Integer.Sparse.eval keyMomentRow2419 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2419).leftCharge (GramAssembly.key 2419).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3995) := by
    have ha : gramCharges (GramAssembly.key 2419).leftCharge (GramAssembly.key 2419).rightCharge = raw42150 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42150Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42150 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2419).leftCharge (GramAssembly.key 2419).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5473) := by
    have ha : gramCharges (GramAssembly.key 2419).leftCharge (GramAssembly.key 2419).rightCharge = raw42151 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42151Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42151 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2419).leftCharge (GramAssembly.key 2419).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2419).leftCharge (GramAssembly.key 2419).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2419, Integer.Sparse.eval]
  ring

theorem keyMoment2420 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2420) =
      Integer.Sparse.eval keyMomentRow2420 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2420).leftCharge (GramAssembly.key 2420).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4005) := by
    have ha : gramCharges (GramAssembly.key 2420).leftCharge (GramAssembly.key 2420).rightCharge = raw42152 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42152Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42152 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2420).leftCharge (GramAssembly.key 2420).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5474) := by
    have ha : gramCharges (GramAssembly.key 2420).leftCharge (GramAssembly.key 2420).rightCharge = raw42153 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42153Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42153 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2420).leftCharge (GramAssembly.key 2420).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2420).leftCharge (GramAssembly.key 2420).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2420, Integer.Sparse.eval]
  ring

theorem keyMoment2421 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2421) =
      Integer.Sparse.eval keyMomentRow2421 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2421).leftCharge (GramAssembly.key 2421).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3846) := by
    have ha : gramCharges (GramAssembly.key 2421).leftCharge (GramAssembly.key 2421).rightCharge = raw42154 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42154Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42154 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2421).leftCharge (GramAssembly.key 2421).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2421).leftCharge (GramAssembly.key 2421).rightCharge = raw42155 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42155Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42155 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2421).leftCharge (GramAssembly.key 2421).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2421).leftCharge (GramAssembly.key 2421).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2421, Integer.Sparse.eval]
  ring

theorem keyMoment2422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2422) =
      Integer.Sparse.eval keyMomentRow2422 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2422).leftCharge (GramAssembly.key 2422).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3976) := by
    have ha : gramCharges (GramAssembly.key 2422).leftCharge (GramAssembly.key 2422).rightCharge = raw42156 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42156Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42156 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2422).leftCharge (GramAssembly.key 2422).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5471) := by
    have ha : gramCharges (GramAssembly.key 2422).leftCharge (GramAssembly.key 2422).rightCharge = raw42157 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42157Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42157 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2422).leftCharge (GramAssembly.key 2422).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2422).leftCharge (GramAssembly.key 2422).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2422, Integer.Sparse.eval]
  ring

theorem keyMoment2423 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2423) =
      Integer.Sparse.eval keyMomentRow2423 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2423).leftCharge (GramAssembly.key 2423).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4002) := by
    have ha : gramCharges (GramAssembly.key 2423).leftCharge (GramAssembly.key 2423).rightCharge = raw42158 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42158Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42158 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2423).leftCharge (GramAssembly.key 2423).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5472) := by
    have ha : gramCharges (GramAssembly.key 2423).leftCharge (GramAssembly.key 2423).rightCharge = raw42159 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42159Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42159 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2423).leftCharge (GramAssembly.key 2423).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2423).leftCharge (GramAssembly.key 2423).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2423, Integer.Sparse.eval]
  ring

theorem keyMoment2424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2424) =
      Integer.Sparse.eval keyMomentRow2424 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2424).leftCharge (GramAssembly.key 2424).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3846) := by
    have ha : gramCharges (GramAssembly.key 2424).leftCharge (GramAssembly.key 2424).rightCharge = raw42160 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42160Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42160 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2424).leftCharge (GramAssembly.key 2424).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2424).leftCharge (GramAssembly.key 2424).rightCharge = raw42161 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42161Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42161 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2424).leftCharge (GramAssembly.key 2424).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2424).leftCharge (GramAssembly.key 2424).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2424, Integer.Sparse.eval]
  ring

theorem keyMoment2425 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2425) =
      Integer.Sparse.eval keyMomentRow2425 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2425).leftCharge (GramAssembly.key 2425).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3229) := by
    have ha : gramCharges (GramAssembly.key 2425).leftCharge (GramAssembly.key 2425).rightCharge = raw42162 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42162Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42162 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2425).leftCharge (GramAssembly.key 2425).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4895) := by
    have ha : gramCharges (GramAssembly.key 2425).leftCharge (GramAssembly.key 2425).rightCharge = raw42163 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42163Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42163 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2425).leftCharge (GramAssembly.key 2425).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2425).leftCharge (GramAssembly.key 2425).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2425, Integer.Sparse.eval]
  ring

theorem keyMoment2426 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2426) =
      Integer.Sparse.eval keyMomentRow2426 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2426).leftCharge (GramAssembly.key 2426).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3109) := by
    have ha : gramCharges (GramAssembly.key 2426).leftCharge (GramAssembly.key 2426).rightCharge = raw42164 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42164Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42164 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2426).leftCharge (GramAssembly.key 2426).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5271) := by
    have ha : gramCharges (GramAssembly.key 2426).leftCharge (GramAssembly.key 2426).rightCharge = raw42165 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42165Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42165 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2426).leftCharge (GramAssembly.key 2426).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2426).leftCharge (GramAssembly.key 2426).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2426, Integer.Sparse.eval]
  ring

theorem keyMoment2427 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2427) =
      Integer.Sparse.eval keyMomentRow2427 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2427).leftCharge (GramAssembly.key 2427).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3996) := by
    have ha : gramCharges (GramAssembly.key 2427).leftCharge (GramAssembly.key 2427).rightCharge = raw42166 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42166Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42166 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2427).leftCharge (GramAssembly.key 2427).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5410) := by
    have ha : gramCharges (GramAssembly.key 2427).leftCharge (GramAssembly.key 2427).rightCharge = raw42167 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42167Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42167 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2427).leftCharge (GramAssembly.key 2427).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2427).leftCharge (GramAssembly.key 2427).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2427, Integer.Sparse.eval]
  ring

theorem keyMoment2428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2428) =
      Integer.Sparse.eval keyMomentRow2428 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2428).leftCharge (GramAssembly.key 2428).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3995) := by
    have ha : gramCharges (GramAssembly.key 2428).leftCharge (GramAssembly.key 2428).rightCharge = raw42168 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42168Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42168 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2428).leftCharge (GramAssembly.key 2428).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5473) := by
    have ha : gramCharges (GramAssembly.key 2428).leftCharge (GramAssembly.key 2428).rightCharge = raw42169 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42169Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42169 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2428).leftCharge (GramAssembly.key 2428).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2428).leftCharge (GramAssembly.key 2428).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2428, Integer.Sparse.eval]
  ring

theorem keyMoment2429 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2429) =
      Integer.Sparse.eval keyMomentRow2429 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2429).leftCharge (GramAssembly.key 2429).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2773) := by
    have ha : gramCharges (GramAssembly.key 2429).leftCharge (GramAssembly.key 2429).rightCharge = raw42170 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42170Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42170 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2429).leftCharge (GramAssembly.key 2429).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2429).leftCharge (GramAssembly.key 2429).rightCharge = raw42171 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42171Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42171 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2429).leftCharge (GramAssembly.key 2429).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2429).leftCharge (GramAssembly.key 2429).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2429, Integer.Sparse.eval]
  ring

theorem keyMoment2430 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2430) =
      Integer.Sparse.eval keyMomentRow2430 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2430).leftCharge (GramAssembly.key 2430).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3990) := by
    have ha : gramCharges (GramAssembly.key 2430).leftCharge (GramAssembly.key 2430).rightCharge = raw42172 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42172Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42172 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2430).leftCharge (GramAssembly.key 2430).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5424) := by
    have ha : gramCharges (GramAssembly.key 2430).leftCharge (GramAssembly.key 2430).rightCharge = raw42173 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42173Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42173 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2430).leftCharge (GramAssembly.key 2430).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2430).leftCharge (GramAssembly.key 2430).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2430, Integer.Sparse.eval]
  ring

theorem keyMoment2431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2431) =
      Integer.Sparse.eval keyMomentRow2431 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2431).leftCharge (GramAssembly.key 2431).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3871) := by
    have ha : gramCharges (GramAssembly.key 2431).leftCharge (GramAssembly.key 2431).rightCharge = raw42174 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42174Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42174 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2431).leftCharge (GramAssembly.key 2431).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2431).leftCharge (GramAssembly.key 2431).rightCharge = raw42175 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42175Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42175 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2431).leftCharge (GramAssembly.key 2431).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2431).leftCharge (GramAssembly.key 2431).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2431, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2400 : keyMomentRows (2400 : Fin 2886) =
    keyMomentRow2400 := by decide +kernel

theorem keyMomentRowsAt2401 : keyMomentRows (2401 : Fin 2886) =
    keyMomentRow2401 := by decide +kernel

theorem keyMomentRowsAt2402 : keyMomentRows (2402 : Fin 2886) =
    keyMomentRow2402 := by decide +kernel

theorem keyMomentRowsAt2403 : keyMomentRows (2403 : Fin 2886) =
    keyMomentRow2403 := by decide +kernel

theorem keyMomentRowsAt2404 : keyMomentRows (2404 : Fin 2886) =
    keyMomentRow2404 := by decide +kernel

theorem keyMomentRowsAt2405 : keyMomentRows (2405 : Fin 2886) =
    keyMomentRow2405 := by decide +kernel

theorem keyMomentRowsAt2406 : keyMomentRows (2406 : Fin 2886) =
    keyMomentRow2406 := by decide +kernel

theorem keyMomentRowsAt2407 : keyMomentRows (2407 : Fin 2886) =
    keyMomentRow2407 := by decide +kernel

theorem keyMomentRowsAt2408 : keyMomentRows (2408 : Fin 2886) =
    keyMomentRow2408 := by decide +kernel

theorem keyMomentRowsAt2409 : keyMomentRows (2409 : Fin 2886) =
    keyMomentRow2409 := by decide +kernel

theorem keyMomentRowsAt2410 : keyMomentRows (2410 : Fin 2886) =
    keyMomentRow2410 := by decide +kernel

theorem keyMomentRowsAt2411 : keyMomentRows (2411 : Fin 2886) =
    keyMomentRow2411 := by decide +kernel

theorem keyMomentRowsAt2412 : keyMomentRows (2412 : Fin 2886) =
    keyMomentRow2412 := by decide +kernel

theorem keyMomentRowsAt2413 : keyMomentRows (2413 : Fin 2886) =
    keyMomentRow2413 := by decide +kernel

theorem keyMomentRowsAt2414 : keyMomentRows (2414 : Fin 2886) =
    keyMomentRow2414 := by decide +kernel

theorem keyMomentRowsAt2415 : keyMomentRows (2415 : Fin 2886) =
    keyMomentRow2415 := by decide +kernel

theorem keyMomentRowsAt2416 : keyMomentRows (2416 : Fin 2886) =
    keyMomentRow2416 := by decide +kernel

theorem keyMomentRowsAt2417 : keyMomentRows (2417 : Fin 2886) =
    keyMomentRow2417 := by decide +kernel

theorem keyMomentRowsAt2418 : keyMomentRows (2418 : Fin 2886) =
    keyMomentRow2418 := by decide +kernel

theorem keyMomentRowsAt2419 : keyMomentRows (2419 : Fin 2886) =
    keyMomentRow2419 := by decide +kernel

theorem keyMomentRowsAt2420 : keyMomentRows (2420 : Fin 2886) =
    keyMomentRow2420 := by decide +kernel

theorem keyMomentRowsAt2421 : keyMomentRows (2421 : Fin 2886) =
    keyMomentRow2421 := by decide +kernel

theorem keyMomentRowsAt2422 : keyMomentRows (2422 : Fin 2886) =
    keyMomentRow2422 := by decide +kernel

theorem keyMomentRowsAt2423 : keyMomentRows (2423 : Fin 2886) =
    keyMomentRow2423 := by decide +kernel

theorem keyMomentRowsAt2424 : keyMomentRows (2424 : Fin 2886) =
    keyMomentRow2424 := by decide +kernel

theorem keyMomentRowsAt2425 : keyMomentRows (2425 : Fin 2886) =
    keyMomentRow2425 := by decide +kernel

theorem keyMomentRowsAt2426 : keyMomentRows (2426 : Fin 2886) =
    keyMomentRow2426 := by decide +kernel

theorem keyMomentRowsAt2427 : keyMomentRows (2427 : Fin 2886) =
    keyMomentRow2427 := by decide +kernel

theorem keyMomentRowsAt2428 : keyMomentRows (2428 : Fin 2886) =
    keyMomentRow2428 := by decide +kernel

theorem keyMomentRowsAt2429 : keyMomentRows (2429 : Fin 2886) =
    keyMomentRow2429 := by decide +kernel

theorem keyMomentRowsAt2430 : keyMomentRows (2430 : Fin 2886) =
    keyMomentRow2430 := by decide +kernel

theorem keyMomentRowsAt2431 : keyMomentRows (2431 : Fin 2886) =
    keyMomentRow2431 := by decide +kernel

theorem keyMomentChunkSound75_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 75) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2400 ∨ k.val = 2401 ∨ k.val = 2402 ∨ k.val = 2403 ∨ k.val = 2404 ∨ k.val = 2405 ∨ k.val = 2406 ∨ k.val = 2407 ∨ k.val = 2408 ∨ k.val = 2409 ∨ k.val = 2410 ∨ k.val = 2411 ∨ k.val = 2412 ∨ k.val = 2413 ∨ k.val = 2414 ∨ k.val = 2415 ∨ k.val = 2416 ∨ k.val = 2417 ∨ k.val = 2418 ∨ k.val = 2419 ∨ k.val = 2420 ∨ k.val = 2421 ∨ k.val = 2422 ∨ k.val = 2423 ∨ k.val = 2424 ∨ k.val = 2425 ∨ k.val = 2426 ∨ k.val = 2427 ∨ k.val = 2428 ∨ k.val = 2429 ∨ k.val = 2430 ∨ k.val = 2431 := by omega
  rcases heq with h2400 | h2401 | h2402 | h2403 | h2404 | h2405 | h2406 | h2407 | h2408 | h2409 | h2410 | h2411 | h2412 | h2413 | h2414 | h2415 | h2416 | h2417 | h2418 | h2419 | h2420 | h2421 | h2422 | h2423 | h2424 | h2425 | h2426 | h2427 | h2428 | h2429 | h2430 | h2431
  · have he : k = (2400 : Fin 2886) := Fin.ext h2400
    subst k
    rw [keyMomentRowsAt2400]
    exact keyMoment2400 B hB
  · have he : k = (2401 : Fin 2886) := Fin.ext h2401
    subst k
    rw [keyMomentRowsAt2401]
    exact keyMoment2401 B hB
  · have he : k = (2402 : Fin 2886) := Fin.ext h2402
    subst k
    rw [keyMomentRowsAt2402]
    exact keyMoment2402 B hB
  · have he : k = (2403 : Fin 2886) := Fin.ext h2403
    subst k
    rw [keyMomentRowsAt2403]
    exact keyMoment2403 B hB
  · have he : k = (2404 : Fin 2886) := Fin.ext h2404
    subst k
    rw [keyMomentRowsAt2404]
    exact keyMoment2404 B hB
  · have he : k = (2405 : Fin 2886) := Fin.ext h2405
    subst k
    rw [keyMomentRowsAt2405]
    exact keyMoment2405 B hB
  · have he : k = (2406 : Fin 2886) := Fin.ext h2406
    subst k
    rw [keyMomentRowsAt2406]
    exact keyMoment2406 B hB
  · have he : k = (2407 : Fin 2886) := Fin.ext h2407
    subst k
    rw [keyMomentRowsAt2407]
    exact keyMoment2407 B hB
  · have he : k = (2408 : Fin 2886) := Fin.ext h2408
    subst k
    rw [keyMomentRowsAt2408]
    exact keyMoment2408 B hB
  · have he : k = (2409 : Fin 2886) := Fin.ext h2409
    subst k
    rw [keyMomentRowsAt2409]
    exact keyMoment2409 B hB
  · have he : k = (2410 : Fin 2886) := Fin.ext h2410
    subst k
    rw [keyMomentRowsAt2410]
    exact keyMoment2410 B hB
  · have he : k = (2411 : Fin 2886) := Fin.ext h2411
    subst k
    rw [keyMomentRowsAt2411]
    exact keyMoment2411 B hB
  · have he : k = (2412 : Fin 2886) := Fin.ext h2412
    subst k
    rw [keyMomentRowsAt2412]
    exact keyMoment2412 B hB
  · have he : k = (2413 : Fin 2886) := Fin.ext h2413
    subst k
    rw [keyMomentRowsAt2413]
    exact keyMoment2413 B hB
  · have he : k = (2414 : Fin 2886) := Fin.ext h2414
    subst k
    rw [keyMomentRowsAt2414]
    exact keyMoment2414 B hB
  · have he : k = (2415 : Fin 2886) := Fin.ext h2415
    subst k
    rw [keyMomentRowsAt2415]
    exact keyMoment2415 B hB
  · have he : k = (2416 : Fin 2886) := Fin.ext h2416
    subst k
    rw [keyMomentRowsAt2416]
    exact keyMoment2416 B hB
  · have he : k = (2417 : Fin 2886) := Fin.ext h2417
    subst k
    rw [keyMomentRowsAt2417]
    exact keyMoment2417 B hB
  · have he : k = (2418 : Fin 2886) := Fin.ext h2418
    subst k
    rw [keyMomentRowsAt2418]
    exact keyMoment2418 B hB
  · have he : k = (2419 : Fin 2886) := Fin.ext h2419
    subst k
    rw [keyMomentRowsAt2419]
    exact keyMoment2419 B hB
  · have he : k = (2420 : Fin 2886) := Fin.ext h2420
    subst k
    rw [keyMomentRowsAt2420]
    exact keyMoment2420 B hB
  · have he : k = (2421 : Fin 2886) := Fin.ext h2421
    subst k
    rw [keyMomentRowsAt2421]
    exact keyMoment2421 B hB
  · have he : k = (2422 : Fin 2886) := Fin.ext h2422
    subst k
    rw [keyMomentRowsAt2422]
    exact keyMoment2422 B hB
  · have he : k = (2423 : Fin 2886) := Fin.ext h2423
    subst k
    rw [keyMomentRowsAt2423]
    exact keyMoment2423 B hB
  · have he : k = (2424 : Fin 2886) := Fin.ext h2424
    subst k
    rw [keyMomentRowsAt2424]
    exact keyMoment2424 B hB
  · have he : k = (2425 : Fin 2886) := Fin.ext h2425
    subst k
    rw [keyMomentRowsAt2425]
    exact keyMoment2425 B hB
  · have he : k = (2426 : Fin 2886) := Fin.ext h2426
    subst k
    rw [keyMomentRowsAt2426]
    exact keyMoment2426 B hB
  · have he : k = (2427 : Fin 2886) := Fin.ext h2427
    subst k
    rw [keyMomentRowsAt2427]
    exact keyMoment2427 B hB
  · have he : k = (2428 : Fin 2886) := Fin.ext h2428
    subst k
    rw [keyMomentRowsAt2428]
    exact keyMoment2428 B hB
  · have he : k = (2429 : Fin 2886) := Fin.ext h2429
    subst k
    rw [keyMomentRowsAt2429]
    exact keyMoment2429 B hB
  · have he : k = (2430 : Fin 2886) := Fin.ext h2430
    subst k
    rw [keyMomentRowsAt2430]
    exact keyMoment2430 B hB
  · have he : k = (2431 : Fin 2886) := Fin.ext h2431
    subst k
    rw [keyMomentRowsAt2431]
    exact keyMoment2431 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound75_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound75_e_oai
