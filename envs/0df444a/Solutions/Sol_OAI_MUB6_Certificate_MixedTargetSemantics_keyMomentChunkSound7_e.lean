-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound7_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:01:50.794539+00:00
-- url     : https://prove2.me/submissions/0ad12c58-194c-4325-9a28-72bf09d74e1a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E110
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

theorem mixedMoment_zero_first_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (hA : ∀ i, A i 0 = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i j.succ) (fun j => label j.succ) := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  unfold mixedIntegrand
  rw [Fin.prod_univ_succ]
  have hz : (fun i => A i 0) = 0 := funext hA
  rw [hz, rowFourier_zero, one_mul]

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

theorem delete_zero_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (σ : Equiv.Perm (Fin (n + 1))) (hz : ∀ i, A i (σ 0) = 0) :
    mixedMoment B A label =
      mixedMoment B (fun i j => A i (σ j.succ)) (fun j => label (σ j.succ)) := by
  rw [← mixedMoment_factor_permutation B A label σ]
  exact mixedMoment_zero_first_factor B _ _ hz

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical309
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39674 raw39674Labels = mixedMoment B node487 node487Labels := by
  calc
    mixedMoment B raw39674 raw39674Labels = mixedMoment B raw39674step0 raw39674step0Labels := by
      have hz : ∀ j, raw39674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39674step0 = (fun i j => raw39674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39674step0 raw39674; decide +kernel
      have hl : raw39674step0Labels = raw39674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39674 raw39674Labels permutation346 hz
    mixedMoment B raw39674step0 raw39674step0Labels = mixedMoment B raw39674step1 raw39674step1Labels := by
      have ha : raw39674step1 = (fun i j => raw39674step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39674step1 raw39674step0; decide +kernel
      have hl : raw39674step1Labels = raw39674step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39674step0 raw39674step0Labels permutation32 permutation3
    _ = mixedMoment B node487 node487Labels := by rfl

theorem canonical39675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39675 raw39675Labels = mixedMoment B node490 node490Labels := by
  calc
    mixedMoment B raw39675 raw39675Labels = mixedMoment B raw39675step0 raw39675step0Labels := by
      have hz : ∀ j, raw39675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39675step0 = (fun i j => raw39675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39675step0 raw39675; decide +kernel
      have hl : raw39675step0Labels = raw39675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39675 raw39675Labels permutation346 hz
    mixedMoment B raw39675step0 raw39675step0Labels = mixedMoment B raw39675step1 raw39675step1Labels := by
      have ha : raw39675step1 = (fun i j => raw39675step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39675step1 raw39675step0; decide +kernel
      have hl : raw39675step1Labels = raw39675step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39675step0 raw39675step0Labels permutation151 permutation2
    mixedMoment B raw39675step1 raw39675step1Labels = mixedMoment B raw39675step2 raw39675step2Labels := by
      have ha : raw39675step2 = -raw39675step1 := by apply Matrix.ext; change ∀ i j, raw39675step2 i j = -(raw39675step1 i j); unfold raw39675step2 raw39675step1; decide +kernel
      have hl : raw39675step2Labels = raw39675step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node490 node490Labels := by rfl

theorem canonical39676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39676 raw39676Labels = mixedMoment B node409 node409Labels := by
  calc
    mixedMoment B raw39676 raw39676Labels = mixedMoment B raw39676step0 raw39676step0Labels := by
      have hz : ∀ j, raw39676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39676step0 = (fun i j => raw39676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39676step0 raw39676; decide +kernel
      have hl : raw39676step0Labels = raw39676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39676 raw39676Labels permutation346 hz
    mixedMoment B raw39676step0 raw39676step0Labels = mixedMoment B raw39676step1 raw39676step1Labels := by
      have ha : raw39676step1 = (fun i j => raw39676step0 (permutation133 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39676step1 raw39676step0; decide +kernel
      have hl : raw39676step1Labels = raw39676step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39676step0 raw39676step0Labels permutation133 permutation7
    _ = mixedMoment B node409 node409Labels := by rfl

theorem canonical39677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39677 raw39677Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39677 raw39677Labels = mixedMoment B raw39677step0 raw39677step0Labels := by
      have hz : ∀ j, raw39677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39677step0 = (fun i j => raw39677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39677step0 raw39677; decide +kernel
      have hl : raw39677step0Labels = raw39677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39677 raw39677Labels permutation346 hz
    mixedMoment B raw39677step0 raw39677step0Labels = mixedMoment B raw39677step1 raw39677step1Labels := by
      have ha : raw39677step1 = (fun i j => raw39677step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39677step1 raw39677step0; decide +kernel
      have hl : raw39677step1Labels = raw39677step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39677step0 raw39677step0Labels permutation146 permutation7
    _ = mixedMoment B node384 node384Labels := by rfl

theorem canonical39678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39678 raw39678Labels = mixedMoment B node485 node485Labels := by
  calc
    mixedMoment B raw39678 raw39678Labels = mixedMoment B raw39678step0 raw39678step0Labels := by
      have ha : raw39678step0 = (fun i j => raw39678 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39678step0 raw39678; decide +kernel
      have hl : raw39678step0Labels = raw39678Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39678 raw39678Labels permutation152 permutation3
    _ = mixedMoment B node485 node485Labels := by rfl

theorem canonical39679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39679 raw39679Labels = mixedMoment B node486 node486Labels := by
  calc
    mixedMoment B raw39679 raw39679Labels = mixedMoment B raw39679step0 raw39679step0Labels := by
      have ha : raw39679step0 = (fun i j => raw39679 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39679step0 raw39679; decide +kernel
      have hl : raw39679step0Labels = raw39679Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39679 raw39679Labels permutation152 permutation3
    _ = mixedMoment B node486 node486Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical310
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39680 raw39680Labels = mixedMoment B node487 node487Labels := by
  calc
    mixedMoment B raw39680 raw39680Labels = mixedMoment B raw39680step0 raw39680step0Labels := by
      have hz : ∀ j, raw39680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39680step0 = (fun i j => raw39680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39680step0 raw39680; decide +kernel
      have hl : raw39680step0Labels = raw39680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39680 raw39680Labels permutation434 hz
    mixedMoment B raw39680step0 raw39680step0Labels = mixedMoment B raw39680step1 raw39680step1Labels := by
      have ha : raw39680step1 = (fun i j => raw39680step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39680step1 raw39680step0; decide +kernel
      have hl : raw39680step1Labels = raw39680step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39680step0 raw39680step0Labels permutation151 permutation3
    mixedMoment B raw39680step1 raw39680step1Labels = mixedMoment B raw39680step2 raw39680step2Labels := by
      have ha : raw39680step2 = -raw39680step1 := by apply Matrix.ext; change ∀ i j, raw39680step2 i j = -(raw39680step1 i j); unfold raw39680step2 raw39680step1; decide +kernel
      have hl : raw39680step2Labels = raw39680step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node487 node487Labels := by rfl

theorem canonical39681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39681 raw39681Labels = mixedMoment B node491 node491Labels := by
  calc
    mixedMoment B raw39681 raw39681Labels = mixedMoment B raw39681step0 raw39681step0Labels := by
      have hz : ∀ j, raw39681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39681step0 = (fun i j => raw39681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39681step0 raw39681; decide +kernel
      have hl : raw39681step0Labels = raw39681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39681 raw39681Labels permutation434 hz
    mixedMoment B raw39681step0 raw39681step0Labels = mixedMoment B raw39681step1 raw39681step1Labels := by
      have ha : raw39681step1 = (fun i j => raw39681step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39681step1 raw39681step0; decide +kernel
      have hl : raw39681step1Labels = raw39681step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39681step0 raw39681step0Labels permutation42 permutation5
    mixedMoment B raw39681step1 raw39681step1Labels = mixedMoment B raw39681step2 raw39681step2Labels := by
      have ha : raw39681step2 = -raw39681step1 := by apply Matrix.ext; change ∀ i j, raw39681step2 i j = -(raw39681step1 i j); unfold raw39681step2 raw39681step1; decide +kernel
      have hl : raw39681step2Labels = raw39681step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node491 node491Labels := by rfl

theorem canonical39682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39682 raw39682Labels = mixedMoment B node484 node484Labels := by
  calc
    mixedMoment B raw39682 raw39682Labels = mixedMoment B raw39682step0 raw39682step0Labels := by
      have ha : raw39682step0 = (fun i j => raw39682 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39682step0 raw39682; decide +kernel
      have hl : raw39682step0Labels = raw39682Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39682 raw39682Labels permutation184 permutation5
    mixedMoment B raw39682step0 raw39682step0Labels = mixedMoment B raw39682step1 raw39682step1Labels := by
      have ha : raw39682step1 = -raw39682step0 := by apply Matrix.ext; change ∀ i j, raw39682step1 i j = -(raw39682step0 i j); unfold raw39682step1 raw39682step0; decide +kernel
      have hl : raw39682step1Labels = raw39682step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node484 node484Labels := by rfl

theorem canonical39683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39683 raw39683Labels = mixedMoment B node486 node486Labels := by
  calc
    mixedMoment B raw39683 raw39683Labels = mixedMoment B raw39683step0 raw39683step0Labels := by
      have ha : raw39683step0 = (fun i j => raw39683 (permutation182 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39683step0 raw39683; decide +kernel
      have hl : raw39683step0Labels = raw39683Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39683 raw39683Labels permutation182 permutation5
    mixedMoment B raw39683step0 raw39683step0Labels = mixedMoment B raw39683step1 raw39683step1Labels := by
      have ha : raw39683step1 = -raw39683step0 := by apply Matrix.ext; change ∀ i j, raw39683step1 i j = -(raw39683step0 i j); unfold raw39683step1 raw39683step0; decide +kernel
      have hl : raw39683step1Labels = raw39683step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node486 node486Labels := by rfl

theorem canonical39684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39684 raw39684Labels = mixedMoment B node501 node501Labels := by
  calc
    mixedMoment B raw39684 raw39684Labels = mixedMoment B raw39684step0 raw39684step0Labels := by
      have hz : ∀ j, raw39684 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39684step0 = (fun i j => raw39684 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39684step0 raw39684; decide +kernel
      have hl : raw39684step0Labels = raw39684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39684 raw39684Labels permutation434 hz
    mixedMoment B raw39684step0 raw39684step0Labels = mixedMoment B raw39684step1 raw39684step1Labels := by
      have hz : ∀ j, raw39684step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39684step1 = (fun i j => raw39684step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39684step1 raw39684step0; decide +kernel
      have hl : raw39684step1Labels = raw39684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39684step0 raw39684step0Labels permutation80 hz
    mixedMoment B raw39684step1 raw39684step1Labels = mixedMoment B raw39684step2 raw39684step2Labels := by
      have ha : raw39684step2 = (fun i j => raw39684step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39684step2 raw39684step1; decide +kernel
      have hl : raw39684step2Labels = raw39684step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39684step1 raw39684step1Labels permutation8 permutation3
    _ = mixedMoment B node501 node501Labels := by rfl

theorem canonical39685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39685 raw39685Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw39685 raw39685Labels = mixedMoment B raw39685step0 raw39685step0Labels := by
      have hz : ∀ j, raw39685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39685step0 = (fun i j => raw39685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39685step0 raw39685; decide +kernel
      have hl : raw39685step0Labels = raw39685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39685 raw39685Labels permutation434 hz
    mixedMoment B raw39685step0 raw39685step0Labels = mixedMoment B raw39685step1 raw39685step1Labels := by
      have hz : ∀ j, raw39685step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39685step1 = (fun i j => raw39685step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39685step1 raw39685step0; decide +kernel
      have hl : raw39685step1Labels = raw39685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39685step0 raw39685step0Labels permutation80 hz
    mixedMoment B raw39685step1 raw39685step1Labels = mixedMoment B raw39685step2 raw39685step2Labels := by
      have ha : raw39685step2 = (fun i j => raw39685step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39685step2 raw39685step1; decide +kernel
      have hl : raw39685step2Labels = raw39685step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39685step1 raw39685step1Labels permutation31 permutation2
    mixedMoment B raw39685step2 raw39685step2Labels = mixedMoment B raw39685step3 raw39685step3Labels := by
      have ha : raw39685step3 = -raw39685step2 := by apply Matrix.ext; change ∀ i j, raw39685step3 i j = -(raw39685step2 i j); unfold raw39685step3 raw39685step2; decide +kernel
      have hl : raw39685step3Labels = raw39685step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node496 node496Labels := by rfl

theorem canonical39686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39686 raw39686Labels = mixedMoment B node410 node410Labels := by
  calc
    mixedMoment B raw39686 raw39686Labels = mixedMoment B raw39686step0 raw39686step0Labels := by
      have hz : ∀ j, raw39686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39686step0 = (fun i j => raw39686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39686step0 raw39686; decide +kernel
      have hl : raw39686step0Labels = raw39686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39686 raw39686Labels permutation434 hz
    mixedMoment B raw39686step0 raw39686step0Labels = mixedMoment B raw39686step1 raw39686step1Labels := by
      have hz : ∀ j, raw39686step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39686step1 = (fun i j => raw39686step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39686step1 raw39686step0; decide +kernel
      have hl : raw39686step1Labels = raw39686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39686step0 raw39686step0Labels permutation80 hz
    mixedMoment B raw39686step1 raw39686step1Labels = mixedMoment B raw39686step2 raw39686step2Labels := by
      have ha : raw39686step2 = (fun i j => raw39686step1 (permutation27 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39686step2 raw39686step1; decide +kernel
      have hl : raw39686step2Labels = raw39686step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39686step1 raw39686step1Labels permutation27 permutation7
    _ = mixedMoment B node410 node410Labels := by rfl

theorem canonical39687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39687 raw39687Labels = mixedMoment B node498 node498Labels := by
  calc
    mixedMoment B raw39687 raw39687Labels = mixedMoment B raw39687step0 raw39687step0Labels := by
      have hz : ∀ j, raw39687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39687step0 = (fun i j => raw39687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39687step0 raw39687; decide +kernel
      have hl : raw39687step0Labels = raw39687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39687 raw39687Labels permutation346 hz
    mixedMoment B raw39687step0 raw39687step0Labels = mixedMoment B raw39687step1 raw39687step1Labels := by
      have ha : raw39687step1 = (fun i j => raw39687step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39687step1 raw39687step0; decide +kernel
      have hl : raw39687step1Labels = raw39687step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39687step0 raw39687step0Labels permutation40 permutation5
    mixedMoment B raw39687step1 raw39687step1Labels = mixedMoment B raw39687step2 raw39687step2Labels := by
      have ha : raw39687step2 = -raw39687step1 := by apply Matrix.ext; change ∀ i j, raw39687step2 i j = -(raw39687step1 i j); unfold raw39687step2 raw39687step1; decide +kernel
      have hl : raw39687step2Labels = raw39687step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node498 node498Labels := by rfl

theorem canonical39688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39688 raw39688Labels = mixedMoment B node500 node500Labels := by
  calc
    mixedMoment B raw39688 raw39688Labels = mixedMoment B raw39688step0 raw39688step0Labels := by
      have hz : ∀ j, raw39688 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39688step0 = (fun i j => raw39688 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39688step0 raw39688; decide +kernel
      have hl : raw39688step0Labels = raw39688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39688 raw39688Labels permutation346 hz
    mixedMoment B raw39688step0 raw39688step0Labels = mixedMoment B raw39688step1 raw39688step1Labels := by
      have ha : raw39688step1 = (fun i j => raw39688step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39688step1 raw39688step0; decide +kernel
      have hl : raw39688step1Labels = raw39688step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39688step0 raw39688step0Labels permutation32 permutation3
    _ = mixedMoment B node500 node500Labels := by rfl

theorem canonical39689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39689 raw39689Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39689 raw39689Labels = mixedMoment B raw39689step0 raw39689step0Labels := by
      have hz : ∀ j, raw39689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39689step0 = (fun i j => raw39689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39689step0 raw39689; decide +kernel
      have hl : raw39689step0Labels = raw39689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39689 raw39689Labels permutation434 hz
    mixedMoment B raw39689step0 raw39689step0Labels = mixedMoment B raw39689step1 raw39689step1Labels := by
      have ha : raw39689step1 = (fun i j => raw39689step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39689step1 raw39689step0; decide +kernel
      have hl : raw39689step1Labels = raw39689step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39689step0 raw39689step0Labels permutation68 permutation6
    mixedMoment B raw39689step1 raw39689step1Labels = mixedMoment B raw39689step2 raw39689step2Labels := by
      have ha : raw39689step2 = -raw39689step1 := by apply Matrix.ext; change ∀ i j, raw39689step2 i j = -(raw39689step1 i j); unfold raw39689step2 raw39689step1; decide +kernel
      have hl : raw39689step2Labels = raw39689step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node384 node384Labels := by rfl

theorem canonical39690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39690 raw39690Labels = mixedMoment B node385 node385Labels := by
  calc
    mixedMoment B raw39690 raw39690Labels = mixedMoment B raw39690step0 raw39690step0Labels := by
      have hz : ∀ j, raw39690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39690step0 = (fun i j => raw39690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39690step0 raw39690; decide +kernel
      have hl : raw39690step0Labels = raw39690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39690 raw39690Labels permutation434 hz
    mixedMoment B raw39690step0 raw39690step0Labels = mixedMoment B raw39690step1 raw39690step1Labels := by
      have hz : ∀ j, raw39690step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39690step1 = (fun i j => raw39690step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39690step1 raw39690step0; decide +kernel
      have hl : raw39690step1Labels = raw39690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39690step0 raw39690step0Labels permutation80 hz
    mixedMoment B raw39690step1 raw39690step1Labels = mixedMoment B raw39690step2 raw39690step2Labels := by
      have ha : raw39690step2 = (fun i j => raw39690step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39690step2 raw39690step1; decide +kernel
      have hl : raw39690step2Labels = raw39690step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39690step1 raw39690step1Labels permutation16 permutation6
    mixedMoment B raw39690step2 raw39690step2Labels = mixedMoment B raw39690step3 raw39690step3Labels := by
      have ha : raw39690step3 = -raw39690step2 := by apply Matrix.ext; change ∀ i j, raw39690step3 i j = -(raw39690step2 i j); unfold raw39690step3 raw39690step2; decide +kernel
      have hl : raw39690step3Labels = raw39690step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node385 node385Labels := by rfl

theorem canonical39691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39691 raw39691Labels = mixedMoment B node495 node495Labels := by
  calc
    mixedMoment B raw39691 raw39691Labels = mixedMoment B raw39691step0 raw39691step0Labels := by
      have hz : ∀ j, raw39691 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39691step0 = (fun i j => raw39691 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39691step0 raw39691; decide +kernel
      have hl : raw39691step0Labels = raw39691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39691 raw39691Labels permutation434 hz
    mixedMoment B raw39691step0 raw39691step0Labels = mixedMoment B raw39691step1 raw39691step1Labels := by
      have hz : ∀ j, raw39691step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39691step1 = (fun i j => raw39691step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39691step1 raw39691step0; decide +kernel
      have hl : raw39691step1Labels = raw39691step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39691step0 raw39691step0Labels permutation80 hz
    mixedMoment B raw39691step1 raw39691step1Labels = mixedMoment B raw39691step2 raw39691step2Labels := by
      have ha : raw39691step2 = (fun i j => raw39691step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39691step2 raw39691step1; decide +kernel
      have hl : raw39691step2Labels = raw39691step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39691step1 raw39691step1Labels permutation31 permutation5
    _ = mixedMoment B node495 node495Labels := by rfl

theorem canonical39692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39692 raw39692Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw39692 raw39692Labels = mixedMoment B raw39692step0 raw39692step0Labels := by
      have hz : ∀ j, raw39692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39692step0 = (fun i j => raw39692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39692step0 raw39692; decide +kernel
      have hl : raw39692step0Labels = raw39692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39692 raw39692Labels permutation434 hz
    mixedMoment B raw39692step0 raw39692step0Labels = mixedMoment B raw39692step1 raw39692step1Labels := by
      have hz : ∀ j, raw39692step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39692step1 = (fun i j => raw39692step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39692step1 raw39692step0; decide +kernel
      have hl : raw39692step1Labels = raw39692step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39692step0 raw39692step0Labels permutation80 hz
    mixedMoment B raw39692step1 raw39692step1Labels = mixedMoment B raw39692step2 raw39692step2Labels := by
      have ha : raw39692step2 = (fun i j => raw39692step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39692step2 raw39692step1; decide +kernel
      have hl : raw39692step2Labels = raw39692step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39692step1 raw39692step1Labels permutation31 permutation4
    _ = mixedMoment B node405 node405Labels := by rfl

theorem canonical39693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39693 raw39693Labels = mixedMoment B node5505 node5505Labels := by
  calc
    mixedMoment B raw39693 raw39693Labels = mixedMoment B raw39693step0 raw39693step0Labels := by
      have hz : ∀ j, raw39693 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39693step0 = (fun i j => raw39693 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39693step0 raw39693; decide +kernel
      have hl : raw39693step0Labels = raw39693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39693 raw39693Labels permutation434 hz
    mixedMoment B raw39693step0 raw39693step0Labels = mixedMoment B raw39693step1 raw39693step1Labels := by
      have hz : ∀ j, raw39693step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39693step1 = (fun i j => raw39693step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39693step1 raw39693step0; decide +kernel
      have hl : raw39693step1Labels = raw39693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39693step0 raw39693step0Labels permutation80 hz
    mixedMoment B raw39693step1 raw39693step1Labels = mixedMoment B raw39693step2 raw39693step2Labels := by
      have ha : raw39693step2 = (fun i j => raw39693step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39693step2 raw39693step1; decide +kernel
      have hl : raw39693step2Labels = raw39693step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39693step1 raw39693step1Labels permutation8 permutation5
    mixedMoment B raw39693step2 raw39693step2Labels = mixedMoment B raw39693step3 raw39693step3Labels := by
      have ha : raw39693step3 = -raw39693step2 := by apply Matrix.ext; change ∀ i j, raw39693step3 i j = -(raw39693step2 i j); unfold raw39693step3 raw39693step2; decide +kernel
      have hl : raw39693step3Labels = raw39693step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5505 node5505Labels := by rfl

theorem canonical39694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39694 raw39694Labels = mixedMoment B node468 node468Labels := by
  calc
    mixedMoment B raw39694 raw39694Labels = mixedMoment B raw39694step0 raw39694step0Labels := by
      have hz : ∀ j, raw39694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39694step0 = (fun i j => raw39694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39694step0 raw39694; decide +kernel
      have hl : raw39694step0Labels = raw39694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39694 raw39694Labels permutation346 hz
    mixedMoment B raw39694step0 raw39694step0Labels = mixedMoment B raw39694step1 raw39694step1Labels := by
      have ha : raw39694step1 = (fun i j => raw39694step0 (permutation121 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39694step1 raw39694step0; decide +kernel
      have hl : raw39694step1Labels = raw39694step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39694step0 raw39694step0Labels permutation121 permutation4
    _ = mixedMoment B node468 node468Labels := by rfl

theorem canonical39695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39695 raw39695Labels = mixedMoment B node489 node489Labels := by
  calc
    mixedMoment B raw39695 raw39695Labels = mixedMoment B raw39695step0 raw39695step0Labels := by
      have hz : ∀ j, raw39695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39695step0 = (fun i j => raw39695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39695step0 raw39695; decide +kernel
      have hl : raw39695step0Labels = raw39695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39695 raw39695Labels permutation346 hz
    mixedMoment B raw39695step0 raw39695step0Labels = mixedMoment B raw39695step1 raw39695step1Labels := by
      have ha : raw39695step1 = (fun i j => raw39695step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39695step1 raw39695step0; decide +kernel
      have hl : raw39695step1Labels = raw39695step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39695step0 raw39695step0Labels permutation34 permutation5
    mixedMoment B raw39695step1 raw39695step1Labels = mixedMoment B raw39695step2 raw39695step2Labels := by
      have ha : raw39695step2 = -raw39695step1 := by apply Matrix.ext; change ∀ i j, raw39695step2 i j = -(raw39695step1 i j); unfold raw39695step2 raw39695step1; decide +kernel
      have hl : raw39695step2Labels = raw39695step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node489 node489Labels := by rfl

theorem canonical39696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39696 raw39696Labels = mixedMoment B node490 node490Labels := by
  calc
    mixedMoment B raw39696 raw39696Labels = mixedMoment B raw39696step0 raw39696step0Labels := by
      have hz : ∀ j, raw39696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39696step0 = (fun i j => raw39696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39696step0 raw39696; decide +kernel
      have hl : raw39696step0Labels = raw39696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39696 raw39696Labels permutation346 hz
    mixedMoment B raw39696step0 raw39696step0Labels = mixedMoment B raw39696step1 raw39696step1Labels := by
      have ha : raw39696step1 = (fun i j => raw39696step0 (permutation103 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39696step1 raw39696step0; decide +kernel
      have hl : raw39696step1Labels = raw39696step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39696step0 raw39696step0Labels permutation103 permutation4
    _ = mixedMoment B node490 node490Labels := by rfl

theorem canonical39697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39697 raw39697Labels = mixedMoment B node261 node261Labels := by
  calc
    mixedMoment B raw39697 raw39697Labels = mixedMoment B raw39697step0 raw39697step0Labels := by
      have hz : ∀ j, raw39697 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39697step0 = (fun i j => raw39697 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39697step0 raw39697; decide +kernel
      have hl : raw39697step0Labels = raw39697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39697 raw39697Labels permutation346 hz
    mixedMoment B raw39697step0 raw39697step0Labels = mixedMoment B raw39697step1 raw39697step1Labels := by
      have ha : raw39697step1 = (fun i j => raw39697step0 (permutation97 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39697step1 raw39697step0; decide +kernel
      have hl : raw39697step1Labels = raw39697step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39697step0 raw39697step0Labels permutation97 permutation4
    _ = mixedMoment B node261 node261Labels := by rfl

theorem canonical39698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39698 raw39698Labels = mixedMoment B node462 node462Labels := by
  calc
    mixedMoment B raw39698 raw39698Labels = mixedMoment B raw39698step0 raw39698step0Labels := by
      have ha : raw39698step0 = (fun i j => raw39698 (permutation480 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39698step0 raw39698; decide +kernel
      have hl : raw39698step0Labels = raw39698Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39698 raw39698Labels permutation480 permutation4
    _ = mixedMoment B node462 node462Labels := by rfl

theorem canonical39699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39699 raw39699Labels = mixedMoment B node6 node6Labels := by
  calc
    mixedMoment B raw39699 raw39699Labels = mixedMoment B raw39699step0 raw39699step0Labels := by
      have hz : ∀ j, raw39699 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39699step0 = (fun i j => raw39699 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39699step0 raw39699; decide +kernel
      have hl : raw39699step0Labels = raw39699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39699 raw39699Labels permutation520 hz
    mixedMoment B raw39699step0 raw39699step0Labels = mixedMoment B raw39699step1 raw39699step1Labels := by
      have hz : ∀ j, raw39699step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39699step1 = (fun i j => raw39699step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39699step1 raw39699step0; decide +kernel
      have hl : raw39699step1Labels = raw39699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39699step0 raw39699step0Labels permutation104 hz
    mixedMoment B raw39699step1 raw39699step1Labels = mixedMoment B raw39699step2 raw39699step2Labels := by
      have hz : ∀ j, raw39699step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39699step2 = (fun i j => raw39699step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39699step2 raw39699step1; decide +kernel
      have hl : raw39699step2Labels = raw39699step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39699step1 raw39699step1Labels permutation20 hz
    mixedMoment B raw39699step2 raw39699step2Labels = mixedMoment B raw39699step3 raw39699step3Labels := by
      have hz : ∀ j, raw39699step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw39699step3 = (fun i j => raw39699step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw39699step3 raw39699step2; decide +kernel
      have hl : raw39699step3Labels = raw39699step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39699step2 raw39699step2Labels permutation4 hz
    mixedMoment B raw39699step3 raw39699step3Labels = mixedMoment B raw39699step4 raw39699step4Labels := by
      have hz : ∀ i, raw39699step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw39699step4 = (fun i j => raw39699step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw39699step4 raw39699step3; decide +kernel
      have hl : raw39699step4Labels = (fun j => raw39699step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw39699step3 raw39699step3Labels permutation6 hz
    _ = mixedMoment B node6 node6Labels := by rfl

theorem canonical39700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39700 raw39700Labels = mixedMoment B node507 node507Labels := by
  calc
    mixedMoment B raw39700 raw39700Labels = mixedMoment B raw39700step0 raw39700step0Labels := by
      have hz : ∀ j, raw39700 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39700step0 = (fun i j => raw39700 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39700step0 raw39700; decide +kernel
      have hl : raw39700step0Labels = raw39700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39700 raw39700Labels permutation434 hz
    mixedMoment B raw39700step0 raw39700step0Labels = mixedMoment B raw39700step1 raw39700step1Labels := by
      have hz : ∀ j, raw39700step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39700step1 = (fun i j => raw39700step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39700step1 raw39700step0; decide +kernel
      have hl : raw39700step1Labels = raw39700step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39700step0 raw39700step0Labels permutation80 hz
    mixedMoment B raw39700step1 raw39700step1Labels = mixedMoment B raw39700step2 raw39700step2Labels := by
      have hz : ∀ j, raw39700step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39700step2 = (fun i j => raw39700step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39700step2 raw39700step1; decide +kernel
      have hl : raw39700step2Labels = raw39700step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39700step1 raw39700step1Labels permutation14 hz
    mixedMoment B raw39700step2 raw39700step2Labels = mixedMoment B raw39700step3 raw39700step3Labels := by
      have ha : raw39700step3 = (fun i j => raw39700step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39700step3 raw39700step2; decide +kernel
      have hl : raw39700step3Labels = raw39700step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39700step2 raw39700step2Labels permutation7 permutation2
    mixedMoment B raw39700step3 raw39700step3Labels = mixedMoment B raw39700step4 raw39700step4Labels := by
      have ha : raw39700step4 = -raw39700step3 := by apply Matrix.ext; change ∀ i j, raw39700step4 i j = -(raw39700step3 i j); unfold raw39700step4 raw39700step3; decide +kernel
      have hl : raw39700step4Labels = raw39700step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node507 node507Labels := by rfl

theorem canonical39701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39701 raw39701Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw39701 raw39701Labels = mixedMoment B raw39701step0 raw39701step0Labels := by
      have hz : ∀ j, raw39701 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39701step0 = (fun i j => raw39701 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39701step0 raw39701; decide +kernel
      have hl : raw39701step0Labels = raw39701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39701 raw39701Labels permutation434 hz
    mixedMoment B raw39701step0 raw39701step0Labels = mixedMoment B raw39701step1 raw39701step1Labels := by
      have hz : ∀ j, raw39701step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39701step1 = (fun i j => raw39701step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39701step1 raw39701step0; decide +kernel
      have hl : raw39701step1Labels = raw39701step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39701step0 raw39701step0Labels permutation80 hz
    mixedMoment B raw39701step1 raw39701step1Labels = mixedMoment B raw39701step2 raw39701step2Labels := by
      have hz : ∀ j, raw39701step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39701step2 = (fun i j => raw39701step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39701step2 raw39701step1; decide +kernel
      have hl : raw39701step2Labels = raw39701step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39701step1 raw39701step1Labels permutation14 hz
    mixedMoment B raw39701step2 raw39701step2Labels = mixedMoment B raw39701step3 raw39701step3Labels := by
      have ha : raw39701step3 = (fun i j => raw39701step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39701step3 raw39701step2; decide +kernel
      have hl : raw39701step3Labels = raw39701step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39701step2 raw39701step2Labels permutation7 permutation4
    _ = mixedMoment B node420 node420Labels := by rfl

theorem canonical39702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39702 raw39702Labels = mixedMoment B node5 node5Labels := by
  calc
    mixedMoment B raw39702 raw39702Labels = mixedMoment B raw39702step0 raw39702step0Labels := by
      have hz : ∀ j, raw39702 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39702step0 = (fun i j => raw39702 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39702step0 raw39702; decide +kernel
      have hl : raw39702step0Labels = raw39702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39702 raw39702Labels permutation434 hz
    mixedMoment B raw39702step0 raw39702step0Labels = mixedMoment B raw39702step1 raw39702step1Labels := by
      have hz : ∀ j, raw39702step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39702step1 = (fun i j => raw39702step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39702step1 raw39702step0; decide +kernel
      have hl : raw39702step1Labels = raw39702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39702step0 raw39702step0Labels permutation80 hz
    mixedMoment B raw39702step1 raw39702step1Labels = mixedMoment B raw39702step2 raw39702step2Labels := by
      have hz : ∀ j, raw39702step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39702step2 = (fun i j => raw39702step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39702step2 raw39702step1; decide +kernel
      have hl : raw39702step2Labels = raw39702step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39702step1 raw39702step1Labels permutation14 hz
    mixedMoment B raw39702step2 raw39702step2Labels = mixedMoment B raw39702step3 raw39702step3Labels := by
      have hz : ∀ i, raw39702step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw39702step3 = (fun i j => raw39702step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw39702step3 raw39702step2; decide +kernel
      have hl : raw39702step3Labels = (fun j => raw39702step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw39702step2 raw39702step2Labels permutation6 hz
    _ = mixedMoment B node5 node5Labels := by rfl

theorem canonical39703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39703 raw39703Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw39703 raw39703Labels = mixedMoment B raw39703step0 raw39703step0Labels := by
      have hz : ∀ j, raw39703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39703step0 = (fun i j => raw39703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39703step0 raw39703; decide +kernel
      have hl : raw39703step0Labels = raw39703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39703 raw39703Labels permutation346 hz
    mixedMoment B raw39703step0 raw39703step0Labels = mixedMoment B raw39703step1 raw39703step1Labels := by
      have hz : ∀ j, raw39703step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39703step1 = (fun i j => raw39703step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39703step1 raw39703step0; decide +kernel
      have hl : raw39703step1Labels = raw39703step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39703step0 raw39703step0Labels permutation56 hz
    mixedMoment B raw39703step1 raw39703step1Labels = mixedMoment B raw39703step2 raw39703step2Labels := by
      have ha : raw39703step2 = (fun i j => raw39703step1 (permutation26 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39703step2 raw39703step1; decide +kernel
      have hl : raw39703step2Labels = raw39703step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39703step1 raw39703step1Labels permutation26 permutation7
    _ = mixedMoment B node412 node412Labels := by rfl

theorem canonical39704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39704 raw39704Labels = mixedMoment B node503 node503Labels := by
  calc
    mixedMoment B raw39704 raw39704Labels = mixedMoment B raw39704step0 raw39704step0Labels := by
      have hz : ∀ j, raw39704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39704step0 = (fun i j => raw39704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39704step0 raw39704; decide +kernel
      have hl : raw39704step0Labels = raw39704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39704 raw39704Labels permutation346 hz
    mixedMoment B raw39704step0 raw39704step0Labels = mixedMoment B raw39704step1 raw39704step1Labels := by
      have hz : ∀ j, raw39704step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39704step1 = (fun i j => raw39704step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39704step1 raw39704step0; decide +kernel
      have hl : raw39704step1Labels = raw39704step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39704step0 raw39704step0Labels permutation56 hz
    mixedMoment B raw39704step1 raw39704step1Labels = mixedMoment B raw39704step2 raw39704step2Labels := by
      have ha : raw39704step2 = (fun i j => raw39704step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39704step2 raw39704step1; decide +kernel
      have hl : raw39704step2Labels = raw39704step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39704step1 raw39704step1Labels permutation10 permutation5
    mixedMoment B raw39704step2 raw39704step2Labels = mixedMoment B raw39704step3 raw39704step3Labels := by
      have ha : raw39704step3 = -raw39704step2 := by apply Matrix.ext; change ∀ i j, raw39704step3 i j = -(raw39704step2 i j); unfold raw39704step3 raw39704step2; decide +kernel
      have hl : raw39704step3Labels = raw39704step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node503 node503Labels := by rfl

theorem canonical39705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39705 raw39705Labels = mixedMoment B node506 node506Labels := by
  calc
    mixedMoment B raw39705 raw39705Labels = mixedMoment B raw39705step0 raw39705step0Labels := by
      have hz : ∀ j, raw39705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39705step0 = (fun i j => raw39705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39705step0 raw39705; decide +kernel
      have hl : raw39705step0Labels = raw39705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39705 raw39705Labels permutation346 hz
    mixedMoment B raw39705step0 raw39705step0Labels = mixedMoment B raw39705step1 raw39705step1Labels := by
      have hz : ∀ j, raw39705step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39705step1 = (fun i j => raw39705step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39705step1 raw39705step0; decide +kernel
      have hl : raw39705step1Labels = raw39705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39705step0 raw39705step0Labels permutation56 hz
    mixedMoment B raw39705step1 raw39705step1Labels = mixedMoment B raw39705step2 raw39705step2Labels := by
      have ha : raw39705step2 = (fun i j => raw39705step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39705step2 raw39705step1; decide +kernel
      have hl : raw39705step2Labels = raw39705step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39705step1 raw39705step1Labels permutation8 permutation3
    _ = mixedMoment B node506 node506Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 224) =
      Integer.Sparse.eval keyMomentRow224 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 224).leftCharge (GramAssembly.key 224).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 487) := by
    have ha : gramCharges (GramAssembly.key 224).leftCharge (GramAssembly.key 224).rightCharge = raw39674 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39674Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39674 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 224).leftCharge (GramAssembly.key 224).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow224, Integer.Sparse.eval]

theorem keyMoment225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 225) =
      Integer.Sparse.eval keyMomentRow225 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 225).leftCharge (GramAssembly.key 225).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 490) := by
    have ha : gramCharges (GramAssembly.key 225).leftCharge (GramAssembly.key 225).rightCharge = raw39675 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39675Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39675 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 225).leftCharge (GramAssembly.key 225).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow225, Integer.Sparse.eval]

theorem keyMoment226 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 226) =
      Integer.Sparse.eval keyMomentRow226 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 226).leftCharge (GramAssembly.key 226).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 409) := by
    have ha : gramCharges (GramAssembly.key 226).leftCharge (GramAssembly.key 226).rightCharge = raw39676 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39676Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39676 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 226).leftCharge (GramAssembly.key 226).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow226, Integer.Sparse.eval]

theorem keyMoment227 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 227) =
      Integer.Sparse.eval keyMomentRow227 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 227).leftCharge (GramAssembly.key 227).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 227).leftCharge (GramAssembly.key 227).rightCharge = raw39677 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39677Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39677 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 227).leftCharge (GramAssembly.key 227).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow227, Integer.Sparse.eval]

theorem keyMoment228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 228) =
      Integer.Sparse.eval keyMomentRow228 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 228).leftCharge (GramAssembly.key 228).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 485) := by
    have ha : gramCharges (GramAssembly.key 228).leftCharge (GramAssembly.key 228).rightCharge = raw39678 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39678Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39678 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 228).leftCharge (GramAssembly.key 228).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow228, Integer.Sparse.eval]

theorem keyMoment229 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 229) =
      Integer.Sparse.eval keyMomentRow229 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 229).leftCharge (GramAssembly.key 229).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 486) := by
    have ha : gramCharges (GramAssembly.key 229).leftCharge (GramAssembly.key 229).rightCharge = raw39679 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39679Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39679 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 229).leftCharge (GramAssembly.key 229).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow229, Integer.Sparse.eval]

theorem keyMoment230 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 230) =
      Integer.Sparse.eval keyMomentRow230 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 230).leftCharge (GramAssembly.key 230).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 487) := by
    have ha : gramCharges (GramAssembly.key 230).leftCharge (GramAssembly.key 230).rightCharge = raw39680 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39680Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39680 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 230).leftCharge (GramAssembly.key 230).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow230, Integer.Sparse.eval]

theorem keyMoment231 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 231) =
      Integer.Sparse.eval keyMomentRow231 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 231).leftCharge (GramAssembly.key 231).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 491) := by
    have ha : gramCharges (GramAssembly.key 231).leftCharge (GramAssembly.key 231).rightCharge = raw39681 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39681Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39681 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 231).leftCharge (GramAssembly.key 231).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow231, Integer.Sparse.eval]

theorem keyMoment232 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 232) =
      Integer.Sparse.eval keyMomentRow232 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 232).leftCharge (GramAssembly.key 232).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 484) := by
    have ha : gramCharges (GramAssembly.key 232).leftCharge (GramAssembly.key 232).rightCharge = raw39682 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39682Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39682 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 232).leftCharge (GramAssembly.key 232).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow232, Integer.Sparse.eval]

theorem keyMoment233 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 233) =
      Integer.Sparse.eval keyMomentRow233 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 233).leftCharge (GramAssembly.key 233).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 486) := by
    have ha : gramCharges (GramAssembly.key 233).leftCharge (GramAssembly.key 233).rightCharge = raw39683 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39683Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39683 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 233).leftCharge (GramAssembly.key 233).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow233, Integer.Sparse.eval]

theorem keyMoment234 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 234) =
      Integer.Sparse.eval keyMomentRow234 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 234).leftCharge (GramAssembly.key 234).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 501) := by
    have ha : gramCharges (GramAssembly.key 234).leftCharge (GramAssembly.key 234).rightCharge = raw39684 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39684Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39684 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 234).leftCharge (GramAssembly.key 234).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow234, Integer.Sparse.eval]

theorem keyMoment235 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 235) =
      Integer.Sparse.eval keyMomentRow235 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 235).leftCharge (GramAssembly.key 235).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 496) := by
    have ha : gramCharges (GramAssembly.key 235).leftCharge (GramAssembly.key 235).rightCharge = raw39685 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39685Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39685 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 235).leftCharge (GramAssembly.key 235).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow235, Integer.Sparse.eval]

theorem keyMoment236 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 236) =
      Integer.Sparse.eval keyMomentRow236 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 236).leftCharge (GramAssembly.key 236).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 410) := by
    have ha : gramCharges (GramAssembly.key 236).leftCharge (GramAssembly.key 236).rightCharge = raw39686 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39686Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39686 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 236).leftCharge (GramAssembly.key 236).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow236, Integer.Sparse.eval]

theorem keyMoment237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 237) =
      Integer.Sparse.eval keyMomentRow237 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 237).leftCharge (GramAssembly.key 237).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 498) := by
    have ha : gramCharges (GramAssembly.key 237).leftCharge (GramAssembly.key 237).rightCharge = raw39687 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39687Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39687 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 237).leftCharge (GramAssembly.key 237).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow237, Integer.Sparse.eval]

theorem keyMoment238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 238) =
      Integer.Sparse.eval keyMomentRow238 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 238).leftCharge (GramAssembly.key 238).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 500) := by
    have ha : gramCharges (GramAssembly.key 238).leftCharge (GramAssembly.key 238).rightCharge = raw39688 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39688Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39688 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 238).leftCharge (GramAssembly.key 238).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow238, Integer.Sparse.eval]

theorem keyMoment239 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 239) =
      Integer.Sparse.eval keyMomentRow239 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 239).leftCharge (GramAssembly.key 239).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 239).leftCharge (GramAssembly.key 239).rightCharge = raw39689 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39689Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39689 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 239).leftCharge (GramAssembly.key 239).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow239, Integer.Sparse.eval]

theorem keyMoment240 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 240) =
      Integer.Sparse.eval keyMomentRow240 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 240).leftCharge (GramAssembly.key 240).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 385) := by
    have ha : gramCharges (GramAssembly.key 240).leftCharge (GramAssembly.key 240).rightCharge = raw39690 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39690Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39690 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 240).leftCharge (GramAssembly.key 240).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow240, Integer.Sparse.eval]

theorem keyMoment241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 241) =
      Integer.Sparse.eval keyMomentRow241 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 241).leftCharge (GramAssembly.key 241).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 495) := by
    have ha : gramCharges (GramAssembly.key 241).leftCharge (GramAssembly.key 241).rightCharge = raw39691 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39691Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39691 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 241).leftCharge (GramAssembly.key 241).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow241, Integer.Sparse.eval]

theorem keyMoment242 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 242) =
      Integer.Sparse.eval keyMomentRow242 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 242).leftCharge (GramAssembly.key 242).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 405) := by
    have ha : gramCharges (GramAssembly.key 242).leftCharge (GramAssembly.key 242).rightCharge = raw39692 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39692Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39692 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 242).leftCharge (GramAssembly.key 242).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow242, Integer.Sparse.eval]

theorem keyMoment243 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 243) =
      Integer.Sparse.eval keyMomentRow243 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 243).leftCharge (GramAssembly.key 243).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 3) := by
    have ha : gramCharges (GramAssembly.key 243).leftCharge (GramAssembly.key 243).rightCharge = raw39693 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39693Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39693 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 243).leftCharge (GramAssembly.key 243).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow243, Integer.Sparse.eval]

theorem keyMoment244 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 244) =
      Integer.Sparse.eval keyMomentRow244 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 244).leftCharge (GramAssembly.key 244).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 468) := by
    have ha : gramCharges (GramAssembly.key 244).leftCharge (GramAssembly.key 244).rightCharge = raw39694 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39694Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39694 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 244).leftCharge (GramAssembly.key 244).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow244, Integer.Sparse.eval]

theorem keyMoment245 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 245) =
      Integer.Sparse.eval keyMomentRow245 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 245).leftCharge (GramAssembly.key 245).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 489) := by
    have ha : gramCharges (GramAssembly.key 245).leftCharge (GramAssembly.key 245).rightCharge = raw39695 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39695Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39695 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 245).leftCharge (GramAssembly.key 245).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow245, Integer.Sparse.eval]

theorem keyMoment246 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 246) =
      Integer.Sparse.eval keyMomentRow246 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 246).leftCharge (GramAssembly.key 246).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 490) := by
    have ha : gramCharges (GramAssembly.key 246).leftCharge (GramAssembly.key 246).rightCharge = raw39696 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39696Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39696 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 246).leftCharge (GramAssembly.key 246).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow246, Integer.Sparse.eval]

theorem keyMoment247 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 247) =
      Integer.Sparse.eval keyMomentRow247 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 247).leftCharge (GramAssembly.key 247).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 261) := by
    have ha : gramCharges (GramAssembly.key 247).leftCharge (GramAssembly.key 247).rightCharge = raw39697 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39697Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39697 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 247).leftCharge (GramAssembly.key 247).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow247, Integer.Sparse.eval]

theorem keyMoment248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 248) =
      Integer.Sparse.eval keyMomentRow248 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 248).leftCharge (GramAssembly.key 248).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 462) := by
    have ha : gramCharges (GramAssembly.key 248).leftCharge (GramAssembly.key 248).rightCharge = raw39698 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39698Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39698 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 248).leftCharge (GramAssembly.key 248).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow248, Integer.Sparse.eval]

theorem keyMoment249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 249) =
      Integer.Sparse.eval keyMomentRow249 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 249).leftCharge (GramAssembly.key 249).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 6) := by
    have ha : gramCharges (GramAssembly.key 249).leftCharge (GramAssembly.key 249).rightCharge = raw39699 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39699Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39699 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 249).leftCharge (GramAssembly.key 249).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow249, Integer.Sparse.eval]

theorem keyMoment250 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 250) =
      Integer.Sparse.eval keyMomentRow250 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 250).leftCharge (GramAssembly.key 250).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 507) := by
    have ha : gramCharges (GramAssembly.key 250).leftCharge (GramAssembly.key 250).rightCharge = raw39700 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39700Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39700 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 250).leftCharge (GramAssembly.key 250).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow250, Integer.Sparse.eval]

theorem keyMoment251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 251) =
      Integer.Sparse.eval keyMomentRow251 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 251).leftCharge (GramAssembly.key 251).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 420) := by
    have ha : gramCharges (GramAssembly.key 251).leftCharge (GramAssembly.key 251).rightCharge = raw39701 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39701Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39701 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 251).leftCharge (GramAssembly.key 251).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow251, Integer.Sparse.eval]

theorem keyMoment252 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 252) =
      Integer.Sparse.eval keyMomentRow252 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 252).leftCharge (GramAssembly.key 252).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 5) := by
    have ha : gramCharges (GramAssembly.key 252).leftCharge (GramAssembly.key 252).rightCharge = raw39702 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39702Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39702 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 252).leftCharge (GramAssembly.key 252).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow252, Integer.Sparse.eval]

theorem keyMoment253 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 253) =
      Integer.Sparse.eval keyMomentRow253 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 253).leftCharge (GramAssembly.key 253).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 412) := by
    have ha : gramCharges (GramAssembly.key 253).leftCharge (GramAssembly.key 253).rightCharge = raw39703 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39703Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39703 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 253).leftCharge (GramAssembly.key 253).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow253, Integer.Sparse.eval]

theorem keyMoment254 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 254) =
      Integer.Sparse.eval keyMomentRow254 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 254).leftCharge (GramAssembly.key 254).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 503) := by
    have ha : gramCharges (GramAssembly.key 254).leftCharge (GramAssembly.key 254).rightCharge = raw39704 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39704Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39704 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 254).leftCharge (GramAssembly.key 254).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow254, Integer.Sparse.eval]

theorem keyMoment255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 255) =
      Integer.Sparse.eval keyMomentRow255 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 255).leftCharge (GramAssembly.key 255).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 506) := by
    have ha : gramCharges (GramAssembly.key 255).leftCharge (GramAssembly.key 255).rightCharge = raw39705 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39705Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39705 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 255).leftCharge (GramAssembly.key 255).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow255, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt224 : keyMomentRows (224 : Fin 2886) =
    keyMomentRow224 := by decide +kernel

theorem keyMomentRowsAt225 : keyMomentRows (225 : Fin 2886) =
    keyMomentRow225 := by decide +kernel

theorem keyMomentRowsAt226 : keyMomentRows (226 : Fin 2886) =
    keyMomentRow226 := by decide +kernel

theorem keyMomentRowsAt227 : keyMomentRows (227 : Fin 2886) =
    keyMomentRow227 := by decide +kernel

theorem keyMomentRowsAt228 : keyMomentRows (228 : Fin 2886) =
    keyMomentRow228 := by decide +kernel

theorem keyMomentRowsAt229 : keyMomentRows (229 : Fin 2886) =
    keyMomentRow229 := by decide +kernel

theorem keyMomentRowsAt230 : keyMomentRows (230 : Fin 2886) =
    keyMomentRow230 := by decide +kernel

theorem keyMomentRowsAt231 : keyMomentRows (231 : Fin 2886) =
    keyMomentRow231 := by decide +kernel

theorem keyMomentRowsAt232 : keyMomentRows (232 : Fin 2886) =
    keyMomentRow232 := by decide +kernel

theorem keyMomentRowsAt233 : keyMomentRows (233 : Fin 2886) =
    keyMomentRow233 := by decide +kernel

theorem keyMomentRowsAt234 : keyMomentRows (234 : Fin 2886) =
    keyMomentRow234 := by decide +kernel

theorem keyMomentRowsAt235 : keyMomentRows (235 : Fin 2886) =
    keyMomentRow235 := by decide +kernel

theorem keyMomentRowsAt236 : keyMomentRows (236 : Fin 2886) =
    keyMomentRow236 := by decide +kernel

theorem keyMomentRowsAt237 : keyMomentRows (237 : Fin 2886) =
    keyMomentRow237 := by decide +kernel

theorem keyMomentRowsAt238 : keyMomentRows (238 : Fin 2886) =
    keyMomentRow238 := by decide +kernel

theorem keyMomentRowsAt239 : keyMomentRows (239 : Fin 2886) =
    keyMomentRow239 := by decide +kernel

theorem keyMomentRowsAt240 : keyMomentRows (240 : Fin 2886) =
    keyMomentRow240 := by decide +kernel

theorem keyMomentRowsAt241 : keyMomentRows (241 : Fin 2886) =
    keyMomentRow241 := by decide +kernel

theorem keyMomentRowsAt242 : keyMomentRows (242 : Fin 2886) =
    keyMomentRow242 := by decide +kernel

theorem keyMomentRowsAt243 : keyMomentRows (243 : Fin 2886) =
    keyMomentRow243 := by decide +kernel

theorem keyMomentRowsAt244 : keyMomentRows (244 : Fin 2886) =
    keyMomentRow244 := by decide +kernel

theorem keyMomentRowsAt245 : keyMomentRows (245 : Fin 2886) =
    keyMomentRow245 := by decide +kernel

theorem keyMomentRowsAt246 : keyMomentRows (246 : Fin 2886) =
    keyMomentRow246 := by decide +kernel

theorem keyMomentRowsAt247 : keyMomentRows (247 : Fin 2886) =
    keyMomentRow247 := by decide +kernel

theorem keyMomentRowsAt248 : keyMomentRows (248 : Fin 2886) =
    keyMomentRow248 := by decide +kernel

theorem keyMomentRowsAt249 : keyMomentRows (249 : Fin 2886) =
    keyMomentRow249 := by decide +kernel

theorem keyMomentRowsAt250 : keyMomentRows (250 : Fin 2886) =
    keyMomentRow250 := by decide +kernel

theorem keyMomentRowsAt251 : keyMomentRows (251 : Fin 2886) =
    keyMomentRow251 := by decide +kernel

theorem keyMomentRowsAt252 : keyMomentRows (252 : Fin 2886) =
    keyMomentRow252 := by decide +kernel

theorem keyMomentRowsAt253 : keyMomentRows (253 : Fin 2886) =
    keyMomentRow253 := by decide +kernel

theorem keyMomentRowsAt254 : keyMomentRows (254 : Fin 2886) =
    keyMomentRow254 := by decide +kernel

theorem keyMomentRowsAt255 : keyMomentRows (255 : Fin 2886) =
    keyMomentRow255 := by decide +kernel

theorem keyMomentChunkSound7_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 7) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 224 ∨ k.val = 225 ∨ k.val = 226 ∨ k.val = 227 ∨ k.val = 228 ∨ k.val = 229 ∨ k.val = 230 ∨ k.val = 231 ∨ k.val = 232 ∨ k.val = 233 ∨ k.val = 234 ∨ k.val = 235 ∨ k.val = 236 ∨ k.val = 237 ∨ k.val = 238 ∨ k.val = 239 ∨ k.val = 240 ∨ k.val = 241 ∨ k.val = 242 ∨ k.val = 243 ∨ k.val = 244 ∨ k.val = 245 ∨ k.val = 246 ∨ k.val = 247 ∨ k.val = 248 ∨ k.val = 249 ∨ k.val = 250 ∨ k.val = 251 ∨ k.val = 252 ∨ k.val = 253 ∨ k.val = 254 ∨ k.val = 255 := by omega
  rcases heq with h224 | h225 | h226 | h227 | h228 | h229 | h230 | h231 | h232 | h233 | h234 | h235 | h236 | h237 | h238 | h239 | h240 | h241 | h242 | h243 | h244 | h245 | h246 | h247 | h248 | h249 | h250 | h251 | h252 | h253 | h254 | h255
  · have he : k = (224 : Fin 2886) := Fin.ext h224
    subst k
    rw [keyMomentRowsAt224]
    exact keyMoment224 B hB
  · have he : k = (225 : Fin 2886) := Fin.ext h225
    subst k
    rw [keyMomentRowsAt225]
    exact keyMoment225 B hB
  · have he : k = (226 : Fin 2886) := Fin.ext h226
    subst k
    rw [keyMomentRowsAt226]
    exact keyMoment226 B hB
  · have he : k = (227 : Fin 2886) := Fin.ext h227
    subst k
    rw [keyMomentRowsAt227]
    exact keyMoment227 B hB
  · have he : k = (228 : Fin 2886) := Fin.ext h228
    subst k
    rw [keyMomentRowsAt228]
    exact keyMoment228 B hB
  · have he : k = (229 : Fin 2886) := Fin.ext h229
    subst k
    rw [keyMomentRowsAt229]
    exact keyMoment229 B hB
  · have he : k = (230 : Fin 2886) := Fin.ext h230
    subst k
    rw [keyMomentRowsAt230]
    exact keyMoment230 B hB
  · have he : k = (231 : Fin 2886) := Fin.ext h231
    subst k
    rw [keyMomentRowsAt231]
    exact keyMoment231 B hB
  · have he : k = (232 : Fin 2886) := Fin.ext h232
    subst k
    rw [keyMomentRowsAt232]
    exact keyMoment232 B hB
  · have he : k = (233 : Fin 2886) := Fin.ext h233
    subst k
    rw [keyMomentRowsAt233]
    exact keyMoment233 B hB
  · have he : k = (234 : Fin 2886) := Fin.ext h234
    subst k
    rw [keyMomentRowsAt234]
    exact keyMoment234 B hB
  · have he : k = (235 : Fin 2886) := Fin.ext h235
    subst k
    rw [keyMomentRowsAt235]
    exact keyMoment235 B hB
  · have he : k = (236 : Fin 2886) := Fin.ext h236
    subst k
    rw [keyMomentRowsAt236]
    exact keyMoment236 B hB
  · have he : k = (237 : Fin 2886) := Fin.ext h237
    subst k
    rw [keyMomentRowsAt237]
    exact keyMoment237 B hB
  · have he : k = (238 : Fin 2886) := Fin.ext h238
    subst k
    rw [keyMomentRowsAt238]
    exact keyMoment238 B hB
  · have he : k = (239 : Fin 2886) := Fin.ext h239
    subst k
    rw [keyMomentRowsAt239]
    exact keyMoment239 B hB
  · have he : k = (240 : Fin 2886) := Fin.ext h240
    subst k
    rw [keyMomentRowsAt240]
    exact keyMoment240 B hB
  · have he : k = (241 : Fin 2886) := Fin.ext h241
    subst k
    rw [keyMomentRowsAt241]
    exact keyMoment241 B hB
  · have he : k = (242 : Fin 2886) := Fin.ext h242
    subst k
    rw [keyMomentRowsAt242]
    exact keyMoment242 B hB
  · have he : k = (243 : Fin 2886) := Fin.ext h243
    subst k
    rw [keyMomentRowsAt243]
    exact keyMoment243 B hB
  · have he : k = (244 : Fin 2886) := Fin.ext h244
    subst k
    rw [keyMomentRowsAt244]
    exact keyMoment244 B hB
  · have he : k = (245 : Fin 2886) := Fin.ext h245
    subst k
    rw [keyMomentRowsAt245]
    exact keyMoment245 B hB
  · have he : k = (246 : Fin 2886) := Fin.ext h246
    subst k
    rw [keyMomentRowsAt246]
    exact keyMoment246 B hB
  · have he : k = (247 : Fin 2886) := Fin.ext h247
    subst k
    rw [keyMomentRowsAt247]
    exact keyMoment247 B hB
  · have he : k = (248 : Fin 2886) := Fin.ext h248
    subst k
    rw [keyMomentRowsAt248]
    exact keyMoment248 B hB
  · have he : k = (249 : Fin 2886) := Fin.ext h249
    subst k
    rw [keyMomentRowsAt249]
    exact keyMoment249 B hB
  · have he : k = (250 : Fin 2886) := Fin.ext h250
    subst k
    rw [keyMomentRowsAt250]
    exact keyMoment250 B hB
  · have he : k = (251 : Fin 2886) := Fin.ext h251
    subst k
    rw [keyMomentRowsAt251]
    exact keyMoment251 B hB
  · have he : k = (252 : Fin 2886) := Fin.ext h252
    subst k
    rw [keyMomentRowsAt252]
    exact keyMoment252 B hB
  · have he : k = (253 : Fin 2886) := Fin.ext h253
    subst k
    rw [keyMomentRowsAt253]
    exact keyMoment253 B hB
  · have he : k = (254 : Fin 2886) := Fin.ext h254
    subst k
    rw [keyMomentRowsAt254]
    exact keyMoment254 B hB
  · have he : k = (255 : Fin 2886) := Fin.ext h255
    subst k
    rw [keyMomentRowsAt255]
    exact keyMoment255 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound7_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound7_e_oai
