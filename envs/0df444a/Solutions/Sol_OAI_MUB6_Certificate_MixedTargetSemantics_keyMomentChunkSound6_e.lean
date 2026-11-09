-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound6_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:58:42.746673+00:00
-- url     : https://prove2.me/submissions/dbe6f8f4-43be-4790-9f71-d17fb27b22fe

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

theorem canonical39642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39642 raw39642Labels = mixedMoment B node422 node422Labels := by
  calc
    mixedMoment B raw39642 raw39642Labels = mixedMoment B raw39642step0 raw39642step0Labels := by
      have hz : ∀ j, raw39642 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39642step0 = (fun i j => raw39642 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39642step0 raw39642; decide +kernel
      have hl : raw39642step0Labels = raw39642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39642 raw39642Labels permutation520 hz
    mixedMoment B raw39642step0 raw39642step0Labels = mixedMoment B raw39642step1 raw39642step1Labels := by
      have hz : ∀ j, raw39642step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39642step1 = (fun i j => raw39642step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39642step1 raw39642step0; decide +kernel
      have hl : raw39642step1Labels = raw39642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39642step0 raw39642step0Labels permutation104 hz
    mixedMoment B raw39642step1 raw39642step1Labels = mixedMoment B raw39642step2 raw39642step2Labels := by
      have hz : ∀ j, raw39642step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39642step2 = (fun i j => raw39642step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39642step2 raw39642step1; decide +kernel
      have hl : raw39642step2Labels = raw39642step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39642step1 raw39642step1Labels permutation20 hz
    mixedMoment B raw39642step2 raw39642step2Labels = mixedMoment B raw39642step3 raw39642step3Labels := by
      have hz : ∀ j, raw39642step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw39642step3 = (fun i j => raw39642step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw39642step3 raw39642step2; decide +kernel
      have hl : raw39642step3Labels = raw39642step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39642step2 raw39642step2Labels permutation4 hz
    mixedMoment B raw39642step3 raw39642step3Labels = mixedMoment B raw39642step4 raw39642step4Labels := by
      have ha : raw39642step4 = (fun i j => raw39642step3 (permutation1 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39642step4 raw39642step3; decide +kernel
      have hl : raw39642step4Labels = raw39642step3Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39642step3 raw39642step3Labels permutation1 permutation5
    _ = mixedMoment B node422 node422Labels := by rfl

theorem canonical39643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39643 raw39643Labels = mixedMoment B node418 node418Labels := by
  calc
    mixedMoment B raw39643 raw39643Labels = mixedMoment B raw39643step0 raw39643step0Labels := by
      have hz : ∀ j, raw39643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39643step0 = (fun i j => raw39643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39643step0 raw39643; decide +kernel
      have hl : raw39643step0Labels = raw39643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39643 raw39643Labels permutation434 hz
    mixedMoment B raw39643step0 raw39643step0Labels = mixedMoment B raw39643step1 raw39643step1Labels := by
      have hz : ∀ j, raw39643step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39643step1 = (fun i j => raw39643step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39643step1 raw39643step0; decide +kernel
      have hl : raw39643step1Labels = raw39643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39643step0 raw39643step0Labels permutation80 hz
    mixedMoment B raw39643step1 raw39643step1Labels = mixedMoment B raw39643step2 raw39643step2Labels := by
      have hz : ∀ j, raw39643step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39643step2 = (fun i j => raw39643step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39643step2 raw39643step1; decide +kernel
      have hl : raw39643step2Labels = raw39643step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39643step1 raw39643step1Labels permutation14 hz
    mixedMoment B raw39643step2 raw39643step2Labels = mixedMoment B raw39643step3 raw39643step3Labels := by
      have ha : raw39643step3 = (fun i j => raw39643step2 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39643step3 raw39643step2; decide +kernel
      have hl : raw39643step3Labels = raw39643step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39643step2 raw39643step2Labels permutation2 permutation5
    mixedMoment B raw39643step3 raw39643step3Labels = mixedMoment B raw39643step4 raw39643step4Labels := by
      have ha : raw39643step4 = -raw39643step3 := by apply Matrix.ext; change ∀ i j, raw39643step4 i j = -(raw39643step3 i j); unfold raw39643step4 raw39643step3; decide +kernel
      have hl : raw39643step4Labels = raw39643step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node418 node418Labels := by rfl

theorem canonical39644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39644 raw39644Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw39644 raw39644Labels = mixedMoment B raw39644step0 raw39644step0Labels := by
      have hz : ∀ j, raw39644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39644step0 = (fun i j => raw39644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39644step0 raw39644; decide +kernel
      have hl : raw39644step0Labels = raw39644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39644 raw39644Labels permutation434 hz
    mixedMoment B raw39644step0 raw39644step0Labels = mixedMoment B raw39644step1 raw39644step1Labels := by
      have hz : ∀ j, raw39644step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39644step1 = (fun i j => raw39644step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39644step1 raw39644step0; decide +kernel
      have hl : raw39644step1Labels = raw39644step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39644step0 raw39644step0Labels permutation80 hz
    mixedMoment B raw39644step1 raw39644step1Labels = mixedMoment B raw39644step2 raw39644step2Labels := by
      have hz : ∀ j, raw39644step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39644step2 = (fun i j => raw39644step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39644step2 raw39644step1; decide +kernel
      have hl : raw39644step2Labels = raw39644step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39644step1 raw39644step1Labels permutation14 hz
    mixedMoment B raw39644step2 raw39644step2Labels = mixedMoment B raw39644step3 raw39644step3Labels := by
      have ha : raw39644step3 = (fun i j => raw39644step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39644step3 raw39644step2; decide +kernel
      have hl : raw39644step3Labels = raw39644step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39644step2 raw39644step2Labels permutation3 permutation5
    mixedMoment B raw39644step3 raw39644step3Labels = mixedMoment B raw39644step4 raw39644step4Labels := by
      have ha : raw39644step4 = -raw39644step3 := by apply Matrix.ext; change ∀ i j, raw39644step4 i j = -(raw39644step3 i j); unfold raw39644step4 raw39644step3; decide +kernel
      have hl : raw39644step4Labels = raw39644step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node420 node420Labels := by rfl

theorem canonical39645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39645 raw39645Labels = mixedMoment B node270 node270Labels := by
  calc
    mixedMoment B raw39645 raw39645Labels = mixedMoment B raw39645step0 raw39645step0Labels := by
      have hz : ∀ j, raw39645 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39645step0 = (fun i j => raw39645 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39645step0 raw39645; decide +kernel
      have hl : raw39645step0Labels = raw39645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39645 raw39645Labels permutation434 hz
    mixedMoment B raw39645step0 raw39645step0Labels = mixedMoment B raw39645step1 raw39645step1Labels := by
      have hz : ∀ j, raw39645step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39645step1 = (fun i j => raw39645step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39645step1 raw39645step0; decide +kernel
      have hl : raw39645step1Labels = raw39645step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39645step0 raw39645step0Labels permutation80 hz
    mixedMoment B raw39645step1 raw39645step1Labels = mixedMoment B raw39645step2 raw39645step2Labels := by
      have hz : ∀ j, raw39645step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39645step2 = (fun i j => raw39645step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39645step2 raw39645step1; decide +kernel
      have hl : raw39645step2Labels = raw39645step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39645step1 raw39645step1Labels permutation14 hz
    mixedMoment B raw39645step2 raw39645step2Labels = mixedMoment B raw39645step3 raw39645step3Labels := by
      have ha : raw39645step3 = (fun i j => raw39645step2 (permutation5 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39645step3 raw39645step2; decide +kernel
      have hl : raw39645step3Labels = raw39645step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39645step2 raw39645step2Labels permutation5 permutation4
    _ = mixedMoment B node270 node270Labels := by rfl

theorem canonical39646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39646 raw39646Labels = mixedMoment B node419 node419Labels := by
  calc
    mixedMoment B raw39646 raw39646Labels = mixedMoment B raw39646step0 raw39646step0Labels := by
      have hz : ∀ j, raw39646 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39646step0 = (fun i j => raw39646 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39646step0 raw39646; decide +kernel
      have hl : raw39646step0Labels = raw39646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39646 raw39646Labels permutation434 hz
    mixedMoment B raw39646step0 raw39646step0Labels = mixedMoment B raw39646step1 raw39646step1Labels := by
      have hz : ∀ j, raw39646step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39646step1 = (fun i j => raw39646step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39646step1 raw39646step0; decide +kernel
      have hl : raw39646step1Labels = raw39646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39646step0 raw39646step0Labels permutation80 hz
    mixedMoment B raw39646step1 raw39646step1Labels = mixedMoment B raw39646step2 raw39646step2Labels := by
      have hz : ∀ j, raw39646step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39646step2 = (fun i j => raw39646step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39646step2 raw39646step1; decide +kernel
      have hl : raw39646step2Labels = raw39646step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39646step1 raw39646step1Labels permutation14 hz
    mixedMoment B raw39646step2 raw39646step2Labels = mixedMoment B raw39646step3 raw39646step3Labels := by
      have ha : raw39646step3 = (fun i j => raw39646step2 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39646step3 raw39646step2; decide +kernel
      have hl : raw39646step3Labels = raw39646step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39646step2 raw39646step2Labels permutation2 permutation5
    mixedMoment B raw39646step3 raw39646step3Labels = mixedMoment B raw39646step4 raw39646step4Labels := by
      have ha : raw39646step4 = -raw39646step3 := by apply Matrix.ext; change ∀ i j, raw39646step4 i j = -(raw39646step3 i j); unfold raw39646step4 raw39646step3; decide +kernel
      have hl : raw39646step4Labels = raw39646step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node419 node419Labels := by rfl

theorem canonical39647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39647 raw39647Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw39647 raw39647Labels = mixedMoment B raw39647step0 raw39647step0Labels := by
      have hz : ∀ j, raw39647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39647step0 = (fun i j => raw39647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39647step0 raw39647; decide +kernel
      have hl : raw39647step0Labels = raw39647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39647 raw39647Labels permutation346 hz
    mixedMoment B raw39647step0 raw39647step0Labels = mixedMoment B raw39647step1 raw39647step1Labels := by
      have hz : ∀ j, raw39647step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39647step1 = (fun i j => raw39647step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39647step1 raw39647step0; decide +kernel
      have hl : raw39647step1Labels = raw39647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39647step0 raw39647step0Labels permutation56 hz
    mixedMoment B raw39647step1 raw39647step1Labels = mixedMoment B raw39647step2 raw39647step2Labels := by
      have ha : raw39647step2 = (fun i j => raw39647step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39647step2 raw39647step1; decide +kernel
      have hl : raw39647step2Labels = raw39647step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39647step1 raw39647step1Labels permutation12 permutation5
    mixedMoment B raw39647step2 raw39647step2Labels = mixedMoment B raw39647step3 raw39647step3Labels := by
      have ha : raw39647step3 = -raw39647step2 := by apply Matrix.ext; change ∀ i j, raw39647step3 i j = -(raw39647step2 i j); unfold raw39647step3 raw39647step2; decide +kernel
      have hl : raw39647step3Labels = raw39647step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node412 node412Labels := by rfl

theorem canonical39648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39648 raw39648Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw39648 raw39648Labels = mixedMoment B raw39648step0 raw39648step0Labels := by
      have hz : ∀ j, raw39648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39648step0 = (fun i j => raw39648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39648step0 raw39648; decide +kernel
      have hl : raw39648step0Labels = raw39648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39648 raw39648Labels permutation346 hz
    mixedMoment B raw39648step0 raw39648step0Labels = mixedMoment B raw39648step1 raw39648step1Labels := by
      have hz : ∀ j, raw39648step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39648step1 = (fun i j => raw39648step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39648step1 raw39648step0; decide +kernel
      have hl : raw39648step1Labels = raw39648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39648step0 raw39648step0Labels permutation56 hz
    mixedMoment B raw39648step1 raw39648step1Labels = mixedMoment B raw39648step2 raw39648step2Labels := by
      have ha : raw39648step2 = (fun i j => raw39648step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39648step2 raw39648step1; decide +kernel
      have hl : raw39648step2Labels = raw39648step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39648step1 raw39648step1Labels permutation10 permutation5
    mixedMoment B raw39648step2 raw39648step2Labels = mixedMoment B raw39648step3 raw39648step3Labels := by
      have ha : raw39648step3 = -raw39648step2 := by apply Matrix.ext; change ∀ i j, raw39648step3 i j = -(raw39648step2 i j); unfold raw39648step3 raw39648step2; decide +kernel
      have hl : raw39648step3Labels = raw39648step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node404 node404Labels := by rfl

theorem canonical39649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39649 raw39649Labels = mixedMoment B node417 node417Labels := by
  calc
    mixedMoment B raw39649 raw39649Labels = mixedMoment B raw39649step0 raw39649step0Labels := by
      have hz : ∀ j, raw39649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39649step0 = (fun i j => raw39649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39649step0 raw39649; decide +kernel
      have hl : raw39649step0Labels = raw39649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39649 raw39649Labels permutation346 hz
    mixedMoment B raw39649step0 raw39649step0Labels = mixedMoment B raw39649step1 raw39649step1Labels := by
      have hz : ∀ j, raw39649step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39649step1 = (fun i j => raw39649step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39649step1 raw39649step0; decide +kernel
      have hl : raw39649step1Labels = raw39649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39649step0 raw39649step0Labels permutation56 hz
    mixedMoment B raw39649step1 raw39649step1Labels = mixedMoment B raw39649step2 raw39649step2Labels := by
      have ha : raw39649step2 = (fun i j => raw39649step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39649step2 raw39649step1; decide +kernel
      have hl : raw39649step2Labels = raw39649step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39649step1 raw39649step1Labels permutation8 permutation5
    mixedMoment B raw39649step2 raw39649step2Labels = mixedMoment B raw39649step3 raw39649step3Labels := by
      have ha : raw39649step3 = -raw39649step2 := by apply Matrix.ext; change ∀ i j, raw39649step3 i j = -(raw39649step2 i j); unfold raw39649step3 raw39649step2; decide +kernel
      have hl : raw39649step3Labels = raw39649step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node417 node417Labels := by rfl

theorem canonical39650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39650 raw39650Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw39650 raw39650Labels = mixedMoment B raw39650step0 raw39650step0Labels := by
      have hz : ∀ j, raw39650 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39650step0 = (fun i j => raw39650 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39650step0 raw39650; decide +kernel
      have hl : raw39650step0Labels = raw39650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39650 raw39650Labels permutation346 hz
    mixedMoment B raw39650step0 raw39650step0Labels = mixedMoment B raw39650step1 raw39650step1Labels := by
      have hz : ∀ j, raw39650step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39650step1 = (fun i j => raw39650step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39650step1 raw39650step0; decide +kernel
      have hl : raw39650step1Labels = raw39650step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39650step0 raw39650step0Labels permutation56 hz
    mixedMoment B raw39650step1 raw39650step1Labels = mixedMoment B raw39650step2 raw39650step2Labels := by
      have ha : raw39650step2 = (fun i j => raw39650step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39650step2 raw39650step1; decide +kernel
      have hl : raw39650step2Labels = raw39650step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39650step1 raw39650step1Labels permutation11 permutation5
    mixedMoment B raw39650step2 raw39650step2Labels = mixedMoment B raw39650step3 raw39650step3Labels := by
      have ha : raw39650step3 = -raw39650step2 := by apply Matrix.ext; change ∀ i j, raw39650step3 i j = -(raw39650step2 i j); unfold raw39650step3 raw39650step2; decide +kernel
      have hl : raw39650step3Labels = raw39650step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node405 node405Labels := by rfl

theorem canonical39651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39651 raw39651Labels = mixedMoment B node397 node397Labels := by
  calc
    mixedMoment B raw39651 raw39651Labels = mixedMoment B raw39651step0 raw39651step0Labels := by
      have hz : ∀ j, raw39651 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39651step0 = (fun i j => raw39651 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39651step0 raw39651; decide +kernel
      have hl : raw39651step0Labels = raw39651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39651 raw39651Labels permutation265 hz
    mixedMoment B raw39651step0 raw39651step0Labels = mixedMoment B raw39651step1 raw39651step1Labels := by
      have ha : raw39651step1 = (fun i j => raw39651step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39651step1 raw39651step0; decide +kernel
      have hl : raw39651step1Labels = raw39651step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39651step0 raw39651step0Labels permutation48 permutation5
    mixedMoment B raw39651step1 raw39651step1Labels = mixedMoment B raw39651step2 raw39651step2Labels := by
      have ha : raw39651step2 = -raw39651step1 := by apply Matrix.ext; change ∀ i j, raw39651step2 i j = -(raw39651step1 i j); unfold raw39651step2 raw39651step1; decide +kernel
      have hl : raw39651step2Labels = raw39651step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node397 node397Labels := by rfl

theorem canonical39652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39652 raw39652Labels = mixedMoment B node396 node396Labels := by
  calc
    mixedMoment B raw39652 raw39652Labels = mixedMoment B raw39652step0 raw39652step0Labels := by
      have ha : raw39652step0 = (fun i j => raw39652 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39652step0 raw39652; decide +kernel
      have hl : raw39652step0Labels = raw39652Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39652 raw39652Labels permutation240 permutation5
    mixedMoment B raw39652step0 raw39652step0Labels = mixedMoment B raw39652step1 raw39652step1Labels := by
      have ha : raw39652step1 = -raw39652step0 := by apply Matrix.ext; change ∀ i j, raw39652step1 i j = -(raw39652step0 i j); unfold raw39652step1 raw39652step0; decide +kernel
      have hl : raw39652step1Labels = raw39652step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node396 node396Labels := by rfl

theorem canonical39653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39653 raw39653Labels = mixedMoment B node1 node1Labels := by
  calc
    mixedMoment B raw39653 raw39653Labels = mixedMoment B raw39653step0 raw39653step0Labels := by
      have hz : ∀ j, raw39653 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39653step0 = (fun i j => raw39653 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39653step0 raw39653; decide +kernel
      have hl : raw39653step0Labels = raw39653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39653 raw39653Labels permutation520 hz
    mixedMoment B raw39653step0 raw39653step0Labels = mixedMoment B raw39653step1 raw39653step1Labels := by
      have hz : ∀ j, raw39653step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39653step1 = (fun i j => raw39653step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39653step1 raw39653step0; decide +kernel
      have hl : raw39653step1Labels = raw39653step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39653step0 raw39653step0Labels permutation104 hz
    mixedMoment B raw39653step1 raw39653step1Labels = mixedMoment B raw39653step2 raw39653step2Labels := by
      have hz : ∀ j, raw39653step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39653step2 = (fun i j => raw39653step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39653step2 raw39653step1; decide +kernel
      have hl : raw39653step2Labels = raw39653step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39653step1 raw39653step1Labels permutation20 hz
    mixedMoment B raw39653step2 raw39653step2Labels = mixedMoment B raw39653step3 raw39653step3Labels := by
      have hz : ∀ i, raw39653step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw39653step3 = (fun i j => raw39653step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw39653step3 raw39653step2; decide +kernel
      have hl : raw39653step3Labels = (fun j => raw39653step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw39653step2 raw39653step2Labels permutation6 hz
    mixedMoment B raw39653step3 raw39653step3Labels = mixedMoment B raw39653step4 raw39653step4Labels := by
      have ha : raw39653step4 = (fun i j => raw39653step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw39653step4 raw39653step3; decide +kernel
      have hl : raw39653step4Labels = raw39653step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39653step3 raw39653step3Labels permutation7 permutation0
    mixedMoment B raw39653step4 raw39653step4Labels = mixedMoment B raw39653step5 raw39653step5Labels := by
      have ha : raw39653step5 = -raw39653step4 := by apply Matrix.ext; change ∀ i j, raw39653step5 i j = -(raw39653step4 i j); unfold raw39653step5 raw39653step4; decide +kernel
      have hl : raw39653step5Labels = raw39653step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1 node1Labels := by rfl

theorem canonical39654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39654 raw39654Labels = mixedMoment B node4 node4Labels := by
  calc
    mixedMoment B raw39654 raw39654Labels = mixedMoment B raw39654step0 raw39654step0Labels := by
      have hz : ∀ j, raw39654 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39654step0 = (fun i j => raw39654 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39654step0 raw39654; decide +kernel
      have hl : raw39654step0Labels = raw39654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39654 raw39654Labels permutation434 hz
    mixedMoment B raw39654step0 raw39654step0Labels = mixedMoment B raw39654step1 raw39654step1Labels := by
      have hz : ∀ j, raw39654step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39654step1 = (fun i j => raw39654step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39654step1 raw39654step0; decide +kernel
      have hl : raw39654step1Labels = raw39654step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39654step0 raw39654step0Labels permutation80 hz
    mixedMoment B raw39654step1 raw39654step1Labels = mixedMoment B raw39654step2 raw39654step2Labels := by
      have hz : ∀ i, raw39654step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw39654step2 = (fun i j => raw39654step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw39654step2 raw39654step1; decide +kernel
      have hl : raw39654step2Labels = (fun j => raw39654step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw39654step1 raw39654step1Labels permutation6 hz
    _ = mixedMoment B node4 node4Labels := by rfl

theorem canonical39655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39655 raw39655Labels = mixedMoment B node469 node469Labels := by
  calc
    mixedMoment B raw39655 raw39655Labels = mixedMoment B raw39655step0 raw39655step0Labels := by
      have hz : ∀ j, raw39655 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39655step0 = (fun i j => raw39655 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39655step0 raw39655; decide +kernel
      have hl : raw39655step0Labels = raw39655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39655 raw39655Labels permutation434 hz
    mixedMoment B raw39655step0 raw39655step0Labels = mixedMoment B raw39655step1 raw39655step1Labels := by
      have hz : ∀ j, raw39655step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39655step1 = (fun i j => raw39655step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39655step1 raw39655step0; decide +kernel
      have hl : raw39655step1Labels = raw39655step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39655step0 raw39655step0Labels permutation80 hz
    mixedMoment B raw39655step1 raw39655step1Labels = mixedMoment B raw39655step2 raw39655step2Labels := by
      have ha : raw39655step2 = (fun i j => raw39655step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39655step2 raw39655step1; decide +kernel
      have hl : raw39655step2Labels = raw39655step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39655step1 raw39655step1Labels permutation8 permutation3
    _ = mixedMoment B node469 node469Labels := by rfl

theorem canonical39656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39656 raw39656Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw39656 raw39656Labels = mixedMoment B raw39656step0 raw39656step0Labels := by
      have hz : ∀ j, raw39656 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39656step0 = (fun i j => raw39656 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39656step0 raw39656; decide +kernel
      have hl : raw39656step0Labels = raw39656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39656 raw39656Labels permutation434 hz
    mixedMoment B raw39656step0 raw39656step0Labels = mixedMoment B raw39656step1 raw39656step1Labels := by
      have hz : ∀ j, raw39656step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39656step1 = (fun i j => raw39656step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39656step1 raw39656step0; decide +kernel
      have hl : raw39656step1Labels = raw39656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39656step0 raw39656step0Labels permutation80 hz
    mixedMoment B raw39656step1 raw39656step1Labels = mixedMoment B raw39656step2 raw39656step2Labels := by
      have ha : raw39656step2 = (fun i j => raw39656step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39656step2 raw39656step1; decide +kernel
      have hl : raw39656step2Labels = raw39656step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39656step1 raw39656step1Labels permutation25 permutation4
    _ = mixedMoment B node412 node412Labels := by rfl

theorem canonical39657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39657 raw39657Labels = mixedMoment B node465 node465Labels := by
  calc
    mixedMoment B raw39657 raw39657Labels = mixedMoment B raw39657step0 raw39657step0Labels := by
      have hz : ∀ j, raw39657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39657step0 = (fun i j => raw39657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39657step0 raw39657; decide +kernel
      have hl : raw39657step0Labels = raw39657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39657 raw39657Labels permutation346 hz
    mixedMoment B raw39657step0 raw39657step0Labels = mixedMoment B raw39657step1 raw39657step1Labels := by
      have ha : raw39657step1 = (fun i j => raw39657step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39657step1 raw39657step0; decide +kernel
      have hl : raw39657step1Labels = raw39657step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39657step0 raw39657step0Labels permutation32 permutation3
    _ = mixedMoment B node465 node465Labels := by rfl

theorem canonical39658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39658 raw39658Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw39658 raw39658Labels = mixedMoment B raw39658step0 raw39658step0Labels := by
      have hz : ∀ j, raw39658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39658step0 = (fun i j => raw39658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39658step0 raw39658; decide +kernel
      have hl : raw39658step0Labels = raw39658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39658 raw39658Labels permutation346 hz
    mixedMoment B raw39658step0 raw39658step0Labels = mixedMoment B raw39658step1 raw39658step1Labels := by
      have ha : raw39658step1 = (fun i j => raw39658step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39658step1 raw39658step0; decide +kernel
      have hl : raw39658step1Labels = raw39658step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39658step0 raw39658step0Labels permutation32 permutation3
    _ = mixedMoment B node467 node467Labels := by rfl

theorem canonical39659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39659 raw39659Labels = mixedMoment B node468 node468Labels := by
  calc
    mixedMoment B raw39659 raw39659Labels = mixedMoment B raw39659step0 raw39659step0Labels := by
      have hz : ∀ j, raw39659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39659step0 = (fun i j => raw39659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39659step0 raw39659; decide +kernel
      have hl : raw39659step0Labels = raw39659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39659 raw39659Labels permutation346 hz
    mixedMoment B raw39659step0 raw39659step0Labels = mixedMoment B raw39659step1 raw39659step1Labels := by
      have ha : raw39659step1 = (fun i j => raw39659step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39659step1 raw39659step0; decide +kernel
      have hl : raw39659step1Labels = raw39659step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39659step0 raw39659step0Labels permutation32 permutation3
    _ = mixedMoment B node468 node468Labels := by rfl

theorem canonical39660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39660 raw39660Labels = mixedMoment B node466 node466Labels := by
  calc
    mixedMoment B raw39660 raw39660Labels = mixedMoment B raw39660step0 raw39660step0Labels := by
      have hz : ∀ j, raw39660 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39660step0 = (fun i j => raw39660 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39660step0 raw39660; decide +kernel
      have hl : raw39660step0Labels = raw39660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39660 raw39660Labels permutation346 hz
    mixedMoment B raw39660step0 raw39660step0Labels = mixedMoment B raw39660step1 raw39660step1Labels := by
      have ha : raw39660step1 = (fun i j => raw39660step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39660step1 raw39660step0; decide +kernel
      have hl : raw39660step1Labels = raw39660step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39660step0 raw39660step0Labels permutation32 permutation5
    mixedMoment B raw39660step1 raw39660step1Labels = mixedMoment B raw39660step2 raw39660step2Labels := by
      have ha : raw39660step2 = -raw39660step1 := by apply Matrix.ext; change ∀ i j, raw39660step2 i j = -(raw39660step1 i j); unfold raw39660step2 raw39660step1; decide +kernel
      have hl : raw39660step2Labels = raw39660step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node466 node466Labels := by rfl

theorem canonical39661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39661 raw39661Labels = mixedMoment B node3 node3Labels := by
  calc
    mixedMoment B raw39661 raw39661Labels = mixedMoment B raw39661step0 raw39661step0Labels := by
      have hz : ∀ j, raw39661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39661step0 = (fun i j => raw39661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39661step0 raw39661; decide +kernel
      have hl : raw39661step0Labels = raw39661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39661 raw39661Labels permutation346 hz
    mixedMoment B raw39661step0 raw39661step0Labels = mixedMoment B raw39661step1 raw39661step1Labels := by
      have hz : ∀ i, raw39661step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw39661step1 = (fun i j => raw39661step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw39661step1 raw39661step0; decide +kernel
      have hl : raw39661step1Labels = (fun j => raw39661step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw39661step0 raw39661step0Labels permutation6 hz
    _ = mixedMoment B node3 node3Labels := by rfl

theorem canonical39662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39662 raw39662Labels = mixedMoment B node461 node461Labels := by
  calc
    mixedMoment B raw39662 raw39662Labels = mixedMoment B raw39662step0 raw39662step0Labels := by
      have ha : raw39662step0 = (fun i j => raw39662 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39662step0 raw39662; decide +kernel
      have hl : raw39662step0Labels = raw39662Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39662 raw39662Labels permutation160 permutation5
    mixedMoment B raw39662step0 raw39662step0Labels = mixedMoment B raw39662step1 raw39662step1Labels := by
      have ha : raw39662step1 = -raw39662step0 := by apply Matrix.ext; change ∀ i j, raw39662step1 i j = -(raw39662step0 i j); unfold raw39662step1 raw39662step0; decide +kernel
      have hl : raw39662step1Labels = raw39662step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node461 node461Labels := by rfl

theorem canonical39663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39663 raw39663Labels = mixedMoment B node464 node464Labels := by
  calc
    mixedMoment B raw39663 raw39663Labels = mixedMoment B raw39663step0 raw39663step0Labels := by
      have ha : raw39663step0 = (fun i j => raw39663 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39663step0 raw39663; decide +kernel
      have hl : raw39663step0Labels = raw39663Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39663 raw39663Labels permutation152 permutation3
    _ = mixedMoment B node464 node464Labels := by rfl

theorem canonical39664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39664 raw39664Labels = mixedMoment B node266 node266Labels := by
  calc
    mixedMoment B raw39664 raw39664Labels = mixedMoment B raw39664step0 raw39664step0Labels := by
      have hz : ∀ j, raw39664 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39664step0 = (fun i j => raw39664 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39664step0 raw39664; decide +kernel
      have hl : raw39664step0Labels = raw39664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39664 raw39664Labels permutation520 hz
    mixedMoment B raw39664step0 raw39664step0Labels = mixedMoment B raw39664step1 raw39664step1Labels := by
      have hz : ∀ j, raw39664step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39664step1 = (fun i j => raw39664step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39664step1 raw39664step0; decide +kernel
      have hl : raw39664step1Labels = raw39664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39664step0 raw39664step0Labels permutation104 hz
    mixedMoment B raw39664step1 raw39664step1Labels = mixedMoment B raw39664step2 raw39664step2Labels := by
      have ha : raw39664step2 = (fun i j => raw39664step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39664step2 raw39664step1; decide +kernel
      have hl : raw39664step2Labels = raw39664step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39664step1 raw39664step1Labels permutation31 permutation3
    mixedMoment B raw39664step2 raw39664step2Labels = mixedMoment B raw39664step3 raw39664step3Labels := by
      have ha : raw39664step3 = -raw39664step2 := by apply Matrix.ext; change ∀ i j, raw39664step3 i j = -(raw39664step2 i j); unfold raw39664step3 raw39664step2; decide +kernel
      have hl : raw39664step3Labels = raw39664step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node266 node266Labels := by rfl

theorem canonical39665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39665 raw39665Labels = mixedMoment B node465 node465Labels := by
  calc
    mixedMoment B raw39665 raw39665Labels = mixedMoment B raw39665step0 raw39665step0Labels := by
      have hz : ∀ j, raw39665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39665step0 = (fun i j => raw39665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39665step0 raw39665; decide +kernel
      have hl : raw39665step0Labels = raw39665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39665 raw39665Labels permutation434 hz
    mixedMoment B raw39665step0 raw39665step0Labels = mixedMoment B raw39665step1 raw39665step1Labels := by
      have ha : raw39665step1 = (fun i j => raw39665step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39665step1 raw39665step0; decide +kernel
      have hl : raw39665step1Labels = raw39665step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39665step0 raw39665step0Labels permutation151 permutation3
    mixedMoment B raw39665step1 raw39665step1Labels = mixedMoment B raw39665step2 raw39665step2Labels := by
      have ha : raw39665step2 = -raw39665step1 := by apply Matrix.ext; change ∀ i j, raw39665step2 i j = -(raw39665step1 i j); unfold raw39665step2 raw39665step1; decide +kernel
      have hl : raw39665step2Labels = raw39665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node465 node465Labels := by rfl

theorem canonical39666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39666 raw39666Labels = mixedMoment B node483 node483Labels := by
  calc
    mixedMoment B raw39666 raw39666Labels = mixedMoment B raw39666step0 raw39666step0Labels := by
      have hz : ∀ j, raw39666 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39666step0 = (fun i j => raw39666 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39666step0 raw39666; decide +kernel
      have hl : raw39666step0Labels = raw39666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39666 raw39666Labels permutation434 hz
    mixedMoment B raw39666step0 raw39666step0Labels = mixedMoment B raw39666step1 raw39666step1Labels := by
      have ha : raw39666step1 = (fun i j => raw39666step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39666step1 raw39666step0; decide +kernel
      have hl : raw39666step1Labels = raw39666step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39666step0 raw39666step0Labels permutation32 permutation3
    _ = mixedMoment B node483 node483Labels := by rfl

theorem canonical39667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39667 raw39667Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39667 raw39667Labels = mixedMoment B raw39667step0 raw39667step0Labels := by
      have hz : ∀ j, raw39667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39667step0 = (fun i j => raw39667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39667step0 raw39667; decide +kernel
      have hl : raw39667step0Labels = raw39667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39667 raw39667Labels permutation434 hz
    mixedMoment B raw39667step0 raw39667step0Labels = mixedMoment B raw39667step1 raw39667step1Labels := by
      have ha : raw39667step1 = (fun i j => raw39667step0 (permutation115 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39667step1 raw39667step0; decide +kernel
      have hl : raw39667step1Labels = raw39667step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39667step0 raw39667step0Labels permutation115 permutation4
    _ = mixedMoment B node384 node384Labels := by rfl

theorem canonical39668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39668 raw39668Labels = mixedMoment B node478 node478Labels := by
  calc
    mixedMoment B raw39668 raw39668Labels = mixedMoment B raw39668step0 raw39668step0Labels := by
      have ha : raw39668step0 = (fun i j => raw39668 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39668step0 raw39668; decide +kernel
      have hl : raw39668step0Labels = raw39668Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39668 raw39668Labels permutation152 permutation3
    _ = mixedMoment B node478 node478Labels := by rfl

theorem canonical39669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39669 raw39669Labels = mixedMoment B node480 node480Labels := by
  calc
    mixedMoment B raw39669 raw39669Labels = mixedMoment B raw39669step0 raw39669step0Labels := by
      have ha : raw39669step0 = (fun i j => raw39669 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39669step0 raw39669; decide +kernel
      have hl : raw39669step0Labels = raw39669Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39669 raw39669Labels permutation152 permutation3
    _ = mixedMoment B node480 node480Labels := by rfl

theorem canonical39670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39670 raw39670Labels = mixedMoment B node481 node481Labels := by
  calc
    mixedMoment B raw39670 raw39670Labels = mixedMoment B raw39670step0 raw39670step0Labels := by
      have ha : raw39670step0 = (fun i j => raw39670 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39670step0 raw39670; decide +kernel
      have hl : raw39670step0Labels = raw39670Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39670 raw39670Labels permutation682 permutation2
    mixedMoment B raw39670step0 raw39670step0Labels = mixedMoment B raw39670step1 raw39670step1Labels := by
      have ha : raw39670step1 = -raw39670step0 := by apply Matrix.ext; change ∀ i j, raw39670step1 i j = -(raw39670step0 i j); unfold raw39670step1 raw39670step0; decide +kernel
      have hl : raw39670step1Labels = raw39670step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node481 node481Labels := by rfl

theorem canonical39671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39671 raw39671Labels = mixedMoment B node479 node479Labels := by
  calc
    mixedMoment B raw39671 raw39671Labels = mixedMoment B raw39671step0 raw39671step0Labels := by
      have ha : raw39671step0 = (fun i j => raw39671 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39671step0 raw39671; decide +kernel
      have hl : raw39671step0Labels = raw39671Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39671 raw39671Labels permutation176 permutation5
    mixedMoment B raw39671step0 raw39671step0Labels = mixedMoment B raw39671step1 raw39671step1Labels := by
      have ha : raw39671step1 = -raw39671step0 := by apply Matrix.ext; change ∀ i j, raw39671step1 i j = -(raw39671step0 i j); unfold raw39671step1 raw39671step0; decide +kernel
      have hl : raw39671step1Labels = raw39671step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node479 node479Labels := by rfl

theorem canonical39672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39672 raw39672Labels = mixedMoment B node482 node482Labels := by
  calc
    mixedMoment B raw39672 raw39672Labels = mixedMoment B raw39672step0 raw39672step0Labels := by
      have ha : raw39672step0 = (fun i j => raw39672 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39672step0 raw39672; decide +kernel
      have hl : raw39672step0Labels = raw39672Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39672 raw39672Labels permutation152 permutation3
    _ = mixedMoment B node482 node482Labels := by rfl

theorem canonical39673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39673 raw39673Labels = mixedMoment B node5505 node5505Labels := by
  calc
    mixedMoment B raw39673 raw39673Labels = mixedMoment B raw39673step0 raw39673step0Labels := by
      have hz : ∀ j, raw39673 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39673step0 = (fun i j => raw39673 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39673step0 raw39673; decide +kernel
      have hl : raw39673step0Labels = raw39673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39673 raw39673Labels permutation434 hz
    mixedMoment B raw39673step0 raw39673step0Labels = mixedMoment B raw39673step1 raw39673step1Labels := by
      have hz : ∀ j, raw39673step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39673step1 = (fun i j => raw39673step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39673step1 raw39673step0; decide +kernel
      have hl : raw39673step1Labels = raw39673step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39673step0 raw39673step0Labels permutation80 hz
    mixedMoment B raw39673step1 raw39673step1Labels = mixedMoment B raw39673step2 raw39673step2Labels := by
      have ha : raw39673step2 = (fun i j => raw39673step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39673step2 raw39673step1; decide +kernel
      have hl : raw39673step2Labels = raw39673step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39673step1 raw39673step1Labels permutation8 permutation3
    _ = mixedMoment B node5505 node5505Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 192) =
      Integer.Sparse.eval keyMomentRow192 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 192).leftCharge (GramAssembly.key 192).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 422) := by
    have ha : gramCharges (GramAssembly.key 192).leftCharge (GramAssembly.key 192).rightCharge = raw39642 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39642Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39642 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 192).leftCharge (GramAssembly.key 192).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow192, Integer.Sparse.eval]

theorem keyMoment193 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 193) =
      Integer.Sparse.eval keyMomentRow193 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 193).leftCharge (GramAssembly.key 193).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 418) := by
    have ha : gramCharges (GramAssembly.key 193).leftCharge (GramAssembly.key 193).rightCharge = raw39643 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39643Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39643 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 193).leftCharge (GramAssembly.key 193).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow193, Integer.Sparse.eval]

theorem keyMoment194 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 194) =
      Integer.Sparse.eval keyMomentRow194 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 194).leftCharge (GramAssembly.key 194).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 420) := by
    have ha : gramCharges (GramAssembly.key 194).leftCharge (GramAssembly.key 194).rightCharge = raw39644 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39644Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39644 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 194).leftCharge (GramAssembly.key 194).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow194, Integer.Sparse.eval]

theorem keyMoment195 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 195) =
      Integer.Sparse.eval keyMomentRow195 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 195).leftCharge (GramAssembly.key 195).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 270) := by
    have ha : gramCharges (GramAssembly.key 195).leftCharge (GramAssembly.key 195).rightCharge = raw39645 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39645Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39645 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 195).leftCharge (GramAssembly.key 195).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow195, Integer.Sparse.eval]

theorem keyMoment196 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 196) =
      Integer.Sparse.eval keyMomentRow196 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 196).leftCharge (GramAssembly.key 196).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 419) := by
    have ha : gramCharges (GramAssembly.key 196).leftCharge (GramAssembly.key 196).rightCharge = raw39646 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39646Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39646 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 196).leftCharge (GramAssembly.key 196).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow196, Integer.Sparse.eval]

theorem keyMoment197 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 197) =
      Integer.Sparse.eval keyMomentRow197 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 197).leftCharge (GramAssembly.key 197).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 412) := by
    have ha : gramCharges (GramAssembly.key 197).leftCharge (GramAssembly.key 197).rightCharge = raw39647 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39647Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39647 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 197).leftCharge (GramAssembly.key 197).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow197, Integer.Sparse.eval]

theorem keyMoment198 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 198) =
      Integer.Sparse.eval keyMomentRow198 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 198).leftCharge (GramAssembly.key 198).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 404) := by
    have ha : gramCharges (GramAssembly.key 198).leftCharge (GramAssembly.key 198).rightCharge = raw39648 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39648Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39648 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 198).leftCharge (GramAssembly.key 198).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow198, Integer.Sparse.eval]

theorem keyMoment199 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 199) =
      Integer.Sparse.eval keyMomentRow199 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 199).leftCharge (GramAssembly.key 199).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 417) := by
    have ha : gramCharges (GramAssembly.key 199).leftCharge (GramAssembly.key 199).rightCharge = raw39649 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39649Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39649 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 199).leftCharge (GramAssembly.key 199).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow199, Integer.Sparse.eval]

theorem keyMoment200 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 200) =
      Integer.Sparse.eval keyMomentRow200 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 200).leftCharge (GramAssembly.key 200).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 405) := by
    have ha : gramCharges (GramAssembly.key 200).leftCharge (GramAssembly.key 200).rightCharge = raw39650 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39650Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39650 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 200).leftCharge (GramAssembly.key 200).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow200, Integer.Sparse.eval]

theorem keyMoment201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 201) =
      Integer.Sparse.eval keyMomentRow201 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 201).leftCharge (GramAssembly.key 201).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 397) := by
    have ha : gramCharges (GramAssembly.key 201).leftCharge (GramAssembly.key 201).rightCharge = raw39651 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39651Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39651 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 201).leftCharge (GramAssembly.key 201).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow201, Integer.Sparse.eval]

theorem keyMoment202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 202) =
      Integer.Sparse.eval keyMomentRow202 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 202).leftCharge (GramAssembly.key 202).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 396) := by
    have ha : gramCharges (GramAssembly.key 202).leftCharge (GramAssembly.key 202).rightCharge = raw39652 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39652Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39652 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 202).leftCharge (GramAssembly.key 202).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow202, Integer.Sparse.eval]

theorem keyMoment203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 203) =
      Integer.Sparse.eval keyMomentRow203 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 203).leftCharge (GramAssembly.key 203).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 1) := by
    have ha : gramCharges (GramAssembly.key 203).leftCharge (GramAssembly.key 203).rightCharge = raw39653 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39653Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39653 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 203).leftCharge (GramAssembly.key 203).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow203, Integer.Sparse.eval]

theorem keyMoment204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 204) =
      Integer.Sparse.eval keyMomentRow204 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 204).leftCharge (GramAssembly.key 204).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 4) := by
    have ha : gramCharges (GramAssembly.key 204).leftCharge (GramAssembly.key 204).rightCharge = raw39654 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39654Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39654 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 204).leftCharge (GramAssembly.key 204).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow204, Integer.Sparse.eval]

theorem keyMoment205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 205) =
      Integer.Sparse.eval keyMomentRow205 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 205).leftCharge (GramAssembly.key 205).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 469) := by
    have ha : gramCharges (GramAssembly.key 205).leftCharge (GramAssembly.key 205).rightCharge = raw39655 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39655Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39655 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 205).leftCharge (GramAssembly.key 205).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow205, Integer.Sparse.eval]

theorem keyMoment206 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 206) =
      Integer.Sparse.eval keyMomentRow206 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 206).leftCharge (GramAssembly.key 206).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 412) := by
    have ha : gramCharges (GramAssembly.key 206).leftCharge (GramAssembly.key 206).rightCharge = raw39656 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39656Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39656 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 206).leftCharge (GramAssembly.key 206).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow206, Integer.Sparse.eval]

theorem keyMoment207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 207) =
      Integer.Sparse.eval keyMomentRow207 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 207).leftCharge (GramAssembly.key 207).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 465) := by
    have ha : gramCharges (GramAssembly.key 207).leftCharge (GramAssembly.key 207).rightCharge = raw39657 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39657Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39657 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 207).leftCharge (GramAssembly.key 207).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow207, Integer.Sparse.eval]

theorem keyMoment208 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 208) =
      Integer.Sparse.eval keyMomentRow208 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 208).leftCharge (GramAssembly.key 208).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 467) := by
    have ha : gramCharges (GramAssembly.key 208).leftCharge (GramAssembly.key 208).rightCharge = raw39658 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39658Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39658 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 208).leftCharge (GramAssembly.key 208).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow208, Integer.Sparse.eval]

theorem keyMoment209 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 209) =
      Integer.Sparse.eval keyMomentRow209 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 209).leftCharge (GramAssembly.key 209).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 468) := by
    have ha : gramCharges (GramAssembly.key 209).leftCharge (GramAssembly.key 209).rightCharge = raw39659 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39659Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39659 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 209).leftCharge (GramAssembly.key 209).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow209, Integer.Sparse.eval]

theorem keyMoment210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 210) =
      Integer.Sparse.eval keyMomentRow210 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 210).leftCharge (GramAssembly.key 210).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 466) := by
    have ha : gramCharges (GramAssembly.key 210).leftCharge (GramAssembly.key 210).rightCharge = raw39660 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39660Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39660 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 210).leftCharge (GramAssembly.key 210).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow210, Integer.Sparse.eval]

theorem keyMoment211 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 211) =
      Integer.Sparse.eval keyMomentRow211 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 211).leftCharge (GramAssembly.key 211).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 3) := by
    have ha : gramCharges (GramAssembly.key 211).leftCharge (GramAssembly.key 211).rightCharge = raw39661 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39661Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39661 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 211).leftCharge (GramAssembly.key 211).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow211, Integer.Sparse.eval]

theorem keyMoment212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 212) =
      Integer.Sparse.eval keyMomentRow212 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 212).leftCharge (GramAssembly.key 212).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 461) := by
    have ha : gramCharges (GramAssembly.key 212).leftCharge (GramAssembly.key 212).rightCharge = raw39662 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39662Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39662 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 212).leftCharge (GramAssembly.key 212).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow212, Integer.Sparse.eval]

theorem keyMoment213 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 213) =
      Integer.Sparse.eval keyMomentRow213 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 213).leftCharge (GramAssembly.key 213).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 464) := by
    have ha : gramCharges (GramAssembly.key 213).leftCharge (GramAssembly.key 213).rightCharge = raw39663 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39663Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39663 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 213).leftCharge (GramAssembly.key 213).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow213, Integer.Sparse.eval]

theorem keyMoment214 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 214) =
      Integer.Sparse.eval keyMomentRow214 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 214).leftCharge (GramAssembly.key 214).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 266) := by
    have ha : gramCharges (GramAssembly.key 214).leftCharge (GramAssembly.key 214).rightCharge = raw39664 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39664Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39664 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 214).leftCharge (GramAssembly.key 214).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow214, Integer.Sparse.eval]

theorem keyMoment215 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 215) =
      Integer.Sparse.eval keyMomentRow215 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 215).leftCharge (GramAssembly.key 215).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 465) := by
    have ha : gramCharges (GramAssembly.key 215).leftCharge (GramAssembly.key 215).rightCharge = raw39665 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39665Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39665 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 215).leftCharge (GramAssembly.key 215).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow215, Integer.Sparse.eval]

theorem keyMoment216 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 216) =
      Integer.Sparse.eval keyMomentRow216 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 216).leftCharge (GramAssembly.key 216).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 483) := by
    have ha : gramCharges (GramAssembly.key 216).leftCharge (GramAssembly.key 216).rightCharge = raw39666 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39666Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39666 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 216).leftCharge (GramAssembly.key 216).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow216, Integer.Sparse.eval]

theorem keyMoment217 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 217) =
      Integer.Sparse.eval keyMomentRow217 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 217).leftCharge (GramAssembly.key 217).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 217).leftCharge (GramAssembly.key 217).rightCharge = raw39667 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39667Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39667 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 217).leftCharge (GramAssembly.key 217).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow217, Integer.Sparse.eval]

theorem keyMoment218 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 218) =
      Integer.Sparse.eval keyMomentRow218 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 218).leftCharge (GramAssembly.key 218).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 478) := by
    have ha : gramCharges (GramAssembly.key 218).leftCharge (GramAssembly.key 218).rightCharge = raw39668 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39668Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39668 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 218).leftCharge (GramAssembly.key 218).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow218, Integer.Sparse.eval]

theorem keyMoment219 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 219) =
      Integer.Sparse.eval keyMomentRow219 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 219).leftCharge (GramAssembly.key 219).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 480) := by
    have ha : gramCharges (GramAssembly.key 219).leftCharge (GramAssembly.key 219).rightCharge = raw39669 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39669Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39669 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 219).leftCharge (GramAssembly.key 219).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow219, Integer.Sparse.eval]

theorem keyMoment220 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 220) =
      Integer.Sparse.eval keyMomentRow220 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 220).leftCharge (GramAssembly.key 220).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 481) := by
    have ha : gramCharges (GramAssembly.key 220).leftCharge (GramAssembly.key 220).rightCharge = raw39670 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39670Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39670 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 220).leftCharge (GramAssembly.key 220).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow220, Integer.Sparse.eval]

theorem keyMoment221 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 221) =
      Integer.Sparse.eval keyMomentRow221 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 221).leftCharge (GramAssembly.key 221).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 479) := by
    have ha : gramCharges (GramAssembly.key 221).leftCharge (GramAssembly.key 221).rightCharge = raw39671 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39671Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39671 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 221).leftCharge (GramAssembly.key 221).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow221, Integer.Sparse.eval]

theorem keyMoment222 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 222) =
      Integer.Sparse.eval keyMomentRow222 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 222).leftCharge (GramAssembly.key 222).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 482) := by
    have ha : gramCharges (GramAssembly.key 222).leftCharge (GramAssembly.key 222).rightCharge = raw39672 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39672Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39672 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 222).leftCharge (GramAssembly.key 222).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow222, Integer.Sparse.eval]

theorem keyMoment223 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 223) =
      Integer.Sparse.eval keyMomentRow223 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 223).leftCharge (GramAssembly.key 223).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 3) := by
    have ha : gramCharges (GramAssembly.key 223).leftCharge (GramAssembly.key 223).rightCharge = raw39673 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39673Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39673 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 223).leftCharge (GramAssembly.key 223).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow223, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt192 : keyMomentRows (192 : Fin 2886) =
    keyMomentRow192 := by decide +kernel

theorem keyMomentRowsAt193 : keyMomentRows (193 : Fin 2886) =
    keyMomentRow193 := by decide +kernel

theorem keyMomentRowsAt194 : keyMomentRows (194 : Fin 2886) =
    keyMomentRow194 := by decide +kernel

theorem keyMomentRowsAt195 : keyMomentRows (195 : Fin 2886) =
    keyMomentRow195 := by decide +kernel

theorem keyMomentRowsAt196 : keyMomentRows (196 : Fin 2886) =
    keyMomentRow196 := by decide +kernel

theorem keyMomentRowsAt197 : keyMomentRows (197 : Fin 2886) =
    keyMomentRow197 := by decide +kernel

theorem keyMomentRowsAt198 : keyMomentRows (198 : Fin 2886) =
    keyMomentRow198 := by decide +kernel

theorem keyMomentRowsAt199 : keyMomentRows (199 : Fin 2886) =
    keyMomentRow199 := by decide +kernel

theorem keyMomentRowsAt200 : keyMomentRows (200 : Fin 2886) =
    keyMomentRow200 := by decide +kernel

theorem keyMomentRowsAt201 : keyMomentRows (201 : Fin 2886) =
    keyMomentRow201 := by decide +kernel

theorem keyMomentRowsAt202 : keyMomentRows (202 : Fin 2886) =
    keyMomentRow202 := by decide +kernel

theorem keyMomentRowsAt203 : keyMomentRows (203 : Fin 2886) =
    keyMomentRow203 := by decide +kernel

theorem keyMomentRowsAt204 : keyMomentRows (204 : Fin 2886) =
    keyMomentRow204 := by decide +kernel

theorem keyMomentRowsAt205 : keyMomentRows (205 : Fin 2886) =
    keyMomentRow205 := by decide +kernel

theorem keyMomentRowsAt206 : keyMomentRows (206 : Fin 2886) =
    keyMomentRow206 := by decide +kernel

theorem keyMomentRowsAt207 : keyMomentRows (207 : Fin 2886) =
    keyMomentRow207 := by decide +kernel

theorem keyMomentRowsAt208 : keyMomentRows (208 : Fin 2886) =
    keyMomentRow208 := by decide +kernel

theorem keyMomentRowsAt209 : keyMomentRows (209 : Fin 2886) =
    keyMomentRow209 := by decide +kernel

theorem keyMomentRowsAt210 : keyMomentRows (210 : Fin 2886) =
    keyMomentRow210 := by decide +kernel

theorem keyMomentRowsAt211 : keyMomentRows (211 : Fin 2886) =
    keyMomentRow211 := by decide +kernel

theorem keyMomentRowsAt212 : keyMomentRows (212 : Fin 2886) =
    keyMomentRow212 := by decide +kernel

theorem keyMomentRowsAt213 : keyMomentRows (213 : Fin 2886) =
    keyMomentRow213 := by decide +kernel

theorem keyMomentRowsAt214 : keyMomentRows (214 : Fin 2886) =
    keyMomentRow214 := by decide +kernel

theorem keyMomentRowsAt215 : keyMomentRows (215 : Fin 2886) =
    keyMomentRow215 := by decide +kernel

theorem keyMomentRowsAt216 : keyMomentRows (216 : Fin 2886) =
    keyMomentRow216 := by decide +kernel

theorem keyMomentRowsAt217 : keyMomentRows (217 : Fin 2886) =
    keyMomentRow217 := by decide +kernel

theorem keyMomentRowsAt218 : keyMomentRows (218 : Fin 2886) =
    keyMomentRow218 := by decide +kernel

theorem keyMomentRowsAt219 : keyMomentRows (219 : Fin 2886) =
    keyMomentRow219 := by decide +kernel

theorem keyMomentRowsAt220 : keyMomentRows (220 : Fin 2886) =
    keyMomentRow220 := by decide +kernel

theorem keyMomentRowsAt221 : keyMomentRows (221 : Fin 2886) =
    keyMomentRow221 := by decide +kernel

theorem keyMomentRowsAt222 : keyMomentRows (222 : Fin 2886) =
    keyMomentRow222 := by decide +kernel

theorem keyMomentRowsAt223 : keyMomentRows (223 : Fin 2886) =
    keyMomentRow223 := by decide +kernel

theorem keyMomentChunkSound6_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 6) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 192 ∨ k.val = 193 ∨ k.val = 194 ∨ k.val = 195 ∨ k.val = 196 ∨ k.val = 197 ∨ k.val = 198 ∨ k.val = 199 ∨ k.val = 200 ∨ k.val = 201 ∨ k.val = 202 ∨ k.val = 203 ∨ k.val = 204 ∨ k.val = 205 ∨ k.val = 206 ∨ k.val = 207 ∨ k.val = 208 ∨ k.val = 209 ∨ k.val = 210 ∨ k.val = 211 ∨ k.val = 212 ∨ k.val = 213 ∨ k.val = 214 ∨ k.val = 215 ∨ k.val = 216 ∨ k.val = 217 ∨ k.val = 218 ∨ k.val = 219 ∨ k.val = 220 ∨ k.val = 221 ∨ k.val = 222 ∨ k.val = 223 := by omega
  rcases heq with h192 | h193 | h194 | h195 | h196 | h197 | h198 | h199 | h200 | h201 | h202 | h203 | h204 | h205 | h206 | h207 | h208 | h209 | h210 | h211 | h212 | h213 | h214 | h215 | h216 | h217 | h218 | h219 | h220 | h221 | h222 | h223
  · have he : k = (192 : Fin 2886) := Fin.ext h192
    subst k
    rw [keyMomentRowsAt192]
    exact keyMoment192 B hB
  · have he : k = (193 : Fin 2886) := Fin.ext h193
    subst k
    rw [keyMomentRowsAt193]
    exact keyMoment193 B hB
  · have he : k = (194 : Fin 2886) := Fin.ext h194
    subst k
    rw [keyMomentRowsAt194]
    exact keyMoment194 B hB
  · have he : k = (195 : Fin 2886) := Fin.ext h195
    subst k
    rw [keyMomentRowsAt195]
    exact keyMoment195 B hB
  · have he : k = (196 : Fin 2886) := Fin.ext h196
    subst k
    rw [keyMomentRowsAt196]
    exact keyMoment196 B hB
  · have he : k = (197 : Fin 2886) := Fin.ext h197
    subst k
    rw [keyMomentRowsAt197]
    exact keyMoment197 B hB
  · have he : k = (198 : Fin 2886) := Fin.ext h198
    subst k
    rw [keyMomentRowsAt198]
    exact keyMoment198 B hB
  · have he : k = (199 : Fin 2886) := Fin.ext h199
    subst k
    rw [keyMomentRowsAt199]
    exact keyMoment199 B hB
  · have he : k = (200 : Fin 2886) := Fin.ext h200
    subst k
    rw [keyMomentRowsAt200]
    exact keyMoment200 B hB
  · have he : k = (201 : Fin 2886) := Fin.ext h201
    subst k
    rw [keyMomentRowsAt201]
    exact keyMoment201 B hB
  · have he : k = (202 : Fin 2886) := Fin.ext h202
    subst k
    rw [keyMomentRowsAt202]
    exact keyMoment202 B hB
  · have he : k = (203 : Fin 2886) := Fin.ext h203
    subst k
    rw [keyMomentRowsAt203]
    exact keyMoment203 B hB
  · have he : k = (204 : Fin 2886) := Fin.ext h204
    subst k
    rw [keyMomentRowsAt204]
    exact keyMoment204 B hB
  · have he : k = (205 : Fin 2886) := Fin.ext h205
    subst k
    rw [keyMomentRowsAt205]
    exact keyMoment205 B hB
  · have he : k = (206 : Fin 2886) := Fin.ext h206
    subst k
    rw [keyMomentRowsAt206]
    exact keyMoment206 B hB
  · have he : k = (207 : Fin 2886) := Fin.ext h207
    subst k
    rw [keyMomentRowsAt207]
    exact keyMoment207 B hB
  · have he : k = (208 : Fin 2886) := Fin.ext h208
    subst k
    rw [keyMomentRowsAt208]
    exact keyMoment208 B hB
  · have he : k = (209 : Fin 2886) := Fin.ext h209
    subst k
    rw [keyMomentRowsAt209]
    exact keyMoment209 B hB
  · have he : k = (210 : Fin 2886) := Fin.ext h210
    subst k
    rw [keyMomentRowsAt210]
    exact keyMoment210 B hB
  · have he : k = (211 : Fin 2886) := Fin.ext h211
    subst k
    rw [keyMomentRowsAt211]
    exact keyMoment211 B hB
  · have he : k = (212 : Fin 2886) := Fin.ext h212
    subst k
    rw [keyMomentRowsAt212]
    exact keyMoment212 B hB
  · have he : k = (213 : Fin 2886) := Fin.ext h213
    subst k
    rw [keyMomentRowsAt213]
    exact keyMoment213 B hB
  · have he : k = (214 : Fin 2886) := Fin.ext h214
    subst k
    rw [keyMomentRowsAt214]
    exact keyMoment214 B hB
  · have he : k = (215 : Fin 2886) := Fin.ext h215
    subst k
    rw [keyMomentRowsAt215]
    exact keyMoment215 B hB
  · have he : k = (216 : Fin 2886) := Fin.ext h216
    subst k
    rw [keyMomentRowsAt216]
    exact keyMoment216 B hB
  · have he : k = (217 : Fin 2886) := Fin.ext h217
    subst k
    rw [keyMomentRowsAt217]
    exact keyMoment217 B hB
  · have he : k = (218 : Fin 2886) := Fin.ext h218
    subst k
    rw [keyMomentRowsAt218]
    exact keyMoment218 B hB
  · have he : k = (219 : Fin 2886) := Fin.ext h219
    subst k
    rw [keyMomentRowsAt219]
    exact keyMoment219 B hB
  · have he : k = (220 : Fin 2886) := Fin.ext h220
    subst k
    rw [keyMomentRowsAt220]
    exact keyMoment220 B hB
  · have he : k = (221 : Fin 2886) := Fin.ext h221
    subst k
    rw [keyMomentRowsAt221]
    exact keyMoment221 B hB
  · have he : k = (222 : Fin 2886) := Fin.ext h222
    subst k
    rw [keyMomentRowsAt222]
    exact keyMoment222 B hB
  · have he : k = (223 : Fin 2886) := Fin.ext h223
    subst k
    rw [keyMomentRowsAt223]
    exact keyMoment223 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound6_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound6_e_oai
