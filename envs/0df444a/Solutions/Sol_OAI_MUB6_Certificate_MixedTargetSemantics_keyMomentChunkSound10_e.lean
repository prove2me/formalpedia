-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound10_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:46:14.021428+00:00
-- url     : https://prove2.me/submissions/342553b7-4236-4e27-8c49-f4c0aad70eb4

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

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical297
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical38095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38095 raw38095Labels = mixedMoment B node499 node499Labels := by
  calc
    _ = mixedMoment B node499 node499Labels := by rfl

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

theorem canonical39770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39770 raw39770Labels = mixedMoment B node415 node415Labels := by
  calc
    mixedMoment B raw39770 raw39770Labels = mixedMoment B raw39770step0 raw39770step0Labels := by
      have hz : ∀ j, raw39770 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39770step0 = (fun i j => raw39770 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39770step0 raw39770; decide +kernel
      have hl : raw39770step0Labels = raw39770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39770 raw39770Labels permutation434 hz
    mixedMoment B raw39770step0 raw39770step0Labels = mixedMoment B raw39770step1 raw39770step1Labels := by
      have hz : ∀ j, raw39770step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39770step1 = (fun i j => raw39770step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39770step1 raw39770step0; decide +kernel
      have hl : raw39770step1Labels = raw39770step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39770step0 raw39770step0Labels permutation80 hz
    mixedMoment B raw39770step1 raw39770step1Labels = mixedMoment B raw39770step2 raw39770step2Labels := by
      have hz : ∀ j, raw39770step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39770step2 = (fun i j => raw39770step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39770step2 raw39770step1; decide +kernel
      have hl : raw39770step2Labels = raw39770step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39770step1 raw39770step1Labels permutation14 hz
    mixedMoment B raw39770step2 raw39770step2Labels = mixedMoment B raw39770step3 raw39770step3Labels := by
      have ha : raw39770step3 = (fun i j => raw39770step2 (permutation6 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39770step3 raw39770step2; decide +kernel
      have hl : raw39770step3Labels = raw39770step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39770step2 raw39770step2Labels permutation6 permutation4
    _ = mixedMoment B node415 node415Labels := by rfl

theorem canonical39771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39771 raw39771Labels = mixedMoment B node416 node416Labels := by
  calc
    mixedMoment B raw39771 raw39771Labels = mixedMoment B raw39771step0 raw39771step0Labels := by
      have hz : ∀ j, raw39771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39771step0 = (fun i j => raw39771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39771step0 raw39771; decide +kernel
      have hl : raw39771step0Labels = raw39771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39771 raw39771Labels permutation346 hz
    mixedMoment B raw39771step0 raw39771step0Labels = mixedMoment B raw39771step1 raw39771step1Labels := by
      have hz : ∀ j, raw39771step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39771step1 = (fun i j => raw39771step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39771step1 raw39771step0; decide +kernel
      have hl : raw39771step1Labels = raw39771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39771step0 raw39771step0Labels permutation56 hz
    mixedMoment B raw39771step1 raw39771step1Labels = mixedMoment B raw39771step2 raw39771step2Labels := by
      have ha : raw39771step2 = (fun i j => raw39771step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39771step2 raw39771step1; decide +kernel
      have hl : raw39771step2Labels = raw39771step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39771step1 raw39771step1Labels permutation29 permutation7
    _ = mixedMoment B node416 node416Labels := by rfl

theorem canonical39772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39772 raw39772Labels = mixedMoment B node152 node152Labels := by
  calc
    mixedMoment B raw39772 raw39772Labels = mixedMoment B raw39772step0 raw39772step0Labels := by
      have hz : ∀ j, raw39772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39772step0 = (fun i j => raw39772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39772step0 raw39772; decide +kernel
      have hl : raw39772step0Labels = raw39772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39772 raw39772Labels permutation346 hz
    mixedMoment B raw39772step0 raw39772step0Labels = mixedMoment B raw39772step1 raw39772step1Labels := by
      have hz : ∀ j, raw39772step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39772step1 = (fun i j => raw39772step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39772step1 raw39772step0; decide +kernel
      have hl : raw39772step1Labels = raw39772step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39772step0 raw39772step0Labels permutation56 hz
    mixedMoment B raw39772step1 raw39772step1Labels = mixedMoment B raw39772step2 raw39772step2Labels := by
      have ha : raw39772step2 = (fun i j => raw39772step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39772step2 raw39772step1; decide +kernel
      have hl : raw39772step2Labels = raw39772step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39772step1 raw39772step1Labels permutation26 permutation6
    _ = mixedMoment B node152 node152Labels := by rfl

theorem canonical39773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39773 raw39773Labels = mixedMoment B node414 node414Labels := by
  calc
    mixedMoment B raw39773 raw39773Labels = mixedMoment B raw39773step0 raw39773step0Labels := by
      have hz : ∀ j, raw39773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39773step0 = (fun i j => raw39773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39773step0 raw39773; decide +kernel
      have hl : raw39773step0Labels = raw39773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39773 raw39773Labels permutation346 hz
    mixedMoment B raw39773step0 raw39773step0Labels = mixedMoment B raw39773step1 raw39773step1Labels := by
      have hz : ∀ j, raw39773step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39773step1 = (fun i j => raw39773step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39773step1 raw39773step0; decide +kernel
      have hl : raw39773step1Labels = raw39773step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39773step0 raw39773step0Labels permutation56 hz
    mixedMoment B raw39773step1 raw39773step1Labels = mixedMoment B raw39773step2 raw39773step2Labels := by
      have ha : raw39773step2 = (fun i j => raw39773step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39773step2 raw39773step1; decide +kernel
      have hl : raw39773step2Labels = raw39773step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39773step1 raw39773step1Labels permutation20 permutation6
    _ = mixedMoment B node414 node414Labels := by rfl

theorem canonical39774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39774 raw39774Labels = mixedMoment B node402 node402Labels := by
  calc
    mixedMoment B raw39774 raw39774Labels = mixedMoment B raw39774step0 raw39774step0Labels := by
      have hz : ∀ j, raw39774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39774step0 = (fun i j => raw39774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39774step0 raw39774; decide +kernel
      have hl : raw39774step0Labels = raw39774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39774 raw39774Labels permutation346 hz
    mixedMoment B raw39774step0 raw39774step0Labels = mixedMoment B raw39774step1 raw39774step1Labels := by
      have hz : ∀ j, raw39774step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39774step1 = (fun i j => raw39774step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39774step1 raw39774step0; decide +kernel
      have hl : raw39774step1Labels = raw39774step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39774step0 raw39774step0Labels permutation56 hz
    mixedMoment B raw39774step1 raw39774step1Labels = mixedMoment B raw39774step2 raw39774step2Labels := by
      have ha : raw39774step2 = (fun i j => raw39774step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39774step2 raw39774step1; decide +kernel
      have hl : raw39774step2Labels = raw39774step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39774step1 raw39774step1Labels permutation24 permutation6
    _ = mixedMoment B node402 node402Labels := by rfl

theorem canonical39775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39775 raw39775Labels = mixedMoment B node247 node247Labels := by
  calc
    mixedMoment B raw39775 raw39775Labels = mixedMoment B raw39775step0 raw39775step0Labels := by
      have hz : ∀ j, raw39775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39775step0 = (fun i j => raw39775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39775step0 raw39775; decide +kernel
      have hl : raw39775step0Labels = raw39775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39775 raw39775Labels permutation346 hz
    mixedMoment B raw39775step0 raw39775step0Labels = mixedMoment B raw39775step1 raw39775step1Labels := by
      have hz : ∀ j, raw39775step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39775step1 = (fun i j => raw39775step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39775step1 raw39775step0; decide +kernel
      have hl : raw39775step1Labels = raw39775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39775step0 raw39775step0Labels permutation56 hz
    mixedMoment B raw39775step1 raw39775step1Labels = mixedMoment B raw39775step2 raw39775step2Labels := by
      have ha : raw39775step2 = (fun i j => raw39775step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39775step2 raw39775step1; decide +kernel
      have hl : raw39775step2Labels = raw39775step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39775step1 raw39775step1Labels permutation15 permutation6
    mixedMoment B raw39775step2 raw39775step2Labels = mixedMoment B raw39775step3 raw39775step3Labels := by
      have ha : raw39775step3 = -raw39775step2 := by apply Matrix.ext; change ∀ i j, raw39775step3 i j = -(raw39775step2 i j); unfold raw39775step3 raw39775step2; decide +kernel
      have hl : raw39775step3Labels = raw39775step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node247 node247Labels := by rfl

theorem canonical39776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39776 raw39776Labels = mixedMoment B node270 node270Labels := by
  calc
    mixedMoment B raw39776 raw39776Labels = mixedMoment B raw39776step0 raw39776step0Labels := by
      have hz : ∀ j, raw39776 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39776step0 = (fun i j => raw39776 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39776step0 raw39776; decide +kernel
      have hl : raw39776step0Labels = raw39776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39776 raw39776Labels permutation520 hz
    mixedMoment B raw39776step0 raw39776step0Labels = mixedMoment B raw39776step1 raw39776step1Labels := by
      have hz : ∀ j, raw39776step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39776step1 = (fun i j => raw39776step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39776step1 raw39776step0; decide +kernel
      have hl : raw39776step1Labels = raw39776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39776step0 raw39776step0Labels permutation104 hz
    mixedMoment B raw39776step1 raw39776step1Labels = mixedMoment B raw39776step2 raw39776step2Labels := by
      have hz : ∀ j, raw39776step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39776step2 = (fun i j => raw39776step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39776step2 raw39776step1; decide +kernel
      have hl : raw39776step2Labels = raw39776step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39776step1 raw39776step1Labels permutation20 hz
    mixedMoment B raw39776step2 raw39776step2Labels = mixedMoment B raw39776step3 raw39776step3Labels := by
      have ha : raw39776step3 = (fun i j => raw39776step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39776step3 raw39776step2; decide +kernel
      have hl : raw39776step3Labels = raw39776step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39776step2 raw39776step2Labels permutation6 permutation5
    _ = mixedMoment B node270 node270Labels := by rfl

theorem canonical39777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39777 raw39777Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw39777 raw39777Labels = mixedMoment B raw39777step0 raw39777step0Labels := by
      have hz : ∀ j, raw39777 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39777step0 = (fun i j => raw39777 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39777step0 raw39777; decide +kernel
      have hl : raw39777step0Labels = raw39777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39777 raw39777Labels permutation434 hz
    mixedMoment B raw39777step0 raw39777step0Labels = mixedMoment B raw39777step1 raw39777step1Labels := by
      have hz : ∀ j, raw39777step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39777step1 = (fun i j => raw39777step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39777step1 raw39777step0; decide +kernel
      have hl : raw39777step1Labels = raw39777step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39777step0 raw39777step0Labels permutation80 hz
    mixedMoment B raw39777step1 raw39777step1Labels = mixedMoment B raw39777step2 raw39777step2Labels := by
      have ha : raw39777step2 = (fun i j => raw39777step1 (permutation14 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39777step2 raw39777step1; decide +kernel
      have hl : raw39777step2Labels = raw39777step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39777step1 raw39777step1Labels permutation14 permutation4
    mixedMoment B raw39777step2 raw39777step2Labels = mixedMoment B raw39777step3 raw39777step3Labels := by
      have ha : raw39777step3 = -raw39777step2 := by apply Matrix.ext; change ∀ i j, raw39777step3 i j = -(raw39777step2 i j); unfold raw39777step3 raw39777step2; decide +kernel
      have hl : raw39777step3Labels = raw39777step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node412 node412Labels := by rfl

theorem canonical39778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39778 raw39778Labels = mixedMoment B node410 node410Labels := by
  calc
    mixedMoment B raw39778 raw39778Labels = mixedMoment B raw39778step0 raw39778step0Labels := by
      have hz : ∀ j, raw39778 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39778step0 = (fun i j => raw39778 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39778step0 raw39778; decide +kernel
      have hl : raw39778step0Labels = raw39778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39778 raw39778Labels permutation434 hz
    mixedMoment B raw39778step0 raw39778step0Labels = mixedMoment B raw39778step1 raw39778step1Labels := by
      have hz : ∀ j, raw39778step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39778step1 = (fun i j => raw39778step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39778step1 raw39778step0; decide +kernel
      have hl : raw39778step1Labels = raw39778step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39778step0 raw39778step0Labels permutation80 hz
    mixedMoment B raw39778step1 raw39778step1Labels = mixedMoment B raw39778step2 raw39778step2Labels := by
      have ha : raw39778step2 = (fun i j => raw39778step1 (permutation15 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39778step2 raw39778step1; decide +kernel
      have hl : raw39778step2Labels = raw39778step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39778step1 raw39778step1Labels permutation15 permutation4
    mixedMoment B raw39778step2 raw39778step2Labels = mixedMoment B raw39778step3 raw39778step3Labels := by
      have ha : raw39778step3 = -raw39778step2 := by apply Matrix.ext; change ∀ i j, raw39778step3 i j = -(raw39778step2 i j); unfold raw39778step3 raw39778step2; decide +kernel
      have hl : raw39778step3Labels = raw39778step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node410 node410Labels := by rfl

theorem canonical39779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39779 raw39779Labels = mixedMoment B node366 node366Labels := by
  calc
    mixedMoment B raw39779 raw39779Labels = mixedMoment B raw39779step0 raw39779step0Labels := by
      have hz : ∀ j, raw39779 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39779step0 = (fun i j => raw39779 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39779step0 raw39779; decide +kernel
      have hl : raw39779step0Labels = raw39779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39779 raw39779Labels permutation434 hz
    mixedMoment B raw39779step0 raw39779step0Labels = mixedMoment B raw39779step1 raw39779step1Labels := by
      have hz : ∀ j, raw39779step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39779step1 = (fun i j => raw39779step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39779step1 raw39779step0; decide +kernel
      have hl : raw39779step1Labels = raw39779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39779step0 raw39779step0Labels permutation80 hz
    mixedMoment B raw39779step1 raw39779step1Labels = mixedMoment B raw39779step2 raw39779step2Labels := by
      have ha : raw39779step2 = (fun i j => raw39779step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39779step2 raw39779step1; decide +kernel
      have hl : raw39779step2Labels = raw39779step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39779step1 raw39779step1Labels permutation21 permutation4
    _ = mixedMoment B node366 node366Labels := by rfl

theorem canonical39780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39780 raw39780Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39780 raw39780Labels = mixedMoment B raw39780step0 raw39780step0Labels := by
      have hz : ∀ j, raw39780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39780step0 = (fun i j => raw39780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39780step0 raw39780; decide +kernel
      have hl : raw39780step0Labels = raw39780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39780 raw39780Labels permutation346 hz
    mixedMoment B raw39780step0 raw39780step0Labels = mixedMoment B raw39780step1 raw39780step1Labels := by
      have ha : raw39780step1 = (fun i j => raw39780step0 (permutation68 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39780step1 raw39780step0; decide +kernel
      have hl : raw39780step1Labels = raw39780step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39780step0 raw39780step0Labels permutation68 permutation4
    mixedMoment B raw39780step1 raw39780step1Labels = mixedMoment B raw39780step2 raw39780step2Labels := by
      have ha : raw39780step2 = -raw39780step1 := by apply Matrix.ext; change ∀ i j, raw39780step2 i j = -(raw39780step1 i j); unfold raw39780step2 raw39780step1; decide +kernel
      have hl : raw39780step2Labels = raw39780step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node384 node384Labels := by rfl

theorem canonical39781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39781 raw39781Labels = mixedMoment B node409 node409Labels := by
  calc
    mixedMoment B raw39781 raw39781Labels = mixedMoment B raw39781step0 raw39781step0Labels := by
      have hz : ∀ j, raw39781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39781step0 = (fun i j => raw39781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39781step0 raw39781; decide +kernel
      have hl : raw39781step0Labels = raw39781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39781 raw39781Labels permutation346 hz
    mixedMoment B raw39781step0 raw39781step0Labels = mixedMoment B raw39781step1 raw39781step1Labels := by
      have ha : raw39781step1 = (fun i j => raw39781step0 (permutation61 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39781step1 raw39781step0; decide +kernel
      have hl : raw39781step1Labels = raw39781step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39781step0 raw39781step0Labels permutation61 permutation4
    mixedMoment B raw39781step1 raw39781step1Labels = mixedMoment B raw39781step2 raw39781step2Labels := by
      have ha : raw39781step2 = -raw39781step1 := by apply Matrix.ext; change ∀ i j, raw39781step2 i j = -(raw39781step1 i j); unfold raw39781step2 raw39781step1; decide +kernel
      have hl : raw39781step2Labels = raw39781step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node409 node409Labels := by rfl

theorem canonical39782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39782 raw39782Labels = mixedMoment B node365 node365Labels := by
  calc
    mixedMoment B raw39782 raw39782Labels = mixedMoment B raw39782step0 raw39782step0Labels := by
      have hz : ∀ j, raw39782 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39782step0 = (fun i j => raw39782 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39782step0 raw39782; decide +kernel
      have hl : raw39782step0Labels = raw39782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39782 raw39782Labels permutation346 hz
    mixedMoment B raw39782step0 raw39782step0Labels = mixedMoment B raw39782step1 raw39782step1Labels := by
      have ha : raw39782step1 = (fun i j => raw39782step0 (permutation74 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39782step1 raw39782step0; decide +kernel
      have hl : raw39782step1Labels = raw39782step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39782step0 raw39782step0Labels permutation74 permutation4
    mixedMoment B raw39782step1 raw39782step1Labels = mixedMoment B raw39782step2 raw39782step2Labels := by
      have ha : raw39782step2 = -raw39782step1 := by apply Matrix.ext; change ∀ i j, raw39782step2 i j = -(raw39782step1 i j); unfold raw39782step2 raw39782step1; decide +kernel
      have hl : raw39782step2Labels = raw39782step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node365 node365Labels := by rfl

theorem canonical39783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39783 raw39783Labels = mixedMoment B node364 node364Labels := by
  calc
    mixedMoment B raw39783 raw39783Labels = mixedMoment B raw39783step0 raw39783step0Labels := by
      have hz : ∀ j, raw39783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39783step0 = (fun i j => raw39783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39783step0 raw39783; decide +kernel
      have hl : raw39783step0Labels = raw39783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39783 raw39783Labels permutation346 hz
    mixedMoment B raw39783step0 raw39783step0Labels = mixedMoment B raw39783step1 raw39783step1Labels := by
      have ha : raw39783step1 = (fun i j => raw39783step0 (permutation75 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39783step1 raw39783step0; decide +kernel
      have hl : raw39783step1Labels = raw39783step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39783step0 raw39783step0Labels permutation75 permutation4
    mixedMoment B raw39783step1 raw39783step1Labels = mixedMoment B raw39783step2 raw39783step2Labels := by
      have ha : raw39783step2 = -raw39783step1 := by apply Matrix.ext; change ∀ i j, raw39783step2 i j = -(raw39783step1 i j); unfold raw39783step2 raw39783step1; decide +kernel
      have hl : raw39783step2Labels = raw39783step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node364 node364Labels := by rfl

theorem canonical39784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39784 raw39784Labels = mixedMoment B node363 node363Labels := by
  calc
    mixedMoment B raw39784 raw39784Labels = mixedMoment B raw39784step0 raw39784step0Labels := by
      have ha : raw39784step0 = (fun i j => raw39784 (permutation337 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39784step0 raw39784; decide +kernel
      have hl : raw39784step0Labels = raw39784Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39784 raw39784Labels permutation337 permutation4
    mixedMoment B raw39784step0 raw39784step0Labels = mixedMoment B raw39784step1 raw39784step1Labels := by
      have ha : raw39784step1 = -raw39784step0 := by apply Matrix.ext; change ∀ i j, raw39784step1 i j = -(raw39784step0 i j); unfold raw39784step1 raw39784step0; decide +kernel
      have hl : raw39784step1Labels = raw39784step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node363 node363Labels := by rfl

theorem canonical39785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39785 raw39785Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw39785 raw39785Labels = mixedMoment B raw39785step0 raw39785step0Labels := by
      have hz : ∀ j, raw39785 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39785step0 = (fun i j => raw39785 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39785step0 raw39785; decide +kernel
      have hl : raw39785step0Labels = raw39785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39785 raw39785Labels permutation520 hz
    mixedMoment B raw39785step0 raw39785step0Labels = mixedMoment B raw39785step1 raw39785step1Labels := by
      have hz : ∀ j, raw39785step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39785step1 = (fun i j => raw39785step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39785step1 raw39785step0; decide +kernel
      have hl : raw39785step1Labels = raw39785step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39785step0 raw39785step0Labels permutation104 hz
    mixedMoment B raw39785step1 raw39785step1Labels = mixedMoment B raw39785step2 raw39785step2Labels := by
      have ha : raw39785step2 = (fun i j => raw39785step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39785step2 raw39785step1; decide +kernel
      have hl : raw39785step2Labels = raw39785step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39785step1 raw39785step1Labels permutation31 permutation3
    mixedMoment B raw39785step2 raw39785step2Labels = mixedMoment B raw39785step3 raw39785step3Labels := by
      have ha : raw39785step3 = -raw39785step2 := by apply Matrix.ext; change ∀ i j, raw39785step3 i j = -(raw39785step2 i j); unfold raw39785step3 raw39785step2; decide +kernel
      have hl : raw39785step3Labels = raw39785step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node268 node268Labels := by rfl

theorem canonical39786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39786 raw39786Labels = mixedMoment B node383 node383Labels := by
  calc
    mixedMoment B raw39786 raw39786Labels = mixedMoment B raw39786step0 raw39786step0Labels := by
      have hz : ∀ j, raw39786 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39786step0 = (fun i j => raw39786 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39786step0 raw39786; decide +kernel
      have hl : raw39786step0Labels = raw39786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39786 raw39786Labels permutation434 hz
    mixedMoment B raw39786step0 raw39786step0Labels = mixedMoment B raw39786step1 raw39786step1Labels := by
      have ha : raw39786step1 = (fun i j => raw39786step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39786step1 raw39786step0; decide +kernel
      have hl : raw39786step1Labels = raw39786step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39786step0 raw39786step0Labels permutation147 permutation5
    _ = mixedMoment B node383 node383Labels := by rfl

theorem canonical39787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39787 raw39787Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw39787 raw39787Labels = mixedMoment B raw39787step0 raw39787step0Labels := by
      have hz : ∀ j, raw39787 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39787step0 = (fun i j => raw39787 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39787step0 raw39787; decide +kernel
      have hl : raw39787step0Labels = raw39787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39787 raw39787Labels permutation434 hz
    mixedMoment B raw39787step0 raw39787step0Labels = mixedMoment B raw39787step1 raw39787step1Labels := by
      have ha : raw39787step1 = (fun i j => raw39787step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39787step1 raw39787step0; decide +kernel
      have hl : raw39787step1Labels = raw39787step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39787step0 raw39787step0Labels permutation151 permutation3
    mixedMoment B raw39787step1 raw39787step1Labels = mixedMoment B raw39787step2 raw39787step2Labels := by
      have ha : raw39787step2 = -raw39787step1 := by apply Matrix.ext; change ∀ i j, raw39787step2 i j = -(raw39787step1 i j); unfold raw39787step2 raw39787step1; decide +kernel
      have hl : raw39787step2Labels = raw39787step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node467 node467Labels := by rfl

theorem canonical39788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39788 raw39788Labels = mixedMoment B node498 node498Labels := by
  calc
    mixedMoment B raw39788 raw39788Labels = mixedMoment B raw39788step0 raw39788step0Labels := by
      have hz : ∀ j, raw39788 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39788step0 = (fun i j => raw39788 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39788step0 raw39788; decide +kernel
      have hl : raw39788step0Labels = raw39788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39788 raw39788Labels permutation434 hz
    _ = mixedMoment B node498 node498Labels := by rfl

theorem canonical39789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39789 raw39789Labels = mixedMoment B node365 node365Labels := by
  calc
    mixedMoment B raw39789 raw39789Labels = mixedMoment B raw39789step0 raw39789step0Labels := by
      have hz : ∀ j, raw39789 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39789step0 = (fun i j => raw39789 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39789step0 raw39789; decide +kernel
      have hl : raw39789step0Labels = raw39789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39789 raw39789Labels permutation434 hz
    mixedMoment B raw39789step0 raw39789step0Labels = mixedMoment B raw39789step1 raw39789step1Labels := by
      have ha : raw39789step1 = (fun i j => raw39789step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39789step1 raw39789step0; decide +kernel
      have hl : raw39789step1Labels = raw39789step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39789step0 raw39789step0Labels permutation109 permutation4
    _ = mixedMoment B node365 node365Labels := by rfl

theorem canonical39790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39790 raw39790Labels = mixedMoment B node480 node480Labels := by
  calc
    mixedMoment B raw39790 raw39790Labels = mixedMoment B raw39790step0 raw39790step0Labels := by
      have ha : raw39790step0 = (fun i j => raw39790 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39790step0 raw39790; decide +kernel
      have hl : raw39790step0Labels = raw39790Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39790 raw39790Labels permutation688 permutation3
    mixedMoment B raw39790step0 raw39790step0Labels = mixedMoment B raw39790step1 raw39790step1Labels := by
      have ha : raw39790step1 = -raw39790step0 := by apply Matrix.ext; change ∀ i j, raw39790step1 i j = -(raw39790step0 i j); unfold raw39790step1 raw39790step0; decide +kernel
      have hl : raw39790step1Labels = raw39790step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node480 node480Labels := by rfl

theorem canonical39791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39791 raw39791Labels = mixedMoment B node475 node475Labels := by
  calc
    mixedMoment B raw39791 raw39791Labels = mixedMoment B raw39791step0 raw39791step0Labels := by
      have ha : raw39791step0 = (fun i j => raw39791 (permutation634 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39791step0 raw39791; decide +kernel
      have hl : raw39791step0Labels = raw39791Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39791 raw39791Labels permutation634 permutation7
    _ = mixedMoment B node475 node475Labels := by rfl

theorem canonical39792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39792 raw39792Labels = mixedMoment B node443 node443Labels := by
  calc
    mixedMoment B raw39792 raw39792Labels = mixedMoment B raw39792step0 raw39792step0Labels := by
      have ha : raw39792step0 = (fun i j => raw39792 (permutation445 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39792step0 raw39792; decide +kernel
      have hl : raw39792step0Labels = raw39792Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39792 raw39792Labels permutation445 permutation6
    mixedMoment B raw39792step0 raw39792step0Labels = mixedMoment B raw39792step1 raw39792step1Labels := by
      have ha : raw39792step1 = -raw39792step0 := by apply Matrix.ext; change ∀ i j, raw39792step1 i j = -(raw39792step0 i j); unfold raw39792step1 raw39792step0; decide +kernel
      have hl : raw39792step1Labels = raw39792step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node443 node443Labels := by rfl

theorem canonical39793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39793 raw39793Labels = mixedMoment B node497 node497Labels := by
  calc
    mixedMoment B raw39793 raw39793Labels = mixedMoment B raw39793step0 raw39793step0Labels := by
      have ha : raw39793step0 = (fun i j => raw39793 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39793step0 raw39793; decide +kernel
      have hl : raw39793step0Labels = raw39793Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39793 raw39793Labels permutation157 permutation2
    _ = mixedMoment B node497 node497Labels := by rfl

theorem canonical39794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39794 raw39794Labels = mixedMoment B node410 node410Labels := by
  calc
    mixedMoment B raw39794 raw39794Labels = mixedMoment B raw39794step0 raw39794step0Labels := by
      have hz : ∀ j, raw39794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39794step0 = (fun i j => raw39794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39794step0 raw39794; decide +kernel
      have hl : raw39794step0Labels = raw39794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39794 raw39794Labels permutation434 hz
    mixedMoment B raw39794step0 raw39794step0Labels = mixedMoment B raw39794step1 raw39794step1Labels := by
      have hz : ∀ j, raw39794step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39794step1 = (fun i j => raw39794step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39794step1 raw39794step0; decide +kernel
      have hl : raw39794step1Labels = raw39794step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39794step0 raw39794step0Labels permutation80 hz
    mixedMoment B raw39794step1 raw39794step1Labels = mixedMoment B raw39794step2 raw39794step2Labels := by
      have ha : raw39794step2 = (fun i j => raw39794step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39794step2 raw39794step1; decide +kernel
      have hl : raw39794step2Labels = raw39794step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39794step1 raw39794step1Labels permutation27 permutation5
    _ = mixedMoment B node410 node410Labels := by rfl

theorem canonical39795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39795 raw39795Labels = mixedMoment B node503 node503Labels := by
  calc
    mixedMoment B raw39795 raw39795Labels = mixedMoment B raw39795step0 raw39795step0Labels := by
      have hz : ∀ j, raw39795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39795step0 = (fun i j => raw39795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39795step0 raw39795; decide +kernel
      have hl : raw39795step0Labels = raw39795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39795 raw39795Labels permutation434 hz
    mixedMoment B raw39795step0 raw39795step0Labels = mixedMoment B raw39795step1 raw39795step1Labels := by
      have hz : ∀ j, raw39795step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39795step1 = (fun i j => raw39795step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39795step1 raw39795step0; decide +kernel
      have hl : raw39795step1Labels = raw39795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39795step0 raw39795step0Labels permutation80 hz
    _ = mixedMoment B node503 node503Labels := by rfl

theorem canonical39796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39796 raw39796Labels = mixedMoment B node501 node501Labels := by
  calc
    mixedMoment B raw39796 raw39796Labels = mixedMoment B raw39796step0 raw39796step0Labels := by
      have hz : ∀ j, raw39796 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39796step0 = (fun i j => raw39796 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39796step0 raw39796; decide +kernel
      have hl : raw39796step0Labels = raw39796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39796 raw39796Labels permutation434 hz
    mixedMoment B raw39796step0 raw39796step0Labels = mixedMoment B raw39796step1 raw39796step1Labels := by
      have hz : ∀ j, raw39796step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39796step1 = (fun i j => raw39796step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39796step1 raw39796step0; decide +kernel
      have hl : raw39796step1Labels = raw39796step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39796step0 raw39796step0Labels permutation80 hz
    _ = mixedMoment B node501 node501Labels := by rfl

theorem canonical39797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39797 raw39797Labels = mixedMoment B node354 node354Labels := by
  calc
    mixedMoment B raw39797 raw39797Labels = mixedMoment B raw39797step0 raw39797step0Labels := by
      have hz : ∀ j, raw39797 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39797step0 = (fun i j => raw39797 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39797step0 raw39797; decide +kernel
      have hl : raw39797step0Labels = raw39797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39797 raw39797Labels permutation434 hz
    mixedMoment B raw39797step0 raw39797step0Labels = mixedMoment B raw39797step1 raw39797step1Labels := by
      have hz : ∀ j, raw39797step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39797step1 = (fun i j => raw39797step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39797step1 raw39797step0; decide +kernel
      have hl : raw39797step1Labels = raw39797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39797step0 raw39797step0Labels permutation80 hz
    mixedMoment B raw39797step1 raw39797step1Labels = mixedMoment B raw39797step2 raw39797step2Labels := by
      have ha : raw39797step2 = (fun i j => raw39797step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39797step2 raw39797step1; decide +kernel
      have hl : raw39797step2Labels = raw39797step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39797step1 raw39797step1Labels permutation29 permutation7
    _ = mixedMoment B node354 node354Labels := by rfl

theorem canonical39798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39798 raw39798Labels = mixedMoment B node491 node491Labels := by
  calc
    mixedMoment B raw39798 raw39798Labels = mixedMoment B raw39798step0 raw39798step0Labels := by
      have hz : ∀ j, raw39798 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39798step0 = (fun i j => raw39798 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39798step0 raw39798; decide +kernel
      have hl : raw39798step0Labels = raw39798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39798 raw39798Labels permutation346 hz
    mixedMoment B raw39798step0 raw39798step0Labels = mixedMoment B raw39798step1 raw39798step1Labels := by
      have ha : raw39798step1 = (fun i j => raw39798step0 (permutation141 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39798step1 raw39798step0; decide +kernel
      have hl : raw39798step1Labels = raw39798step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39798step0 raw39798step0Labels permutation141 permutation5
    _ = mixedMoment B node491 node491Labels := by rfl

theorem canonical39799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39799 raw39799Labels = mixedMoment B node487 node487Labels := by
  calc
    mixedMoment B raw39799 raw39799Labels = mixedMoment B raw39799step0 raw39799step0Labels := by
      have hz : ∀ j, raw39799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39799step0 = (fun i j => raw39799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39799step0 raw39799; decide +kernel
      have hl : raw39799step0Labels = raw39799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39799 raw39799Labels permutation346 hz
    mixedMoment B raw39799step0 raw39799step0Labels = mixedMoment B raw39799step1 raw39799step1Labels := by
      have ha : raw39799step1 = (fun i j => raw39799step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39799step1 raw39799step0; decide +kernel
      have hl : raw39799step1Labels = raw39799step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39799step0 raw39799step0Labels permutation151 permutation2
    mixedMoment B raw39799step1 raw39799step1Labels = mixedMoment B raw39799step2 raw39799step2Labels := by
      have ha : raw39799step2 = -raw39799step1 := by apply Matrix.ext; change ∀ i j, raw39799step2 i j = -(raw39799step1 i j); unfold raw39799step2 raw39799step1; decide +kernel
      have hl : raw39799step2Labels = raw39799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node487 node487Labels := by rfl

theorem canonical39800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39800 raw39800Labels = mixedMoment B node348 node348Labels := by
  calc
    mixedMoment B raw39800 raw39800Labels = mixedMoment B raw39800step0 raw39800step0Labels := by
      have hz : ∀ j, raw39800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39800step0 = (fun i j => raw39800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39800step0 raw39800; decide +kernel
      have hl : raw39800step0Labels = raw39800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39800 raw39800Labels permutation346 hz
    mixedMoment B raw39800step0 raw39800step0Labels = mixedMoment B raw39800step1 raw39800step1Labels := by
      have ha : raw39800step1 = (fun i j => raw39800step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39800step1 raw39800step0; decide +kernel
      have hl : raw39800step1Labels = raw39800step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39800step0 raw39800step0Labels permutation139 permutation7
    _ = mixedMoment B node348 node348Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 320) =
      Integer.Sparse.eval keyMomentRow320 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 320).leftCharge (GramAssembly.key 320).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 415) := by
    have ha : gramCharges (GramAssembly.key 320).leftCharge (GramAssembly.key 320).rightCharge = raw39770 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39770Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39770 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 320).leftCharge (GramAssembly.key 320).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow320, Integer.Sparse.eval]

theorem keyMoment321 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 321) =
      Integer.Sparse.eval keyMomentRow321 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 321).leftCharge (GramAssembly.key 321).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 416) := by
    have ha : gramCharges (GramAssembly.key 321).leftCharge (GramAssembly.key 321).rightCharge = raw39771 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39771Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39771 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 321).leftCharge (GramAssembly.key 321).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow321, Integer.Sparse.eval]

theorem keyMoment322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 322) =
      Integer.Sparse.eval keyMomentRow322 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 322).leftCharge (GramAssembly.key 322).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 152) := by
    have ha : gramCharges (GramAssembly.key 322).leftCharge (GramAssembly.key 322).rightCharge = raw39772 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39772Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39772 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 322).leftCharge (GramAssembly.key 322).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow322, Integer.Sparse.eval]

theorem keyMoment323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 323) =
      Integer.Sparse.eval keyMomentRow323 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 323).leftCharge (GramAssembly.key 323).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 414) := by
    have ha : gramCharges (GramAssembly.key 323).leftCharge (GramAssembly.key 323).rightCharge = raw39773 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39773Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39773 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 323).leftCharge (GramAssembly.key 323).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow323, Integer.Sparse.eval]

theorem keyMoment324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 324) =
      Integer.Sparse.eval keyMomentRow324 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 324).leftCharge (GramAssembly.key 324).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 402) := by
    have ha : gramCharges (GramAssembly.key 324).leftCharge (GramAssembly.key 324).rightCharge = raw39774 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39774Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39774 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 324).leftCharge (GramAssembly.key 324).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow324, Integer.Sparse.eval]

theorem keyMoment325 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 325) =
      Integer.Sparse.eval keyMomentRow325 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 325).leftCharge (GramAssembly.key 325).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 247) := by
    have ha : gramCharges (GramAssembly.key 325).leftCharge (GramAssembly.key 325).rightCharge = raw39775 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39775Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39775 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 325).leftCharge (GramAssembly.key 325).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow325, Integer.Sparse.eval]

theorem keyMoment326 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 326) =
      Integer.Sparse.eval keyMomentRow326 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 326).leftCharge (GramAssembly.key 326).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 270) := by
    have ha : gramCharges (GramAssembly.key 326).leftCharge (GramAssembly.key 326).rightCharge = raw39776 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39776Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39776 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 326).leftCharge (GramAssembly.key 326).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow326, Integer.Sparse.eval]

theorem keyMoment327 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 327) =
      Integer.Sparse.eval keyMomentRow327 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 327).leftCharge (GramAssembly.key 327).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 412) := by
    have ha : gramCharges (GramAssembly.key 327).leftCharge (GramAssembly.key 327).rightCharge = raw39777 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39777Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39777 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 327).leftCharge (GramAssembly.key 327).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow327, Integer.Sparse.eval]

theorem keyMoment328 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 328) =
      Integer.Sparse.eval keyMomentRow328 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 328).leftCharge (GramAssembly.key 328).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 410) := by
    have ha : gramCharges (GramAssembly.key 328).leftCharge (GramAssembly.key 328).rightCharge = raw39778 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39778Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39778 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 328).leftCharge (GramAssembly.key 328).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow328, Integer.Sparse.eval]

theorem keyMoment329 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 329) =
      Integer.Sparse.eval keyMomentRow329 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 329).leftCharge (GramAssembly.key 329).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 366) := by
    have ha : gramCharges (GramAssembly.key 329).leftCharge (GramAssembly.key 329).rightCharge = raw39779 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39779Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39779 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 329).leftCharge (GramAssembly.key 329).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow329, Integer.Sparse.eval]

theorem keyMoment330 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 330) =
      Integer.Sparse.eval keyMomentRow330 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 330).leftCharge (GramAssembly.key 330).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 330).leftCharge (GramAssembly.key 330).rightCharge = raw39780 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39780Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39780 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 330).leftCharge (GramAssembly.key 330).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow330, Integer.Sparse.eval]

theorem keyMoment331 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 331) =
      Integer.Sparse.eval keyMomentRow331 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 331).leftCharge (GramAssembly.key 331).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 409) := by
    have ha : gramCharges (GramAssembly.key 331).leftCharge (GramAssembly.key 331).rightCharge = raw39781 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39781Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39781 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 331).leftCharge (GramAssembly.key 331).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow331, Integer.Sparse.eval]

theorem keyMoment332 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 332) =
      Integer.Sparse.eval keyMomentRow332 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 332).leftCharge (GramAssembly.key 332).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 365) := by
    have ha : gramCharges (GramAssembly.key 332).leftCharge (GramAssembly.key 332).rightCharge = raw39782 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39782Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39782 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 332).leftCharge (GramAssembly.key 332).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow332, Integer.Sparse.eval]

theorem keyMoment333 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 333) =
      Integer.Sparse.eval keyMomentRow333 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 333).leftCharge (GramAssembly.key 333).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 364) := by
    have ha : gramCharges (GramAssembly.key 333).leftCharge (GramAssembly.key 333).rightCharge = raw39783 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39783Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39783 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 333).leftCharge (GramAssembly.key 333).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow333, Integer.Sparse.eval]

theorem keyMoment334 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 334) =
      Integer.Sparse.eval keyMomentRow334 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 334).leftCharge (GramAssembly.key 334).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 363) := by
    have ha : gramCharges (GramAssembly.key 334).leftCharge (GramAssembly.key 334).rightCharge = raw39784 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39784Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39784 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 334).leftCharge (GramAssembly.key 334).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow334, Integer.Sparse.eval]

theorem keyMoment335 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 335) =
      Integer.Sparse.eval keyMomentRow335 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 335).leftCharge (GramAssembly.key 335).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 268) := by
    have ha : gramCharges (GramAssembly.key 335).leftCharge (GramAssembly.key 335).rightCharge = raw39785 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39785Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39785 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 335).leftCharge (GramAssembly.key 335).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow335, Integer.Sparse.eval]

theorem keyMoment336 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 336) =
      Integer.Sparse.eval keyMomentRow336 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 336).leftCharge (GramAssembly.key 336).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 383) := by
    have ha : gramCharges (GramAssembly.key 336).leftCharge (GramAssembly.key 336).rightCharge = raw39786 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39786Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39786 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 336).leftCharge (GramAssembly.key 336).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow336, Integer.Sparse.eval]

theorem keyMoment337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 337) =
      Integer.Sparse.eval keyMomentRow337 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 337).leftCharge (GramAssembly.key 337).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 467) := by
    have ha : gramCharges (GramAssembly.key 337).leftCharge (GramAssembly.key 337).rightCharge = raw39787 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39787Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39787 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 337).leftCharge (GramAssembly.key 337).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow337, Integer.Sparse.eval]

theorem keyMoment338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 338) =
      Integer.Sparse.eval keyMomentRow338 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 338).leftCharge (GramAssembly.key 338).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 498) := by
    have ha : gramCharges (GramAssembly.key 338).leftCharge (GramAssembly.key 338).rightCharge = raw39788 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39788Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39788 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 338).leftCharge (GramAssembly.key 338).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow338, Integer.Sparse.eval]

theorem keyMoment339 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 339) =
      Integer.Sparse.eval keyMomentRow339 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 339).leftCharge (GramAssembly.key 339).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 365) := by
    have ha : gramCharges (GramAssembly.key 339).leftCharge (GramAssembly.key 339).rightCharge = raw39789 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39789Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39789 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 339).leftCharge (GramAssembly.key 339).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow339, Integer.Sparse.eval]

theorem keyMoment340 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 340) =
      Integer.Sparse.eval keyMomentRow340 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 340).leftCharge (GramAssembly.key 340).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 480) := by
    have ha : gramCharges (GramAssembly.key 340).leftCharge (GramAssembly.key 340).rightCharge = raw39790 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39790Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39790 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 340).leftCharge (GramAssembly.key 340).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow340, Integer.Sparse.eval]

theorem keyMoment341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 341) =
      Integer.Sparse.eval keyMomentRow341 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 341).leftCharge (GramAssembly.key 341).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 475) := by
    have ha : gramCharges (GramAssembly.key 341).leftCharge (GramAssembly.key 341).rightCharge = raw39791 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39791Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39791 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 341).leftCharge (GramAssembly.key 341).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow341, Integer.Sparse.eval]

theorem keyMoment342 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 342) =
      Integer.Sparse.eval keyMomentRow342 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 342).leftCharge (GramAssembly.key 342).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 443) := by
    have ha : gramCharges (GramAssembly.key 342).leftCharge (GramAssembly.key 342).rightCharge = raw39792 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39792Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39792 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 342).leftCharge (GramAssembly.key 342).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow342, Integer.Sparse.eval]

theorem keyMoment343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 343) =
      Integer.Sparse.eval keyMomentRow343 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 343).leftCharge (GramAssembly.key 343).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 497) := by
    have ha : gramCharges (GramAssembly.key 343).leftCharge (GramAssembly.key 343).rightCharge = raw39793 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39793Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39793 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 343).leftCharge (GramAssembly.key 343).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow343, Integer.Sparse.eval]

theorem keyMoment344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 344) =
      Integer.Sparse.eval keyMomentRow344 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 344).leftCharge (GramAssembly.key 344).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 499) := by
    have ha : gramCharges (GramAssembly.key 344).leftCharge (GramAssembly.key 344).rightCharge = raw38095 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw38095Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical38095 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 344).leftCharge (GramAssembly.key 344).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow344, Integer.Sparse.eval]

theorem keyMoment345 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 345) =
      Integer.Sparse.eval keyMomentRow345 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 345).leftCharge (GramAssembly.key 345).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 410) := by
    have ha : gramCharges (GramAssembly.key 345).leftCharge (GramAssembly.key 345).rightCharge = raw39794 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39794Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39794 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 345).leftCharge (GramAssembly.key 345).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow345, Integer.Sparse.eval]

theorem keyMoment346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 346) =
      Integer.Sparse.eval keyMomentRow346 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 346).leftCharge (GramAssembly.key 346).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 503) := by
    have ha : gramCharges (GramAssembly.key 346).leftCharge (GramAssembly.key 346).rightCharge = raw39795 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39795Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39795 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 346).leftCharge (GramAssembly.key 346).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow346, Integer.Sparse.eval]

theorem keyMoment347 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 347) =
      Integer.Sparse.eval keyMomentRow347 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 347).leftCharge (GramAssembly.key 347).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 501) := by
    have ha : gramCharges (GramAssembly.key 347).leftCharge (GramAssembly.key 347).rightCharge = raw39796 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39796Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39796 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 347).leftCharge (GramAssembly.key 347).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow347, Integer.Sparse.eval]

theorem keyMoment348 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 348) =
      Integer.Sparse.eval keyMomentRow348 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 348).leftCharge (GramAssembly.key 348).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 354) := by
    have ha : gramCharges (GramAssembly.key 348).leftCharge (GramAssembly.key 348).rightCharge = raw39797 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39797Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39797 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 348).leftCharge (GramAssembly.key 348).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow348, Integer.Sparse.eval]

theorem keyMoment349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 349) =
      Integer.Sparse.eval keyMomentRow349 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 349).leftCharge (GramAssembly.key 349).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 491) := by
    have ha : gramCharges (GramAssembly.key 349).leftCharge (GramAssembly.key 349).rightCharge = raw39798 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39798Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39798 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 349).leftCharge (GramAssembly.key 349).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow349, Integer.Sparse.eval]

theorem keyMoment350 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 350) =
      Integer.Sparse.eval keyMomentRow350 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 350).leftCharge (GramAssembly.key 350).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 487) := by
    have ha : gramCharges (GramAssembly.key 350).leftCharge (GramAssembly.key 350).rightCharge = raw39799 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39799Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39799 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 350).leftCharge (GramAssembly.key 350).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow350, Integer.Sparse.eval]

theorem keyMoment351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 351) =
      Integer.Sparse.eval keyMomentRow351 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 351).leftCharge (GramAssembly.key 351).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 348) := by
    have ha : gramCharges (GramAssembly.key 351).leftCharge (GramAssembly.key 351).rightCharge = raw39800 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39800Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39800 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 351).leftCharge (GramAssembly.key 351).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow351, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt320 : keyMomentRows (320 : Fin 2886) =
    keyMomentRow320 := by decide +kernel

theorem keyMomentRowsAt321 : keyMomentRows (321 : Fin 2886) =
    keyMomentRow321 := by decide +kernel

theorem keyMomentRowsAt322 : keyMomentRows (322 : Fin 2886) =
    keyMomentRow322 := by decide +kernel

theorem keyMomentRowsAt323 : keyMomentRows (323 : Fin 2886) =
    keyMomentRow323 := by decide +kernel

theorem keyMomentRowsAt324 : keyMomentRows (324 : Fin 2886) =
    keyMomentRow324 := by decide +kernel

theorem keyMomentRowsAt325 : keyMomentRows (325 : Fin 2886) =
    keyMomentRow325 := by decide +kernel

theorem keyMomentRowsAt326 : keyMomentRows (326 : Fin 2886) =
    keyMomentRow326 := by decide +kernel

theorem keyMomentRowsAt327 : keyMomentRows (327 : Fin 2886) =
    keyMomentRow327 := by decide +kernel

theorem keyMomentRowsAt328 : keyMomentRows (328 : Fin 2886) =
    keyMomentRow328 := by decide +kernel

theorem keyMomentRowsAt329 : keyMomentRows (329 : Fin 2886) =
    keyMomentRow329 := by decide +kernel

theorem keyMomentRowsAt330 : keyMomentRows (330 : Fin 2886) =
    keyMomentRow330 := by decide +kernel

theorem keyMomentRowsAt331 : keyMomentRows (331 : Fin 2886) =
    keyMomentRow331 := by decide +kernel

theorem keyMomentRowsAt332 : keyMomentRows (332 : Fin 2886) =
    keyMomentRow332 := by decide +kernel

theorem keyMomentRowsAt333 : keyMomentRows (333 : Fin 2886) =
    keyMomentRow333 := by decide +kernel

theorem keyMomentRowsAt334 : keyMomentRows (334 : Fin 2886) =
    keyMomentRow334 := by decide +kernel

theorem keyMomentRowsAt335 : keyMomentRows (335 : Fin 2886) =
    keyMomentRow335 := by decide +kernel

theorem keyMomentRowsAt336 : keyMomentRows (336 : Fin 2886) =
    keyMomentRow336 := by decide +kernel

theorem keyMomentRowsAt337 : keyMomentRows (337 : Fin 2886) =
    keyMomentRow337 := by decide +kernel

theorem keyMomentRowsAt338 : keyMomentRows (338 : Fin 2886) =
    keyMomentRow338 := by decide +kernel

theorem keyMomentRowsAt339 : keyMomentRows (339 : Fin 2886) =
    keyMomentRow339 := by decide +kernel

theorem keyMomentRowsAt340 : keyMomentRows (340 : Fin 2886) =
    keyMomentRow340 := by decide +kernel

theorem keyMomentRowsAt341 : keyMomentRows (341 : Fin 2886) =
    keyMomentRow341 := by decide +kernel

theorem keyMomentRowsAt342 : keyMomentRows (342 : Fin 2886) =
    keyMomentRow342 := by decide +kernel

theorem keyMomentRowsAt343 : keyMomentRows (343 : Fin 2886) =
    keyMomentRow343 := by decide +kernel

theorem keyMomentRowsAt344 : keyMomentRows (344 : Fin 2886) =
    keyMomentRow344 := by decide +kernel

theorem keyMomentRowsAt345 : keyMomentRows (345 : Fin 2886) =
    keyMomentRow345 := by decide +kernel

theorem keyMomentRowsAt346 : keyMomentRows (346 : Fin 2886) =
    keyMomentRow346 := by decide +kernel

theorem keyMomentRowsAt347 : keyMomentRows (347 : Fin 2886) =
    keyMomentRow347 := by decide +kernel

theorem keyMomentRowsAt348 : keyMomentRows (348 : Fin 2886) =
    keyMomentRow348 := by decide +kernel

theorem keyMomentRowsAt349 : keyMomentRows (349 : Fin 2886) =
    keyMomentRow349 := by decide +kernel

theorem keyMomentRowsAt350 : keyMomentRows (350 : Fin 2886) =
    keyMomentRow350 := by decide +kernel

theorem keyMomentRowsAt351 : keyMomentRows (351 : Fin 2886) =
    keyMomentRow351 := by decide +kernel

theorem keyMomentChunkSound10_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 10) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 320 ∨ k.val = 321 ∨ k.val = 322 ∨ k.val = 323 ∨ k.val = 324 ∨ k.val = 325 ∨ k.val = 326 ∨ k.val = 327 ∨ k.val = 328 ∨ k.val = 329 ∨ k.val = 330 ∨ k.val = 331 ∨ k.val = 332 ∨ k.val = 333 ∨ k.val = 334 ∨ k.val = 335 ∨ k.val = 336 ∨ k.val = 337 ∨ k.val = 338 ∨ k.val = 339 ∨ k.val = 340 ∨ k.val = 341 ∨ k.val = 342 ∨ k.val = 343 ∨ k.val = 344 ∨ k.val = 345 ∨ k.val = 346 ∨ k.val = 347 ∨ k.val = 348 ∨ k.val = 349 ∨ k.val = 350 ∨ k.val = 351 := by omega
  rcases heq with h320 | h321 | h322 | h323 | h324 | h325 | h326 | h327 | h328 | h329 | h330 | h331 | h332 | h333 | h334 | h335 | h336 | h337 | h338 | h339 | h340 | h341 | h342 | h343 | h344 | h345 | h346 | h347 | h348 | h349 | h350 | h351
  · have he : k = (320 : Fin 2886) := Fin.ext h320
    subst k
    rw [keyMomentRowsAt320]
    exact keyMoment320 B hB
  · have he : k = (321 : Fin 2886) := Fin.ext h321
    subst k
    rw [keyMomentRowsAt321]
    exact keyMoment321 B hB
  · have he : k = (322 : Fin 2886) := Fin.ext h322
    subst k
    rw [keyMomentRowsAt322]
    exact keyMoment322 B hB
  · have he : k = (323 : Fin 2886) := Fin.ext h323
    subst k
    rw [keyMomentRowsAt323]
    exact keyMoment323 B hB
  · have he : k = (324 : Fin 2886) := Fin.ext h324
    subst k
    rw [keyMomentRowsAt324]
    exact keyMoment324 B hB
  · have he : k = (325 : Fin 2886) := Fin.ext h325
    subst k
    rw [keyMomentRowsAt325]
    exact keyMoment325 B hB
  · have he : k = (326 : Fin 2886) := Fin.ext h326
    subst k
    rw [keyMomentRowsAt326]
    exact keyMoment326 B hB
  · have he : k = (327 : Fin 2886) := Fin.ext h327
    subst k
    rw [keyMomentRowsAt327]
    exact keyMoment327 B hB
  · have he : k = (328 : Fin 2886) := Fin.ext h328
    subst k
    rw [keyMomentRowsAt328]
    exact keyMoment328 B hB
  · have he : k = (329 : Fin 2886) := Fin.ext h329
    subst k
    rw [keyMomentRowsAt329]
    exact keyMoment329 B hB
  · have he : k = (330 : Fin 2886) := Fin.ext h330
    subst k
    rw [keyMomentRowsAt330]
    exact keyMoment330 B hB
  · have he : k = (331 : Fin 2886) := Fin.ext h331
    subst k
    rw [keyMomentRowsAt331]
    exact keyMoment331 B hB
  · have he : k = (332 : Fin 2886) := Fin.ext h332
    subst k
    rw [keyMomentRowsAt332]
    exact keyMoment332 B hB
  · have he : k = (333 : Fin 2886) := Fin.ext h333
    subst k
    rw [keyMomentRowsAt333]
    exact keyMoment333 B hB
  · have he : k = (334 : Fin 2886) := Fin.ext h334
    subst k
    rw [keyMomentRowsAt334]
    exact keyMoment334 B hB
  · have he : k = (335 : Fin 2886) := Fin.ext h335
    subst k
    rw [keyMomentRowsAt335]
    exact keyMoment335 B hB
  · have he : k = (336 : Fin 2886) := Fin.ext h336
    subst k
    rw [keyMomentRowsAt336]
    exact keyMoment336 B hB
  · have he : k = (337 : Fin 2886) := Fin.ext h337
    subst k
    rw [keyMomentRowsAt337]
    exact keyMoment337 B hB
  · have he : k = (338 : Fin 2886) := Fin.ext h338
    subst k
    rw [keyMomentRowsAt338]
    exact keyMoment338 B hB
  · have he : k = (339 : Fin 2886) := Fin.ext h339
    subst k
    rw [keyMomentRowsAt339]
    exact keyMoment339 B hB
  · have he : k = (340 : Fin 2886) := Fin.ext h340
    subst k
    rw [keyMomentRowsAt340]
    exact keyMoment340 B hB
  · have he : k = (341 : Fin 2886) := Fin.ext h341
    subst k
    rw [keyMomentRowsAt341]
    exact keyMoment341 B hB
  · have he : k = (342 : Fin 2886) := Fin.ext h342
    subst k
    rw [keyMomentRowsAt342]
    exact keyMoment342 B hB
  · have he : k = (343 : Fin 2886) := Fin.ext h343
    subst k
    rw [keyMomentRowsAt343]
    exact keyMoment343 B hB
  · have he : k = (344 : Fin 2886) := Fin.ext h344
    subst k
    rw [keyMomentRowsAt344]
    exact keyMoment344 B hB
  · have he : k = (345 : Fin 2886) := Fin.ext h345
    subst k
    rw [keyMomentRowsAt345]
    exact keyMoment345 B hB
  · have he : k = (346 : Fin 2886) := Fin.ext h346
    subst k
    rw [keyMomentRowsAt346]
    exact keyMoment346 B hB
  · have he : k = (347 : Fin 2886) := Fin.ext h347
    subst k
    rw [keyMomentRowsAt347]
    exact keyMoment347 B hB
  · have he : k = (348 : Fin 2886) := Fin.ext h348
    subst k
    rw [keyMomentRowsAt348]
    exact keyMoment348 B hB
  · have he : k = (349 : Fin 2886) := Fin.ext h349
    subst k
    rw [keyMomentRowsAt349]
    exact keyMoment349 B hB
  · have he : k = (350 : Fin 2886) := Fin.ext h350
    subst k
    rw [keyMomentRowsAt350]
    exact keyMoment350 B hB
  · have he : k = (351 : Fin 2886) := Fin.ext h351
    subst k
    rw [keyMomentRowsAt351]
    exact keyMoment351 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound10_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound10_e_oai
