-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound13_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:46:16.926337+00:00
-- url     : https://prove2.me/submissions/72a04199-b078-4cad-94a6-c14fcb843b51

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E111
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical311
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39864 raw39864Labels = mixedMoment B node130 node130Labels := by
  calc
    mixedMoment B raw39864 raw39864Labels = mixedMoment B raw39864step0 raw39864step0Labels := by
      have hz : ∀ j, raw39864 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39864step0 = (fun i j => raw39864 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39864step0 raw39864; decide +kernel
      have hl : raw39864step0Labels = raw39864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39864 raw39864Labels permutation434 hz
    mixedMoment B raw39864step0 raw39864step0Labels = mixedMoment B raw39864step1 raw39864step1Labels := by
      have ha : raw39864step1 = (fun i j => raw39864step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39864step1 raw39864step0; decide +kernel
      have hl : raw39864step1Labels = raw39864step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39864step0 raw39864step0Labels permutation144 permutation6
    _ = mixedMoment B node130 node130Labels := by rfl

theorem canonical39865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39865 raw39865Labels = mixedMoment B node296 node296Labels := by
  calc
    mixedMoment B raw39865 raw39865Labels = mixedMoment B raw39865step0 raw39865step0Labels := by
      have ha : raw39865step0 = (fun i j => raw39865 (permutation479 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39865step0 raw39865; decide +kernel
      have hl : raw39865step0Labels = raw39865Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39865 raw39865Labels permutation479 permutation6
    _ = mixedMoment B node296 node296Labels := by rfl

theorem canonical39866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39866 raw39866Labels = mixedMoment B node300 node300Labels := by
  calc
    mixedMoment B raw39866 raw39866Labels = mixedMoment B raw39866step0 raw39866step0Labels := by
      have ha : raw39866step0 = (fun i j => raw39866 (permutation479 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39866step0 raw39866; decide +kernel
      have hl : raw39866step0Labels = raw39866Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39866 raw39866Labels permutation479 permutation6
    _ = mixedMoment B node300 node300Labels := by rfl

theorem canonical39867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39867 raw39867Labels = mixedMoment B node103 node103Labels := by
  calc
    mixedMoment B raw39867 raw39867Labels = mixedMoment B raw39867step0 raw39867step0Labels := by
      have hz : ∀ j, raw39867 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39867step0 = (fun i j => raw39867 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39867step0 raw39867; decide +kernel
      have hl : raw39867step0Labels = raw39867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39867 raw39867Labels permutation434 hz
    mixedMoment B raw39867step0 raw39867step0Labels = mixedMoment B raw39867step1 raw39867step1Labels := by
      have hz : ∀ j, raw39867step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39867step1 = (fun i j => raw39867step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39867step1 raw39867step0; decide +kernel
      have hl : raw39867step1Labels = raw39867step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39867step0 raw39867step0Labels permutation80 hz
    mixedMoment B raw39867step1 raw39867step1Labels = mixedMoment B raw39867step2 raw39867step2Labels := by
      have ha : raw39867step2 = (fun i j => raw39867step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39867step2 raw39867step1; decide +kernel
      have hl : raw39867step2Labels = raw39867step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39867step1 raw39867step1Labels permutation24 permutation6
    _ = mixedMoment B node103 node103Labels := by rfl

theorem canonical39868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39868 raw39868Labels = mixedMoment B node149 node149Labels := by
  calc
    mixedMoment B raw39868 raw39868Labels = mixedMoment B raw39868step0 raw39868step0Labels := by
      have hz : ∀ j, raw39868 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39868step0 = (fun i j => raw39868 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39868step0 raw39868; decide +kernel
      have hl : raw39868step0Labels = raw39868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39868 raw39868Labels permutation434 hz
    mixedMoment B raw39868step0 raw39868step0Labels = mixedMoment B raw39868step1 raw39868step1Labels := by
      have hz : ∀ j, raw39868step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39868step1 = (fun i j => raw39868step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39868step1 raw39868step0; decide +kernel
      have hl : raw39868step1Labels = raw39868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39868step0 raw39868step0Labels permutation80 hz
    mixedMoment B raw39868step1 raw39868step1Labels = mixedMoment B raw39868step2 raw39868step2Labels := by
      have ha : raw39868step2 = (fun i j => raw39868step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39868step2 raw39868step1; decide +kernel
      have hl : raw39868step2Labels = raw39868step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39868step1 raw39868step1Labels permutation31 permutation7
    _ = mixedMoment B node149 node149Labels := by rfl

theorem canonical39869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39869 raw39869Labels = mixedMoment B node36 node36Labels := by
  calc
    mixedMoment B raw39869 raw39869Labels = mixedMoment B raw39869step0 raw39869step0Labels := by
      have hz : ∀ j, raw39869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39869step0 = (fun i j => raw39869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39869step0 raw39869; decide +kernel
      have hl : raw39869step0Labels = raw39869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39869 raw39869Labels permutation434 hz
    mixedMoment B raw39869step0 raw39869step0Labels = mixedMoment B raw39869step1 raw39869step1Labels := by
      have hz : ∀ j, raw39869step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39869step1 = (fun i j => raw39869step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39869step1 raw39869step0; decide +kernel
      have hl : raw39869step1Labels = raw39869step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39869step0 raw39869step0Labels permutation80 hz
    mixedMoment B raw39869step1 raw39869step1Labels = mixedMoment B raw39869step2 raw39869step2Labels := by
      have ha : raw39869step2 = (fun i j => raw39869step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39869step2 raw39869step1; decide +kernel
      have hl : raw39869step2Labels = raw39869step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39869step1 raw39869step1Labels permutation30 permutation6
    _ = mixedMoment B node36 node36Labels := by rfl

theorem canonical39870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39870 raw39870Labels = mixedMoment B node15 node15Labels := by
  calc
    mixedMoment B raw39870 raw39870Labels = mixedMoment B raw39870step0 raw39870step0Labels := by
      have hz : ∀ j, raw39870 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39870step0 = (fun i j => raw39870 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39870step0 raw39870; decide +kernel
      have hl : raw39870step0Labels = raw39870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39870 raw39870Labels permutation346 hz
    mixedMoment B raw39870step0 raw39870step0Labels = mixedMoment B raw39870step1 raw39870step1Labels := by
      have ha : raw39870step1 = (fun i j => raw39870step0 (permutation150 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39870step1 raw39870step0; decide +kernel
      have hl : raw39870step1Labels = raw39870step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39870step0 raw39870step0Labels permutation150 permutation6
    _ = mixedMoment B node15 node15Labels := by rfl

theorem canonical39871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39871 raw39871Labels = mixedMoment B node168 node168Labels := by
  calc
    mixedMoment B raw39871 raw39871Labels = mixedMoment B raw39871step0 raw39871step0Labels := by
      have hz : ∀ j, raw39871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39871step0 = (fun i j => raw39871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39871step0 raw39871; decide +kernel
      have hl : raw39871step0Labels = raw39871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39871 raw39871Labels permutation434 hz
    mixedMoment B raw39871step0 raw39871step0Labels = mixedMoment B raw39871step1 raw39871step1Labels := by
      have ha : raw39871step1 = (fun i j => raw39871step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39871step1 raw39871step0; decide +kernel
      have hl : raw39871step1Labels = raw39871step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39871step0 raw39871step0Labels permutation102 permutation6
    _ = mixedMoment B node168 node168Labels := by rfl

theorem canonical39872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39872 raw39872Labels = mixedMoment B node278 node278Labels := by
  calc
    mixedMoment B raw39872 raw39872Labels = mixedMoment B raw39872step0 raw39872step0Labels := by
      have ha : raw39872step0 = (fun i j => raw39872 (permutation280 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39872step0 raw39872; decide +kernel
      have hl : raw39872step0Labels = raw39872Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39872 raw39872Labels permutation280 permutation6
    mixedMoment B raw39872step0 raw39872step0Labels = mixedMoment B raw39872step1 raw39872step1Labels := by
      have ha : raw39872step1 = -raw39872step0 := by apply Matrix.ext; change ∀ i j, raw39872step1 i j = -(raw39872step0 i j); unfold raw39872step1 raw39872step0; decide +kernel
      have hl : raw39872step1Labels = raw39872step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node278 node278Labels := by rfl

theorem canonical39873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39873 raw39873Labels = mixedMoment B node279 node279Labels := by
  calc
    mixedMoment B raw39873 raw39873Labels = mixedMoment B raw39873step0 raw39873step0Labels := by
      have hz : ∀ j, raw39873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39873step0 = (fun i j => raw39873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39873step0 raw39873; decide +kernel
      have hl : raw39873step0Labels = raw39873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39873 raw39873Labels permutation434 hz
    mixedMoment B raw39873step0 raw39873step0Labels = mixedMoment B raw39873step1 raw39873step1Labels := by
      have ha : raw39873step1 = (fun i j => raw39873step0 (permutation58 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39873step1 raw39873step0; decide +kernel
      have hl : raw39873step1Labels = raw39873step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39873step0 raw39873step0Labels permutation58 permutation6
    mixedMoment B raw39873step1 raw39873step1Labels = mixedMoment B raw39873step2 raw39873step2Labels := by
      have ha : raw39873step2 = -raw39873step1 := by apply Matrix.ext; change ∀ i j, raw39873step2 i j = -(raw39873step1 i j); unfold raw39873step2 raw39873step1; decide +kernel
      have hl : raw39873step2Labels = raw39873step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node279 node279Labels := by rfl

theorem canonical39874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39874 raw39874Labels = mixedMoment B node116 node116Labels := by
  calc
    mixedMoment B raw39874 raw39874Labels = mixedMoment B raw39874step0 raw39874step0Labels := by
      have hz : ∀ j, raw39874 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39874step0 = (fun i j => raw39874 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39874step0 raw39874; decide +kernel
      have hl : raw39874step0Labels = raw39874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39874 raw39874Labels permutation434 hz
    mixedMoment B raw39874step0 raw39874step0Labels = mixedMoment B raw39874step1 raw39874step1Labels := by
      have ha : raw39874step1 = (fun i j => raw39874step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39874step1 raw39874step0; decide +kernel
      have hl : raw39874step1Labels = raw39874step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39874step0 raw39874step0Labels permutation144 permutation6
    _ = mixedMoment B node116 node116Labels := by rfl

theorem canonical39875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39875 raw39875Labels = mixedMoment B node17 node17Labels := by
  calc
    mixedMoment B raw39875 raw39875Labels = mixedMoment B raw39875step0 raw39875step0Labels := by
      have hz : ∀ j, raw39875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39875step0 = (fun i j => raw39875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39875step0 raw39875; decide +kernel
      have hl : raw39875step0Labels = raw39875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39875 raw39875Labels permutation434 hz
    mixedMoment B raw39875step0 raw39875step0Labels = mixedMoment B raw39875step1 raw39875step1Labels := by
      have hz : ∀ j, raw39875step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39875step1 = (fun i j => raw39875step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39875step1 raw39875step0; decide +kernel
      have hl : raw39875step1Labels = raw39875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39875step0 raw39875step0Labels permutation80 hz
    mixedMoment B raw39875step1 raw39875step1Labels = mixedMoment B raw39875step2 raw39875step2Labels := by
      have ha : raw39875step2 = (fun i j => raw39875step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39875step2 raw39875step1; decide +kernel
      have hl : raw39875step2Labels = raw39875step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39875step1 raw39875step1Labels permutation30 permutation6
    _ = mixedMoment B node17 node17Labels := by rfl

theorem canonical39876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39876 raw39876Labels = mixedMoment B node270 node270Labels := by
  calc
    mixedMoment B raw39876 raw39876Labels = mixedMoment B raw39876step0 raw39876step0Labels := by
      have hz : ∀ j, raw39876 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39876step0 = (fun i j => raw39876 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39876step0 raw39876; decide +kernel
      have hl : raw39876step0Labels = raw39876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39876 raw39876Labels permutation520 hz
    mixedMoment B raw39876step0 raw39876step0Labels = mixedMoment B raw39876step1 raw39876step1Labels := by
      have hz : ∀ j, raw39876step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39876step1 = (fun i j => raw39876step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39876step1 raw39876step0; decide +kernel
      have hl : raw39876step1Labels = raw39876step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39876step0 raw39876step0Labels permutation104 hz
    mixedMoment B raw39876step1 raw39876step1Labels = mixedMoment B raw39876step2 raw39876step2Labels := by
      have hz : ∀ j, raw39876step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39876step2 = (fun i j => raw39876step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39876step2 raw39876step1; decide +kernel
      have hl : raw39876step2Labels = raw39876step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39876step1 raw39876step1Labels permutation20 hz
    mixedMoment B raw39876step2 raw39876step2Labels = mixedMoment B raw39876step3 raw39876step3Labels := by
      have ha : raw39876step3 = (fun i j => raw39876step2 (permutation4 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39876step3 raw39876step2; decide +kernel
      have hl : raw39876step3Labels = raw39876step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39876step2 raw39876step2Labels permutation4 permutation4
    mixedMoment B raw39876step3 raw39876step3Labels = mixedMoment B raw39876step4 raw39876step4Labels := by
      have ha : raw39876step4 = -raw39876step3 := by apply Matrix.ext; change ∀ i j, raw39876step4 i j = -(raw39876step3 i j); unfold raw39876step4 raw39876step3; decide +kernel
      have hl : raw39876step4Labels = raw39876step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node270 node270Labels := by rfl

theorem canonical39877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39877 raw39877Labels = mixedMoment B node269 node269Labels := by
  calc
    mixedMoment B raw39877 raw39877Labels = mixedMoment B raw39877step0 raw39877step0Labels := by
      have hz : ∀ j, raw39877 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39877step0 = (fun i j => raw39877 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39877step0 raw39877; decide +kernel
      have hl : raw39877step0Labels = raw39877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39877 raw39877Labels permutation434 hz
    mixedMoment B raw39877step0 raw39877step0Labels = mixedMoment B raw39877step1 raw39877step1Labels := by
      have hz : ∀ j, raw39877step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39877step1 = (fun i j => raw39877step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39877step1 raw39877step0; decide +kernel
      have hl : raw39877step1Labels = raw39877step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39877step0 raw39877step0Labels permutation80 hz
    mixedMoment B raw39877step1 raw39877step1Labels = mixedMoment B raw39877step2 raw39877step2Labels := by
      have ha : raw39877step2 = (fun i j => raw39877step1 (permutation14 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39877step2 raw39877step1; decide +kernel
      have hl : raw39877step2Labels = raw39877step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39877step1 raw39877step1Labels permutation14 permutation4
    mixedMoment B raw39877step2 raw39877step2Labels = mixedMoment B raw39877step3 raw39877step3Labels := by
      have ha : raw39877step3 = -raw39877step2 := by apply Matrix.ext; change ∀ i j, raw39877step3 i j = -(raw39877step2 i j); unfold raw39877step3 raw39877step2; decide +kernel
      have hl : raw39877step3Labels = raw39877step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node269 node269Labels := by rfl

theorem canonical39878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39878 raw39878Labels = mixedMoment B node251 node251Labels := by
  calc
    mixedMoment B raw39878 raw39878Labels = mixedMoment B raw39878step0 raw39878step0Labels := by
      have hz : ∀ j, raw39878 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39878step0 = (fun i j => raw39878 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39878step0 raw39878; decide +kernel
      have hl : raw39878step0Labels = raw39878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39878 raw39878Labels permutation434 hz
    mixedMoment B raw39878step0 raw39878step0Labels = mixedMoment B raw39878step1 raw39878step1Labels := by
      have hz : ∀ j, raw39878step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39878step1 = (fun i j => raw39878step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39878step1 raw39878step0; decide +kernel
      have hl : raw39878step1Labels = raw39878step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39878step0 raw39878step0Labels permutation80 hz
    mixedMoment B raw39878step1 raw39878step1Labels = mixedMoment B raw39878step2 raw39878step2Labels := by
      have ha : raw39878step2 = (fun i j => raw39878step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39878step2 raw39878step1; decide +kernel
      have hl : raw39878step2Labels = raw39878step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39878step1 raw39878step1Labels permutation18 permutation6
    _ = mixedMoment B node251 node251Labels := by rfl

theorem canonical39879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39879 raw39879Labels = mixedMoment B node185 node185Labels := by
  calc
    mixedMoment B raw39879 raw39879Labels = mixedMoment B raw39879step0 raw39879step0Labels := by
      have hz : ∀ j, raw39879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39879step0 = (fun i j => raw39879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39879step0 raw39879; decide +kernel
      have hl : raw39879step0Labels = raw39879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39879 raw39879Labels permutation434 hz
    mixedMoment B raw39879step0 raw39879step0Labels = mixedMoment B raw39879step1 raw39879step1Labels := by
      have hz : ∀ j, raw39879step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39879step1 = (fun i j => raw39879step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39879step1 raw39879step0; decide +kernel
      have hl : raw39879step1Labels = raw39879step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39879step0 raw39879step0Labels permutation80 hz
    mixedMoment B raw39879step1 raw39879step1Labels = mixedMoment B raw39879step2 raw39879step2Labels := by
      have ha : raw39879step2 = (fun i j => raw39879step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39879step2 raw39879step1; decide +kernel
      have hl : raw39879step2Labels = raw39879step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39879step1 raw39879step1Labels permutation18 permutation6
    _ = mixedMoment B node185 node185Labels := by rfl

theorem canonical39880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39880 raw39880Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw39880 raw39880Labels = mixedMoment B raw39880step0 raw39880step0Labels := by
      have hz : ∀ j, raw39880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39880step0 = (fun i j => raw39880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39880step0 raw39880; decide +kernel
      have hl : raw39880step0Labels = raw39880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39880 raw39880Labels permutation434 hz
    mixedMoment B raw39880step0 raw39880step0Labels = mixedMoment B raw39880step1 raw39880step1Labels := by
      have hz : ∀ j, raw39880step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39880step1 = (fun i j => raw39880step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39880step1 raw39880step0; decide +kernel
      have hl : raw39880step1Labels = raw39880step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39880step0 raw39880step0Labels permutation80 hz
    mixedMoment B raw39880step1 raw39880step1Labels = mixedMoment B raw39880step2 raw39880step2Labels := by
      have ha : raw39880step2 = (fun i j => raw39880step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39880step2 raw39880step1; decide +kernel
      have hl : raw39880step2Labels = raw39880step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39880step1 raw39880step1Labels permutation17 permutation6
    _ = mixedMoment B node268 node268Labels := by rfl

theorem canonical39881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39881 raw39881Labels = mixedMoment B node248 node248Labels := by
  calc
    mixedMoment B raw39881 raw39881Labels = mixedMoment B raw39881step0 raw39881step0Labels := by
      have hz : ∀ j, raw39881 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39881step0 = (fun i j => raw39881 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39881step0 raw39881; decide +kernel
      have hl : raw39881step0Labels = raw39881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39881 raw39881Labels permutation346 hz
    mixedMoment B raw39881step0 raw39881step0Labels = mixedMoment B raw39881step1 raw39881step1Labels := by
      have ha : raw39881step1 = (fun i j => raw39881step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39881step1 raw39881step0; decide +kernel
      have hl : raw39881step1Labels = raw39881step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39881step0 raw39881step0Labels permutation77 permutation6
    _ = mixedMoment B node248 node248Labels := by rfl

theorem canonical39882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39882 raw39882Labels = mixedMoment B node182 node182Labels := by
  calc
    mixedMoment B raw39882 raw39882Labels = mixedMoment B raw39882step0 raw39882step0Labels := by
      have hz : ∀ j, raw39882 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39882step0 = (fun i j => raw39882 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39882step0 raw39882; decide +kernel
      have hl : raw39882step0Labels = raw39882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39882 raw39882Labels permutation346 hz
    mixedMoment B raw39882step0 raw39882step0Labels = mixedMoment B raw39882step1 raw39882step1Labels := by
      have ha : raw39882step1 = (fun i j => raw39882step0 (permutation76 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39882step1 raw39882step0; decide +kernel
      have hl : raw39882step1Labels = raw39882step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39882step0 raw39882step0Labels permutation76 permutation6
    _ = mixedMoment B node182 node182Labels := by rfl

theorem canonical39883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39883 raw39883Labels = mixedMoment B node235 node235Labels := by
  calc
    mixedMoment B raw39883 raw39883Labels = mixedMoment B raw39883step0 raw39883step0Labels := by
      have hz : ∀ j, raw39883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39883step0 = (fun i j => raw39883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39883step0 raw39883; decide +kernel
      have hl : raw39883step0Labels = raw39883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39883 raw39883Labels permutation346 hz
    mixedMoment B raw39883step0 raw39883step0Labels = mixedMoment B raw39883step1 raw39883step1Labels := by
      have ha : raw39883step1 = (fun i j => raw39883step0 (permutation71 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39883step1 raw39883step0; decide +kernel
      have hl : raw39883step1Labels = raw39883step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39883step0 raw39883step0Labels permutation71 permutation6
    _ = mixedMoment B node235 node235Labels := by rfl

theorem canonical39884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39884 raw39884Labels = mixedMoment B node261 node261Labels := by
  calc
    mixedMoment B raw39884 raw39884Labels = mixedMoment B raw39884step0 raw39884step0Labels := by
      have hz : ∀ j, raw39884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39884step0 = (fun i j => raw39884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39884step0 raw39884; decide +kernel
      have hl : raw39884step0Labels = raw39884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39884 raw39884Labels permutation346 hz
    mixedMoment B raw39884step0 raw39884step0Labels = mixedMoment B raw39884step1 raw39884step1Labels := by
      have ha : raw39884step1 = (fun i j => raw39884step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39884step1 raw39884step0; decide +kernel
      have hl : raw39884step1Labels = raw39884step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39884step0 raw39884step0Labels permutation73 permutation6
    _ = mixedMoment B node261 node261Labels := by rfl

theorem canonical39885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39885 raw39885Labels = mixedMoment B node173 node173Labels := by
  calc
    mixedMoment B raw39885 raw39885Labels = mixedMoment B raw39885step0 raw39885step0Labels := by
      have hz : ∀ j, raw39885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39885step0 = (fun i j => raw39885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39885step0 raw39885; decide +kernel
      have hl : raw39885step0Labels = raw39885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39885 raw39885Labels permutation346 hz
    mixedMoment B raw39885step0 raw39885step0Labels = mixedMoment B raw39885step1 raw39885step1Labels := by
      have ha : raw39885step1 = (fun i j => raw39885step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39885step1 raw39885step0; decide +kernel
      have hl : raw39885step1Labels = raw39885step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39885step0 raw39885step0Labels permutation83 permutation6
    mixedMoment B raw39885step1 raw39885step1Labels = mixedMoment B raw39885step2 raw39885step2Labels := by
      have ha : raw39885step2 = -raw39885step1 := by apply Matrix.ext; change ∀ i j, raw39885step2 i j = -(raw39885step1 i j); unfold raw39885step2 raw39885step1; decide +kernel
      have hl : raw39885step2Labels = raw39885step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node173 node173Labels := by rfl

theorem canonical39886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39886 raw39886Labels = mixedMoment B node179 node179Labels := by
  calc
    mixedMoment B raw39886 raw39886Labels = mixedMoment B raw39886step0 raw39886step0Labels := by
      have ha : raw39886step0 = (fun i j => raw39886 (permutation340 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39886step0 raw39886; decide +kernel
      have hl : raw39886step0Labels = raw39886Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39886 raw39886Labels permutation340 permutation6
    _ = mixedMoment B node179 node179Labels := by rfl

theorem canonical39887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39887 raw39887Labels = mixedMoment B node223 node223Labels := by
  calc
    mixedMoment B raw39887 raw39887Labels = mixedMoment B raw39887step0 raw39887step0Labels := by
      have ha : raw39887step0 = (fun i j => raw39887 (permutation332 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39887step0 raw39887; decide +kernel
      have hl : raw39887step0Labels = raw39887Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39887 raw39887Labels permutation332 permutation6
    _ = mixedMoment B node223 node223Labels := by rfl

theorem canonical39888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39888 raw39888Labels = mixedMoment B node209 node209Labels := by
  calc
    mixedMoment B raw39888 raw39888Labels = mixedMoment B raw39888step0 raw39888step0Labels := by
      have ha : raw39888step0 = (fun i j => raw39888 (permutation331 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39888step0 raw39888; decide +kernel
      have hl : raw39888step0Labels = raw39888Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39888 raw39888Labels permutation331 permutation6
    _ = mixedMoment B node209 node209Labels := by rfl

theorem canonical39889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39889 raw39889Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw39889 raw39889Labels = mixedMoment B raw39889step0 raw39889step0Labels := by
      have hz : ∀ j, raw39889 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39889step0 = (fun i j => raw39889 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39889step0 raw39889; decide +kernel
      have hl : raw39889step0Labels = raw39889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39889 raw39889Labels permutation520 hz
    mixedMoment B raw39889step0 raw39889step0Labels = mixedMoment B raw39889step1 raw39889step1Labels := by
      have hz : ∀ j, raw39889step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39889step1 = (fun i j => raw39889step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39889step1 raw39889step0; decide +kernel
      have hl : raw39889step1Labels = raw39889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39889step0 raw39889step0Labels permutation104 hz
    mixedMoment B raw39889step1 raw39889step1Labels = mixedMoment B raw39889step2 raw39889step2Labels := by
      have ha : raw39889step2 = (fun i j => raw39889step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39889step2 raw39889step1; decide +kernel
      have hl : raw39889step2Labels = raw39889step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39889step1 raw39889step1Labels permutation27 permutation5
    _ = mixedMoment B node412 node412Labels := by rfl

theorem canonical39890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39890 raw39890Labels = mixedMoment B node468 node468Labels := by
  calc
    mixedMoment B raw39890 raw39890Labels = mixedMoment B raw39890step0 raw39890step0Labels := by
      have hz : ∀ j, raw39890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39890step0 = (fun i j => raw39890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39890step0 raw39890; decide +kernel
      have hl : raw39890step0Labels = raw39890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39890 raw39890Labels permutation434 hz
    mixedMoment B raw39890step0 raw39890step0Labels = mixedMoment B raw39890step1 raw39890step1Labels := by
      have ha : raw39890step1 = (fun i j => raw39890step0 (permutation62 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39890step1 raw39890step0; decide +kernel
      have hl : raw39890step1Labels = raw39890step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39890step0 raw39890step0Labels permutation62 permutation4
    mixedMoment B raw39890step1 raw39890step1Labels = mixedMoment B raw39890step2 raw39890step2Labels := by
      have ha : raw39890step2 = -raw39890step1 := by apply Matrix.ext; change ∀ i j, raw39890step2 i j = -(raw39890step1 i j); unfold raw39890step2 raw39890step1; decide +kernel
      have hl : raw39890step2Labels = raw39890step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node468 node468Labels := by rfl

theorem canonical39891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39891 raw39891Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw39891 raw39891Labels = mixedMoment B raw39891step0 raw39891step0Labels := by
      have hz : ∀ j, raw39891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39891step0 = (fun i j => raw39891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39891step0 raw39891; decide +kernel
      have hl : raw39891step0Labels = raw39891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39891 raw39891Labels permutation434 hz
    mixedMoment B raw39891step0 raw39891step0Labels = mixedMoment B raw39891step1 raw39891step1Labels := by
      have ha : raw39891step1 = (fun i j => raw39891step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39891step1 raw39891step0; decide +kernel
      have hl : raw39891step1Labels = raw39891step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39891step0 raw39891step0Labels permutation65 permutation6
    _ = mixedMoment B node467 node467Labels := by rfl

theorem canonical39892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39892 raw39892Labels = mixedMoment B node439 node439Labels := by
  calc
    mixedMoment B raw39892 raw39892Labels = mixedMoment B raw39892step0 raw39892step0Labels := by
      have ha : raw39892step0 = (fun i j => raw39892 (permutation339 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39892step0 raw39892; decide +kernel
      have hl : raw39892step0Labels = raw39892Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39892 raw39892Labels permutation339 permutation6
    _ = mixedMoment B node439 node439Labels := by rfl

theorem canonical39893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39893 raw39893Labels = mixedMoment B node455 node455Labels := by
  calc
    mixedMoment B raw39893 raw39893Labels = mixedMoment B raw39893step0 raw39893step0Labels := by
      have ha : raw39893step0 = (fun i j => raw39893 (permutation301 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39893step0 raw39893; decide +kernel
      have hl : raw39893step0Labels = raw39893Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39893 raw39893Labels permutation301 permutation6
    _ = mixedMoment B node455 node455Labels := by rfl

theorem canonical39894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39894 raw39894Labels = mixedMoment B node171 node171Labels := by
  calc
    mixedMoment B raw39894 raw39894Labels = mixedMoment B raw39894step0 raw39894step0Labels := by
      have ha : raw39894step0 = (fun i j => raw39894 (permutation447 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39894step0 raw39894; decide +kernel
      have hl : raw39894step0Labels = raw39894Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39894 raw39894Labels permutation447 permutation6
    mixedMoment B raw39894step0 raw39894step0Labels = mixedMoment B raw39894step1 raw39894step1Labels := by
      have ha : raw39894step1 = -raw39894step0 := by apply Matrix.ext; change ∀ i j, raw39894step1 i j = -(raw39894step0 i j); unfold raw39894step1 raw39894step0; decide +kernel
      have hl : raw39894step1Labels = raw39894step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node171 node171Labels := by rfl

theorem canonical39895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39895 raw39895Labels = mixedMoment B node507 node507Labels := by
  calc
    mixedMoment B raw39895 raw39895Labels = mixedMoment B raw39895step0 raw39895step0Labels := by
      have hz : ∀ j, raw39895 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39895step0 = (fun i j => raw39895 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39895step0 raw39895; decide +kernel
      have hl : raw39895step0Labels = raw39895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39895 raw39895Labels permutation520 hz
    mixedMoment B raw39895step0 raw39895step0Labels = mixedMoment B raw39895step1 raw39895step1Labels := by
      have hz : ∀ j, raw39895step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39895step1 = (fun i j => raw39895step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39895step1 raw39895step0; decide +kernel
      have hl : raw39895step1Labels = raw39895step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39895step0 raw39895step0Labels permutation104 hz
    mixedMoment B raw39895step1 raw39895step1Labels = mixedMoment B raw39895step2 raw39895step2Labels := by
      have hz : ∀ j, raw39895step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39895step2 = (fun i j => raw39895step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39895step2 raw39895step1; decide +kernel
      have hl : raw39895step2Labels = raw39895step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39895step1 raw39895step1Labels permutation20 hz
    _ = mixedMoment B node507 node507Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 416) =
      Integer.Sparse.eval keyMomentRow416 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 416).leftCharge (GramAssembly.key 416).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 130) := by
    have ha : gramCharges (GramAssembly.key 416).leftCharge (GramAssembly.key 416).rightCharge = raw39864 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39864Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39864 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 416).leftCharge (GramAssembly.key 416).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow416, Integer.Sparse.eval]

theorem keyMoment417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 417) =
      Integer.Sparse.eval keyMomentRow417 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 417).leftCharge (GramAssembly.key 417).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 296) := by
    have ha : gramCharges (GramAssembly.key 417).leftCharge (GramAssembly.key 417).rightCharge = raw39865 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39865Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39865 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 417).leftCharge (GramAssembly.key 417).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow417, Integer.Sparse.eval]

theorem keyMoment418 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 418) =
      Integer.Sparse.eval keyMomentRow418 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 418).leftCharge (GramAssembly.key 418).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 300) := by
    have ha : gramCharges (GramAssembly.key 418).leftCharge (GramAssembly.key 418).rightCharge = raw39866 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39866Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39866 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 418).leftCharge (GramAssembly.key 418).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow418, Integer.Sparse.eval]

theorem keyMoment419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 419) =
      Integer.Sparse.eval keyMomentRow419 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 419).leftCharge (GramAssembly.key 419).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 103) := by
    have ha : gramCharges (GramAssembly.key 419).leftCharge (GramAssembly.key 419).rightCharge = raw39867 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39867Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39867 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 419).leftCharge (GramAssembly.key 419).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow419, Integer.Sparse.eval]

theorem keyMoment420 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 420) =
      Integer.Sparse.eval keyMomentRow420 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 420).leftCharge (GramAssembly.key 420).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 149) := by
    have ha : gramCharges (GramAssembly.key 420).leftCharge (GramAssembly.key 420).rightCharge = raw39868 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39868Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39868 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 420).leftCharge (GramAssembly.key 420).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow420, Integer.Sparse.eval]

theorem keyMoment421 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 421) =
      Integer.Sparse.eval keyMomentRow421 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 421).leftCharge (GramAssembly.key 421).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 36) := by
    have ha : gramCharges (GramAssembly.key 421).leftCharge (GramAssembly.key 421).rightCharge = raw39869 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39869Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39869 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 421).leftCharge (GramAssembly.key 421).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow421, Integer.Sparse.eval]

theorem keyMoment422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 422) =
      Integer.Sparse.eval keyMomentRow422 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 422).leftCharge (GramAssembly.key 422).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 15) := by
    have ha : gramCharges (GramAssembly.key 422).leftCharge (GramAssembly.key 422).rightCharge = raw39870 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39870Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39870 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 422).leftCharge (GramAssembly.key 422).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow422, Integer.Sparse.eval]

theorem keyMoment423 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 423) =
      Integer.Sparse.eval keyMomentRow423 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 423).leftCharge (GramAssembly.key 423).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 168) := by
    have ha : gramCharges (GramAssembly.key 423).leftCharge (GramAssembly.key 423).rightCharge = raw39871 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39871Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39871 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 423).leftCharge (GramAssembly.key 423).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow423, Integer.Sparse.eval]

theorem keyMoment424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 424) =
      Integer.Sparse.eval keyMomentRow424 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 424).leftCharge (GramAssembly.key 424).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 278) := by
    have ha : gramCharges (GramAssembly.key 424).leftCharge (GramAssembly.key 424).rightCharge = raw39872 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39872Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39872 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 424).leftCharge (GramAssembly.key 424).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow424, Integer.Sparse.eval]

theorem keyMoment425 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 425) =
      Integer.Sparse.eval keyMomentRow425 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 425).leftCharge (GramAssembly.key 425).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 279) := by
    have ha : gramCharges (GramAssembly.key 425).leftCharge (GramAssembly.key 425).rightCharge = raw39873 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39873Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39873 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 425).leftCharge (GramAssembly.key 425).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow425, Integer.Sparse.eval]

theorem keyMoment426 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 426) =
      Integer.Sparse.eval keyMomentRow426 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 426).leftCharge (GramAssembly.key 426).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 116) := by
    have ha : gramCharges (GramAssembly.key 426).leftCharge (GramAssembly.key 426).rightCharge = raw39874 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39874Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39874 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 426).leftCharge (GramAssembly.key 426).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow426, Integer.Sparse.eval]

theorem keyMoment427 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 427) =
      Integer.Sparse.eval keyMomentRow427 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 427).leftCharge (GramAssembly.key 427).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 17) := by
    have ha : gramCharges (GramAssembly.key 427).leftCharge (GramAssembly.key 427).rightCharge = raw39875 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39875Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39875 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 427).leftCharge (GramAssembly.key 427).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow427, Integer.Sparse.eval]

theorem keyMoment428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 428) =
      Integer.Sparse.eval keyMomentRow428 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 428).leftCharge (GramAssembly.key 428).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 270) := by
    have ha : gramCharges (GramAssembly.key 428).leftCharge (GramAssembly.key 428).rightCharge = raw39876 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39876Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39876 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 428).leftCharge (GramAssembly.key 428).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow428, Integer.Sparse.eval]

theorem keyMoment429 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 429) =
      Integer.Sparse.eval keyMomentRow429 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 429).leftCharge (GramAssembly.key 429).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 269) := by
    have ha : gramCharges (GramAssembly.key 429).leftCharge (GramAssembly.key 429).rightCharge = raw39877 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39877Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39877 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 429).leftCharge (GramAssembly.key 429).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow429, Integer.Sparse.eval]

theorem keyMoment430 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 430) =
      Integer.Sparse.eval keyMomentRow430 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 430).leftCharge (GramAssembly.key 430).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 251) := by
    have ha : gramCharges (GramAssembly.key 430).leftCharge (GramAssembly.key 430).rightCharge = raw39878 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39878Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39878 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 430).leftCharge (GramAssembly.key 430).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow430, Integer.Sparse.eval]

theorem keyMoment431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 431) =
      Integer.Sparse.eval keyMomentRow431 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 431).leftCharge (GramAssembly.key 431).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 185) := by
    have ha : gramCharges (GramAssembly.key 431).leftCharge (GramAssembly.key 431).rightCharge = raw39879 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39879Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39879 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 431).leftCharge (GramAssembly.key 431).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow431, Integer.Sparse.eval]

theorem keyMoment432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 432) =
      Integer.Sparse.eval keyMomentRow432 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 432).leftCharge (GramAssembly.key 432).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 268) := by
    have ha : gramCharges (GramAssembly.key 432).leftCharge (GramAssembly.key 432).rightCharge = raw39880 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39880Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39880 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 432).leftCharge (GramAssembly.key 432).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow432, Integer.Sparse.eval]

theorem keyMoment433 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 433) =
      Integer.Sparse.eval keyMomentRow433 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 433).leftCharge (GramAssembly.key 433).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 248) := by
    have ha : gramCharges (GramAssembly.key 433).leftCharge (GramAssembly.key 433).rightCharge = raw39881 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39881Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39881 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 433).leftCharge (GramAssembly.key 433).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow433, Integer.Sparse.eval]

theorem keyMoment434 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 434) =
      Integer.Sparse.eval keyMomentRow434 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 434).leftCharge (GramAssembly.key 434).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 182) := by
    have ha : gramCharges (GramAssembly.key 434).leftCharge (GramAssembly.key 434).rightCharge = raw39882 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39882Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39882 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 434).leftCharge (GramAssembly.key 434).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow434, Integer.Sparse.eval]

theorem keyMoment435 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 435) =
      Integer.Sparse.eval keyMomentRow435 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 435).leftCharge (GramAssembly.key 435).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 235) := by
    have ha : gramCharges (GramAssembly.key 435).leftCharge (GramAssembly.key 435).rightCharge = raw39883 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39883Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39883 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 435).leftCharge (GramAssembly.key 435).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow435, Integer.Sparse.eval]

theorem keyMoment436 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 436) =
      Integer.Sparse.eval keyMomentRow436 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 436).leftCharge (GramAssembly.key 436).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 261) := by
    have ha : gramCharges (GramAssembly.key 436).leftCharge (GramAssembly.key 436).rightCharge = raw39884 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39884Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39884 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 436).leftCharge (GramAssembly.key 436).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow436, Integer.Sparse.eval]

theorem keyMoment437 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 437) =
      Integer.Sparse.eval keyMomentRow437 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 437).leftCharge (GramAssembly.key 437).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 173) := by
    have ha : gramCharges (GramAssembly.key 437).leftCharge (GramAssembly.key 437).rightCharge = raw39885 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39885Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39885 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 437).leftCharge (GramAssembly.key 437).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow437, Integer.Sparse.eval]

theorem keyMoment438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 438) =
      Integer.Sparse.eval keyMomentRow438 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 438).leftCharge (GramAssembly.key 438).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 179) := by
    have ha : gramCharges (GramAssembly.key 438).leftCharge (GramAssembly.key 438).rightCharge = raw39886 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39886Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39886 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 438).leftCharge (GramAssembly.key 438).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow438, Integer.Sparse.eval]

theorem keyMoment439 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 439) =
      Integer.Sparse.eval keyMomentRow439 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 439).leftCharge (GramAssembly.key 439).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 223) := by
    have ha : gramCharges (GramAssembly.key 439).leftCharge (GramAssembly.key 439).rightCharge = raw39887 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39887Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39887 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 439).leftCharge (GramAssembly.key 439).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow439, Integer.Sparse.eval]

theorem keyMoment440 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 440) =
      Integer.Sparse.eval keyMomentRow440 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 440).leftCharge (GramAssembly.key 440).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 209) := by
    have ha : gramCharges (GramAssembly.key 440).leftCharge (GramAssembly.key 440).rightCharge = raw39888 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39888Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39888 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 440).leftCharge (GramAssembly.key 440).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow440, Integer.Sparse.eval]

theorem keyMoment441 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 441) =
      Integer.Sparse.eval keyMomentRow441 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 441).leftCharge (GramAssembly.key 441).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 412) := by
    have ha : gramCharges (GramAssembly.key 441).leftCharge (GramAssembly.key 441).rightCharge = raw39889 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39889Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39889 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 441).leftCharge (GramAssembly.key 441).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow441, Integer.Sparse.eval]

theorem keyMoment442 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 442) =
      Integer.Sparse.eval keyMomentRow442 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 442).leftCharge (GramAssembly.key 442).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 468) := by
    have ha : gramCharges (GramAssembly.key 442).leftCharge (GramAssembly.key 442).rightCharge = raw39890 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39890Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39890 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 442).leftCharge (GramAssembly.key 442).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow442, Integer.Sparse.eval]

theorem keyMoment443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 443) =
      Integer.Sparse.eval keyMomentRow443 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 443).leftCharge (GramAssembly.key 443).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 467) := by
    have ha : gramCharges (GramAssembly.key 443).leftCharge (GramAssembly.key 443).rightCharge = raw39891 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39891Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39891 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 443).leftCharge (GramAssembly.key 443).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow443, Integer.Sparse.eval]

theorem keyMoment444 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 444) =
      Integer.Sparse.eval keyMomentRow444 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 444).leftCharge (GramAssembly.key 444).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 439) := by
    have ha : gramCharges (GramAssembly.key 444).leftCharge (GramAssembly.key 444).rightCharge = raw39892 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39892Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39892 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 444).leftCharge (GramAssembly.key 444).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow444, Integer.Sparse.eval]

theorem keyMoment445 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 445) =
      Integer.Sparse.eval keyMomentRow445 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 445).leftCharge (GramAssembly.key 445).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 455) := by
    have ha : gramCharges (GramAssembly.key 445).leftCharge (GramAssembly.key 445).rightCharge = raw39893 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39893Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39893 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 445).leftCharge (GramAssembly.key 445).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow445, Integer.Sparse.eval]

theorem keyMoment446 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 446) =
      Integer.Sparse.eval keyMomentRow446 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 446).leftCharge (GramAssembly.key 446).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 171) := by
    have ha : gramCharges (GramAssembly.key 446).leftCharge (GramAssembly.key 446).rightCharge = raw39894 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39894Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39894 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 446).leftCharge (GramAssembly.key 446).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow446, Integer.Sparse.eval]

theorem keyMoment447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 447) =
      Integer.Sparse.eval keyMomentRow447 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 447).leftCharge (GramAssembly.key 447).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 507) := by
    have ha : gramCharges (GramAssembly.key 447).leftCharge (GramAssembly.key 447).rightCharge = raw39895 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39895Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39895 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 447).leftCharge (GramAssembly.key 447).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow447, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt416 : keyMomentRows (416 : Fin 2886) =
    keyMomentRow416 := by decide +kernel

theorem keyMomentRowsAt417 : keyMomentRows (417 : Fin 2886) =
    keyMomentRow417 := by decide +kernel

theorem keyMomentRowsAt418 : keyMomentRows (418 : Fin 2886) =
    keyMomentRow418 := by decide +kernel

theorem keyMomentRowsAt419 : keyMomentRows (419 : Fin 2886) =
    keyMomentRow419 := by decide +kernel

theorem keyMomentRowsAt420 : keyMomentRows (420 : Fin 2886) =
    keyMomentRow420 := by decide +kernel

theorem keyMomentRowsAt421 : keyMomentRows (421 : Fin 2886) =
    keyMomentRow421 := by decide +kernel

theorem keyMomentRowsAt422 : keyMomentRows (422 : Fin 2886) =
    keyMomentRow422 := by decide +kernel

theorem keyMomentRowsAt423 : keyMomentRows (423 : Fin 2886) =
    keyMomentRow423 := by decide +kernel

theorem keyMomentRowsAt424 : keyMomentRows (424 : Fin 2886) =
    keyMomentRow424 := by decide +kernel

theorem keyMomentRowsAt425 : keyMomentRows (425 : Fin 2886) =
    keyMomentRow425 := by decide +kernel

theorem keyMomentRowsAt426 : keyMomentRows (426 : Fin 2886) =
    keyMomentRow426 := by decide +kernel

theorem keyMomentRowsAt427 : keyMomentRows (427 : Fin 2886) =
    keyMomentRow427 := by decide +kernel

theorem keyMomentRowsAt428 : keyMomentRows (428 : Fin 2886) =
    keyMomentRow428 := by decide +kernel

theorem keyMomentRowsAt429 : keyMomentRows (429 : Fin 2886) =
    keyMomentRow429 := by decide +kernel

theorem keyMomentRowsAt430 : keyMomentRows (430 : Fin 2886) =
    keyMomentRow430 := by decide +kernel

theorem keyMomentRowsAt431 : keyMomentRows (431 : Fin 2886) =
    keyMomentRow431 := by decide +kernel

theorem keyMomentRowsAt432 : keyMomentRows (432 : Fin 2886) =
    keyMomentRow432 := by decide +kernel

theorem keyMomentRowsAt433 : keyMomentRows (433 : Fin 2886) =
    keyMomentRow433 := by decide +kernel

theorem keyMomentRowsAt434 : keyMomentRows (434 : Fin 2886) =
    keyMomentRow434 := by decide +kernel

theorem keyMomentRowsAt435 : keyMomentRows (435 : Fin 2886) =
    keyMomentRow435 := by decide +kernel

theorem keyMomentRowsAt436 : keyMomentRows (436 : Fin 2886) =
    keyMomentRow436 := by decide +kernel

theorem keyMomentRowsAt437 : keyMomentRows (437 : Fin 2886) =
    keyMomentRow437 := by decide +kernel

theorem keyMomentRowsAt438 : keyMomentRows (438 : Fin 2886) =
    keyMomentRow438 := by decide +kernel

theorem keyMomentRowsAt439 : keyMomentRows (439 : Fin 2886) =
    keyMomentRow439 := by decide +kernel

theorem keyMomentRowsAt440 : keyMomentRows (440 : Fin 2886) =
    keyMomentRow440 := by decide +kernel

theorem keyMomentRowsAt441 : keyMomentRows (441 : Fin 2886) =
    keyMomentRow441 := by decide +kernel

theorem keyMomentRowsAt442 : keyMomentRows (442 : Fin 2886) =
    keyMomentRow442 := by decide +kernel

theorem keyMomentRowsAt443 : keyMomentRows (443 : Fin 2886) =
    keyMomentRow443 := by decide +kernel

theorem keyMomentRowsAt444 : keyMomentRows (444 : Fin 2886) =
    keyMomentRow444 := by decide +kernel

theorem keyMomentRowsAt445 : keyMomentRows (445 : Fin 2886) =
    keyMomentRow445 := by decide +kernel

theorem keyMomentRowsAt446 : keyMomentRows (446 : Fin 2886) =
    keyMomentRow446 := by decide +kernel

theorem keyMomentRowsAt447 : keyMomentRows (447 : Fin 2886) =
    keyMomentRow447 := by decide +kernel

theorem keyMomentChunkSound13_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 13) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 416 ∨ k.val = 417 ∨ k.val = 418 ∨ k.val = 419 ∨ k.val = 420 ∨ k.val = 421 ∨ k.val = 422 ∨ k.val = 423 ∨ k.val = 424 ∨ k.val = 425 ∨ k.val = 426 ∨ k.val = 427 ∨ k.val = 428 ∨ k.val = 429 ∨ k.val = 430 ∨ k.val = 431 ∨ k.val = 432 ∨ k.val = 433 ∨ k.val = 434 ∨ k.val = 435 ∨ k.val = 436 ∨ k.val = 437 ∨ k.val = 438 ∨ k.val = 439 ∨ k.val = 440 ∨ k.val = 441 ∨ k.val = 442 ∨ k.val = 443 ∨ k.val = 444 ∨ k.val = 445 ∨ k.val = 446 ∨ k.val = 447 := by omega
  rcases heq with h416 | h417 | h418 | h419 | h420 | h421 | h422 | h423 | h424 | h425 | h426 | h427 | h428 | h429 | h430 | h431 | h432 | h433 | h434 | h435 | h436 | h437 | h438 | h439 | h440 | h441 | h442 | h443 | h444 | h445 | h446 | h447
  · have he : k = (416 : Fin 2886) := Fin.ext h416
    subst k
    rw [keyMomentRowsAt416]
    exact keyMoment416 B hB
  · have he : k = (417 : Fin 2886) := Fin.ext h417
    subst k
    rw [keyMomentRowsAt417]
    exact keyMoment417 B hB
  · have he : k = (418 : Fin 2886) := Fin.ext h418
    subst k
    rw [keyMomentRowsAt418]
    exact keyMoment418 B hB
  · have he : k = (419 : Fin 2886) := Fin.ext h419
    subst k
    rw [keyMomentRowsAt419]
    exact keyMoment419 B hB
  · have he : k = (420 : Fin 2886) := Fin.ext h420
    subst k
    rw [keyMomentRowsAt420]
    exact keyMoment420 B hB
  · have he : k = (421 : Fin 2886) := Fin.ext h421
    subst k
    rw [keyMomentRowsAt421]
    exact keyMoment421 B hB
  · have he : k = (422 : Fin 2886) := Fin.ext h422
    subst k
    rw [keyMomentRowsAt422]
    exact keyMoment422 B hB
  · have he : k = (423 : Fin 2886) := Fin.ext h423
    subst k
    rw [keyMomentRowsAt423]
    exact keyMoment423 B hB
  · have he : k = (424 : Fin 2886) := Fin.ext h424
    subst k
    rw [keyMomentRowsAt424]
    exact keyMoment424 B hB
  · have he : k = (425 : Fin 2886) := Fin.ext h425
    subst k
    rw [keyMomentRowsAt425]
    exact keyMoment425 B hB
  · have he : k = (426 : Fin 2886) := Fin.ext h426
    subst k
    rw [keyMomentRowsAt426]
    exact keyMoment426 B hB
  · have he : k = (427 : Fin 2886) := Fin.ext h427
    subst k
    rw [keyMomentRowsAt427]
    exact keyMoment427 B hB
  · have he : k = (428 : Fin 2886) := Fin.ext h428
    subst k
    rw [keyMomentRowsAt428]
    exact keyMoment428 B hB
  · have he : k = (429 : Fin 2886) := Fin.ext h429
    subst k
    rw [keyMomentRowsAt429]
    exact keyMoment429 B hB
  · have he : k = (430 : Fin 2886) := Fin.ext h430
    subst k
    rw [keyMomentRowsAt430]
    exact keyMoment430 B hB
  · have he : k = (431 : Fin 2886) := Fin.ext h431
    subst k
    rw [keyMomentRowsAt431]
    exact keyMoment431 B hB
  · have he : k = (432 : Fin 2886) := Fin.ext h432
    subst k
    rw [keyMomentRowsAt432]
    exact keyMoment432 B hB
  · have he : k = (433 : Fin 2886) := Fin.ext h433
    subst k
    rw [keyMomentRowsAt433]
    exact keyMoment433 B hB
  · have he : k = (434 : Fin 2886) := Fin.ext h434
    subst k
    rw [keyMomentRowsAt434]
    exact keyMoment434 B hB
  · have he : k = (435 : Fin 2886) := Fin.ext h435
    subst k
    rw [keyMomentRowsAt435]
    exact keyMoment435 B hB
  · have he : k = (436 : Fin 2886) := Fin.ext h436
    subst k
    rw [keyMomentRowsAt436]
    exact keyMoment436 B hB
  · have he : k = (437 : Fin 2886) := Fin.ext h437
    subst k
    rw [keyMomentRowsAt437]
    exact keyMoment437 B hB
  · have he : k = (438 : Fin 2886) := Fin.ext h438
    subst k
    rw [keyMomentRowsAt438]
    exact keyMoment438 B hB
  · have he : k = (439 : Fin 2886) := Fin.ext h439
    subst k
    rw [keyMomentRowsAt439]
    exact keyMoment439 B hB
  · have he : k = (440 : Fin 2886) := Fin.ext h440
    subst k
    rw [keyMomentRowsAt440]
    exact keyMoment440 B hB
  · have he : k = (441 : Fin 2886) := Fin.ext h441
    subst k
    rw [keyMomentRowsAt441]
    exact keyMoment441 B hB
  · have he : k = (442 : Fin 2886) := Fin.ext h442
    subst k
    rw [keyMomentRowsAt442]
    exact keyMoment442 B hB
  · have he : k = (443 : Fin 2886) := Fin.ext h443
    subst k
    rw [keyMomentRowsAt443]
    exact keyMoment443 B hB
  · have he : k = (444 : Fin 2886) := Fin.ext h444
    subst k
    rw [keyMomentRowsAt444]
    exact keyMoment444 B hB
  · have he : k = (445 : Fin 2886) := Fin.ext h445
    subst k
    rw [keyMomentRowsAt445]
    exact keyMoment445 B hB
  · have he : k = (446 : Fin 2886) := Fin.ext h446
    subst k
    rw [keyMomentRowsAt446]
    exact keyMoment446 B hB
  · have he : k = (447 : Fin 2886) := Fin.ext h447
    subst k
    rw [keyMomentRowsAt447]
    exact keyMoment447 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound13_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound13_e_oai
