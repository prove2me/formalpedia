-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound16_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:46:52.543735+00:00
-- url     : https://prove2.me/submissions/9b9db063-09f2-4cb5-a129-784d101660e4

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical312
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39960 raw39960Labels = mixedMoment B node379 node379Labels := by
  calc
    mixedMoment B raw39960 raw39960Labels = mixedMoment B raw39960step0 raw39960step0Labels := by
      have hz : ∀ j, raw39960 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39960step0 = (fun i j => raw39960 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39960step0 raw39960; decide +kernel
      have hl : raw39960step0Labels = raw39960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39960 raw39960Labels permutation434 hz
    mixedMoment B raw39960step0 raw39960step0Labels = mixedMoment B raw39960step1 raw39960step1Labels := by
      have hz : ∀ j, raw39960step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39960step1 = (fun i j => raw39960step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39960step1 raw39960step0; decide +kernel
      have hl : raw39960step1Labels = raw39960step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39960step0 raw39960step0Labels permutation80 hz
    mixedMoment B raw39960step1 raw39960step1Labels = mixedMoment B raw39960step2 raw39960step2Labels := by
      have ha : raw39960step2 = (fun i j => raw39960step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39960step2 raw39960step1; decide +kernel
      have hl : raw39960step2Labels = raw39960step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39960step1 raw39960step1Labels permutation31 permutation7
    _ = mixedMoment B node379 node379Labels := by rfl

theorem canonical39961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39961 raw39961Labels = mixedMoment B node147 node147Labels := by
  calc
    mixedMoment B raw39961 raw39961Labels = mixedMoment B raw39961step0 raw39961step0Labels := by
      have hz : ∀ j, raw39961 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39961step0 = (fun i j => raw39961 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39961step0 raw39961; decide +kernel
      have hl : raw39961step0Labels = raw39961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39961 raw39961Labels permutation434 hz
    mixedMoment B raw39961step0 raw39961step0Labels = mixedMoment B raw39961step1 raw39961step1Labels := by
      have hz : ∀ j, raw39961step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39961step1 = (fun i j => raw39961step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39961step1 raw39961step0; decide +kernel
      have hl : raw39961step1Labels = raw39961step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39961step0 raw39961step0Labels permutation80 hz
    mixedMoment B raw39961step1 raw39961step1Labels = mixedMoment B raw39961step2 raw39961step2Labels := by
      have ha : raw39961step2 = (fun i j => raw39961step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39961step2 raw39961step1; decide +kernel
      have hl : raw39961step2Labels = raw39961step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39961step1 raw39961step1Labels permutation29 permutation6
    _ = mixedMoment B node147 node147Labels := by rfl

theorem canonical39962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39962 raw39962Labels = mixedMoment B node323 node323Labels := by
  calc
    mixedMoment B raw39962 raw39962Labels = mixedMoment B raw39962step0 raw39962step0Labels := by
      have hz : ∀ j, raw39962 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39962step0 = (fun i j => raw39962 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39962step0 raw39962; decide +kernel
      have hl : raw39962step0Labels = raw39962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39962 raw39962Labels permutation346 hz
    mixedMoment B raw39962step0 raw39962step0Labels = mixedMoment B raw39962step1 raw39962step1Labels := by
      have ha : raw39962step1 = (fun i j => raw39962step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39962step1 raw39962step0; decide +kernel
      have hl : raw39962step1Labels = raw39962step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39962step0 raw39962step0Labels permutation95 permutation6
    _ = mixedMoment B node323 node323Labels := by rfl

theorem canonical39963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39963 raw39963Labels = mixedMoment B node374 node374Labels := by
  calc
    mixedMoment B raw39963 raw39963Labels = mixedMoment B raw39963step0 raw39963step0Labels := by
      have hz : ∀ j, raw39963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39963step0 = (fun i j => raw39963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39963step0 raw39963; decide +kernel
      have hl : raw39963step0Labels = raw39963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39963 raw39963Labels permutation346 hz
    mixedMoment B raw39963step0 raw39963step0Labels = mixedMoment B raw39963step1 raw39963step1Labels := by
      have ha : raw39963step1 = (fun i j => raw39963step0 (permutation89 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39963step1 raw39963step0; decide +kernel
      have hl : raw39963step1Labels = raw39963step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39963step0 raw39963step0Labels permutation89 permutation6
    _ = mixedMoment B node374 node374Labels := by rfl

theorem canonical39964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39964 raw39964Labels = mixedMoment B node5503 node5503Labels := by
  calc
    mixedMoment B raw39964 raw39964Labels = mixedMoment B raw39964step0 raw39964step0Labels := by
      have hz : ∀ j, raw39964 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39964step0 = (fun i j => raw39964 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39964step0 raw39964; decide +kernel
      have hl : raw39964step0Labels = raw39964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39964 raw39964Labels permutation434 hz
    mixedMoment B raw39964step0 raw39964step0Labels = mixedMoment B raw39964step1 raw39964step1Labels := by
      have ha : raw39964step1 = (fun i j => raw39964step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39964step1 raw39964step0; decide +kernel
      have hl : raw39964step1Labels = raw39964step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39964step0 raw39964step0Labels permutation97 permutation6
    _ = mixedMoment B node5503 node5503Labels := by rfl

theorem canonical39965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39965 raw39965Labels = mixedMoment B node239 node239Labels := by
  calc
    mixedMoment B raw39965 raw39965Labels = mixedMoment B raw39965step0 raw39965step0Labels := by
      have hz : ∀ j, raw39965 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39965step0 = (fun i j => raw39965 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39965step0 raw39965; decide +kernel
      have hl : raw39965step0Labels = raw39965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39965 raw39965Labels permutation434 hz
    mixedMoment B raw39965step0 raw39965step0Labels = mixedMoment B raw39965step1 raw39965step1Labels := by
      have ha : raw39965step1 = (fun i j => raw39965step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39965step1 raw39965step0; decide +kernel
      have hl : raw39965step1Labels = raw39965step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39965step0 raw39965step0Labels permutation103 permutation6
    _ = mixedMoment B node239 node239Labels := by rfl

theorem canonical39966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39966 raw39966Labels = mixedMoment B node176 node176Labels := by
  calc
    mixedMoment B raw39966 raw39966Labels = mixedMoment B raw39966step0 raw39966step0Labels := by
      have hz : ∀ j, raw39966 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39966step0 = (fun i j => raw39966 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39966step0 raw39966; decide +kernel
      have hl : raw39966step0Labels = raw39966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39966 raw39966Labels permutation434 hz
    mixedMoment B raw39966step0 raw39966step0Labels = mixedMoment B raw39966step1 raw39966step1Labels := by
      have ha : raw39966step1 = (fun i j => raw39966step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39966step1 raw39966step0; decide +kernel
      have hl : raw39966step1Labels = raw39966step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39966step0 raw39966step0Labels permutation101 permutation6
    _ = mixedMoment B node176 node176Labels := by rfl

theorem canonical39967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39967 raw39967Labels = mixedMoment B node164 node164Labels := by
  calc
    mixedMoment B raw39967 raw39967Labels = mixedMoment B raw39967step0 raw39967step0Labels := by
      have ha : raw39967step0 = (fun i j => raw39967 (permutation431 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39967step0 raw39967; decide +kernel
      have hl : raw39967step0Labels = raw39967Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39967 raw39967Labels permutation431 permutation6
    _ = mixedMoment B node164 node164Labels := by rfl

theorem canonical39968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39968 raw39968Labels = mixedMoment B node5508 node5508Labels := by
  calc
    mixedMoment B raw39968 raw39968Labels = mixedMoment B raw39968step0 raw39968step0Labels := by
      have ha : raw39968step0 = (fun i j => raw39968 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39968step0 raw39968; decide +kernel
      have hl : raw39968step0Labels = raw39968Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39968 raw39968Labels permutation173 permutation7
    mixedMoment B raw39968step0 raw39968step0Labels = mixedMoment B raw39968step1 raw39968step1Labels := by
      have ha : raw39968step1 = -raw39968step0 := by apply Matrix.ext; change ∀ i j, raw39968step1 i j = -(raw39968step0 i j); unfold raw39968step1 raw39968step0; decide +kernel
      have hl : raw39968step1Labels = raw39968step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5508 node5508Labels := by rfl

theorem canonical39969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39969 raw39969Labels = mixedMoment B node297 node297Labels := by
  calc
    mixedMoment B raw39969 raw39969Labels = mixedMoment B raw39969step0 raw39969step0Labels := by
      have ha : raw39969step0 = (fun i j => raw39969 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39969step0 raw39969; decide +kernel
      have hl : raw39969step0Labels = raw39969Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39969 raw39969Labels permutation166 permutation7
    mixedMoment B raw39969step0 raw39969step0Labels = mixedMoment B raw39969step1 raw39969step1Labels := by
      have ha : raw39969step1 = -raw39969step0 := by apply Matrix.ext; change ∀ i j, raw39969step1 i j = -(raw39969step0 i j); unfold raw39969step1 raw39969step0; decide +kernel
      have hl : raw39969step1Labels = raw39969step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node297 node297Labels := by rfl

theorem canonical39970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39970 raw39970Labels = mixedMoment B node309 node309Labels := by
  calc
    mixedMoment B raw39970 raw39970Labels = mixedMoment B raw39970step0 raw39970step0Labels := by
      have hz : ∀ j, raw39970 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39970step0 = (fun i j => raw39970 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39970step0 raw39970; decide +kernel
      have hl : raw39970step0Labels = raw39970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39970 raw39970Labels permutation434 hz
    mixedMoment B raw39970step0 raw39970step0Labels = mixedMoment B raw39970step1 raw39970step1Labels := by
      have ha : raw39970step1 = (fun i j => raw39970step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39970step1 raw39970step0; decide +kernel
      have hl : raw39970step1Labels = raw39970step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39970step0 raw39970step0Labels permutation36 permutation7
    mixedMoment B raw39970step1 raw39970step1Labels = mixedMoment B raw39970step2 raw39970step2Labels := by
      have ha : raw39970step2 = -raw39970step1 := by apply Matrix.ext; change ∀ i j, raw39970step2 i j = -(raw39970step1 i j); unfold raw39970step2 raw39970step1; decide +kernel
      have hl : raw39970step2Labels = raw39970step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node309 node309Labels := by rfl

theorem canonical39971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39971 raw39971Labels = mixedMoment B node306 node306Labels := by
  calc
    mixedMoment B raw39971 raw39971Labels = mixedMoment B raw39971step0 raw39971step0Labels := by
      have hz : ∀ j, raw39971 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39971step0 = (fun i j => raw39971 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39971step0 raw39971; decide +kernel
      have hl : raw39971step0Labels = raw39971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39971 raw39971Labels permutation434 hz
    mixedMoment B raw39971step0 raw39971step0Labels = mixedMoment B raw39971step1 raw39971step1Labels := by
      have ha : raw39971step1 = (fun i j => raw39971step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39971step1 raw39971step0; decide +kernel
      have hl : raw39971step1Labels = raw39971step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39971step0 raw39971step0Labels permutation34 permutation7
    mixedMoment B raw39971step1 raw39971step1Labels = mixedMoment B raw39971step2 raw39971step2Labels := by
      have ha : raw39971step2 = -raw39971step1 := by apply Matrix.ext; change ∀ i j, raw39971step2 i j = -(raw39971step1 i j); unfold raw39971step2 raw39971step1; decide +kernel
      have hl : raw39971step2Labels = raw39971step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node306 node306Labels := by rfl

theorem canonical39972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39972 raw39972Labels = mixedMoment B node281 node281Labels := by
  calc
    mixedMoment B raw39972 raw39972Labels = mixedMoment B raw39972step0 raw39972step0Labels := by
      have hz : ∀ j, raw39972 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39972step0 = (fun i j => raw39972 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39972step0 raw39972; decide +kernel
      have hl : raw39972step0Labels = raw39972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39972 raw39972Labels permutation434 hz
    mixedMoment B raw39972step0 raw39972step0Labels = mixedMoment B raw39972step1 raw39972step1Labels := by
      have ha : raw39972step1 = (fun i j => raw39972step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39972step1 raw39972step0; decide +kernel
      have hl : raw39972step1Labels = raw39972step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39972step0 raw39972step0Labels permutation145 permutation7
    _ = mixedMoment B node281 node281Labels := by rfl

theorem canonical39973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39973 raw39973Labels = mixedMoment B node298 node298Labels := by
  calc
    mixedMoment B raw39973 raw39973Labels = mixedMoment B raw39973step0 raw39973step0Labels := by
      have ha : raw39973step0 = (fun i j => raw39973 (permutation174 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39973step0 raw39973; decide +kernel
      have hl : raw39973step0Labels = raw39973Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39973 raw39973Labels permutation174 permutation7
    mixedMoment B raw39973step0 raw39973step0Labels = mixedMoment B raw39973step1 raw39973step1Labels := by
      have ha : raw39973step1 = -raw39973step0 := by apply Matrix.ext; change ∀ i j, raw39973step1 i j = -(raw39973step0 i j); unfold raw39973step1 raw39973step0; decide +kernel
      have hl : raw39973step1Labels = raw39973step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node298 node298Labels := by rfl

theorem canonical39974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39974 raw39974Labels = mixedMoment B node300 node300Labels := by
  calc
    mixedMoment B raw39974 raw39974Labels = mixedMoment B raw39974step0 raw39974step0Labels := by
      have ha : raw39974step0 = (fun i j => raw39974 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39974step0 raw39974; decide +kernel
      have hl : raw39974step0Labels = raw39974Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39974 raw39974Labels permutation168 permutation7
    mixedMoment B raw39974step0 raw39974step0Labels = mixedMoment B raw39974step1 raw39974step1Labels := by
      have ha : raw39974step1 = -raw39974step0 := by apply Matrix.ext; change ∀ i j, raw39974step1 i j = -(raw39974step0 i j); unfold raw39974step1 raw39974step0; decide +kernel
      have hl : raw39974step1Labels = raw39974step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node300 node300Labels := by rfl

theorem canonical39975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39975 raw39975Labels = mixedMoment B node301 node301Labels := by
  calc
    mixedMoment B raw39975 raw39975Labels = mixedMoment B raw39975step0 raw39975step0Labels := by
      have ha : raw39975step0 = (fun i j => raw39975 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39975step0 raw39975; decide +kernel
      have hl : raw39975step0Labels = raw39975Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39975 raw39975Labels permutation164 permutation7
    mixedMoment B raw39975step0 raw39975step0Labels = mixedMoment B raw39975step1 raw39975step1Labels := by
      have ha : raw39975step1 = -raw39975step0 := by apply Matrix.ext; change ∀ i j, raw39975step1 i j = -(raw39975step0 i j); unfold raw39975step1 raw39975step0; decide +kernel
      have hl : raw39975step1Labels = raw39975step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node301 node301Labels := by rfl

theorem canonical39976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39976 raw39976Labels = mixedMoment B node308 node308Labels := by
  calc
    mixedMoment B raw39976 raw39976Labels = mixedMoment B raw39976step0 raw39976step0Labels := by
      have hz : ∀ j, raw39976 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39976step0 = (fun i j => raw39976 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39976step0 raw39976; decide +kernel
      have hl : raw39976step0Labels = raw39976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39976 raw39976Labels permutation434 hz
    mixedMoment B raw39976step0 raw39976step0Labels = mixedMoment B raw39976step1 raw39976step1Labels := by
      have ha : raw39976step1 = (fun i j => raw39976step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39976step1 raw39976step0; decide +kernel
      have hl : raw39976step1Labels = raw39976step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39976step0 raw39976step0Labels permutation121 permutation6
    _ = mixedMoment B node308 node308Labels := by rfl

theorem canonical39977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39977 raw39977Labels = mixedMoment B node303 node303Labels := by
  calc
    mixedMoment B raw39977 raw39977Labels = mixedMoment B raw39977step0 raw39977step0Labels := by
      have hz : ∀ j, raw39977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39977step0 = (fun i j => raw39977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39977step0 raw39977; decide +kernel
      have hl : raw39977step0Labels = raw39977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39977 raw39977Labels permutation434 hz
    mixedMoment B raw39977step0 raw39977step0Labels = mixedMoment B raw39977step1 raw39977step1Labels := by
      have ha : raw39977step1 = (fun i j => raw39977step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39977step1 raw39977step0; decide +kernel
      have hl : raw39977step1Labels = raw39977step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39977step0 raw39977step0Labels permutation34 permutation7
    mixedMoment B raw39977step1 raw39977step1Labels = mixedMoment B raw39977step2 raw39977step2Labels := by
      have ha : raw39977step2 = -raw39977step1 := by apply Matrix.ext; change ∀ i j, raw39977step2 i j = -(raw39977step1 i j); unfold raw39977step2 raw39977step1; decide +kernel
      have hl : raw39977step2Labels = raw39977step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node303 node303Labels := by rfl

theorem canonical39978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39978 raw39978Labels = mixedMoment B node122 node122Labels := by
  calc
    mixedMoment B raw39978 raw39978Labels = mixedMoment B raw39978step0 raw39978step0Labels := by
      have hz : ∀ j, raw39978 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39978step0 = (fun i j => raw39978 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39978step0 raw39978; decide +kernel
      have hl : raw39978step0Labels = raw39978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39978 raw39978Labels permutation434 hz
    mixedMoment B raw39978step0 raw39978step0Labels = mixedMoment B raw39978step1 raw39978step1Labels := by
      have ha : raw39978step1 = (fun i j => raw39978step0 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39978step1 raw39978step0; decide +kernel
      have hl : raw39978step1Labels = raw39978step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39978step0 raw39978step0Labels permutation143 permutation6
    _ = mixedMoment B node122 node122Labels := by rfl

theorem canonical39979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39979 raw39979Labels = mixedMoment B node292 node292Labels := by
  calc
    mixedMoment B raw39979 raw39979Labels = mixedMoment B raw39979step0 raw39979step0Labels := by
      have ha : raw39979step0 = (fun i j => raw39979 (permutation478 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39979step0 raw39979; decide +kernel
      have hl : raw39979step0Labels = raw39979Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39979 raw39979Labels permutation478 permutation6
    _ = mixedMoment B node292 node292Labels := by rfl

theorem canonical39980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39980 raw39980Labels = mixedMoment B node299 node299Labels := by
  calc
    mixedMoment B raw39980 raw39980Labels = mixedMoment B raw39980step0 raw39980step0Labels := by
      have ha : raw39980step0 = (fun i j => raw39980 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39980step0 raw39980; decide +kernel
      have hl : raw39980step0Labels = raw39980Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39980 raw39980Labels permutation480 permutation6
    _ = mixedMoment B node299 node299Labels := by rfl

theorem canonical39981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39981 raw39981Labels = mixedMoment B node5504 node5504Labels := by
  calc
    mixedMoment B raw39981 raw39981Labels = mixedMoment B raw39981step0 raw39981step0Labels := by
      have hz : ∀ j, raw39981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39981step0 = (fun i j => raw39981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39981step0 raw39981; decide +kernel
      have hl : raw39981step0Labels = raw39981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39981 raw39981Labels permutation434 hz
    mixedMoment B raw39981step0 raw39981step0Labels = mixedMoment B raw39981step1 raw39981step1Labels := by
      have hz : ∀ j, raw39981step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39981step1 = (fun i j => raw39981step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39981step1 raw39981step0; decide +kernel
      have hl : raw39981step1Labels = raw39981step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39981step0 raw39981step0Labels permutation80 hz
    mixedMoment B raw39981step1 raw39981step1Labels = mixedMoment B raw39981step2 raw39981step2Labels := by
      have ha : raw39981step2 = (fun i j => raw39981step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39981step2 raw39981step1; decide +kernel
      have hl : raw39981step2Labels = raw39981step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39981step1 raw39981step1Labels permutation25 permutation6
    _ = mixedMoment B node5504 node5504Labels := by rfl

theorem canonical39982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39982 raw39982Labels = mixedMoment B node146 node146Labels := by
  calc
    mixedMoment B raw39982 raw39982Labels = mixedMoment B raw39982step0 raw39982step0Labels := by
      have hz : ∀ j, raw39982 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39982step0 = (fun i j => raw39982 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39982step0 raw39982; decide +kernel
      have hl : raw39982step0Labels = raw39982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39982 raw39982Labels permutation434 hz
    mixedMoment B raw39982step0 raw39982step0Labels = mixedMoment B raw39982step1 raw39982step1Labels := by
      have hz : ∀ j, raw39982step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39982step1 = (fun i j => raw39982step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39982step1 raw39982step0; decide +kernel
      have hl : raw39982step1Labels = raw39982step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39982step0 raw39982step0Labels permutation80 hz
    mixedMoment B raw39982step1 raw39982step1Labels = mixedMoment B raw39982step2 raw39982step2Labels := by
      have ha : raw39982step2 = (fun i j => raw39982step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39982step2 raw39982step1; decide +kernel
      have hl : raw39982step2Labels = raw39982step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39982step1 raw39982step1Labels permutation31 permutation7
    _ = mixedMoment B node146 node146Labels := by rfl

theorem canonical39983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39983 raw39983Labels = mixedMoment B node11 node11Labels := by
  calc
    mixedMoment B raw39983 raw39983Labels = mixedMoment B raw39983step0 raw39983step0Labels := by
      have hz : ∀ j, raw39983 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39983step0 = (fun i j => raw39983 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39983step0 raw39983; decide +kernel
      have hl : raw39983step0Labels = raw39983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39983 raw39983Labels permutation346 hz
    mixedMoment B raw39983step0 raw39983step0Labels = mixedMoment B raw39983step1 raw39983step1Labels := by
      have ha : raw39983step1 = (fun i j => raw39983step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39983step1 raw39983step0; decide +kernel
      have hl : raw39983step1Labels = raw39983step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39983step0 raw39983step0Labels permutation149 permutation6
    _ = mixedMoment B node11 node11Labels := by rfl

theorem canonical39984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39984 raw39984Labels = mixedMoment B node169 node169Labels := by
  calc
    mixedMoment B raw39984 raw39984Labels = mixedMoment B raw39984step0 raw39984step0Labels := by
      have hz : ∀ j, raw39984 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39984step0 = (fun i j => raw39984 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39984step0 raw39984; decide +kernel
      have hl : raw39984step0Labels = raw39984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39984 raw39984Labels permutation434 hz
    mixedMoment B raw39984step0 raw39984step0Labels = mixedMoment B raw39984step1 raw39984step1Labels := by
      have ha : raw39984step1 = (fun i j => raw39984step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39984step1 raw39984step0; decide +kernel
      have hl : raw39984step1Labels = raw39984step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39984step0 raw39984step0Labels permutation103 permutation6
    _ = mixedMoment B node169 node169Labels := by rfl

theorem canonical39985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39985 raw39985Labels = mixedMoment B node18 node18Labels := by
  calc
    mixedMoment B raw39985 raw39985Labels = mixedMoment B raw39985step0 raw39985step0Labels := by
      have hz : ∀ j, raw39985 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39985step0 = (fun i j => raw39985 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39985step0 raw39985; decide +kernel
      have hl : raw39985step0Labels = raw39985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39985 raw39985Labels permutation434 hz
    mixedMoment B raw39985step0 raw39985step0Labels = mixedMoment B raw39985step1 raw39985step1Labels := by
      have hz : ∀ j, raw39985step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39985step1 = (fun i j => raw39985step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39985step1 raw39985step0; decide +kernel
      have hl : raw39985step1Labels = raw39985step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39985step0 raw39985step0Labels permutation80 hz
    mixedMoment B raw39985step1 raw39985step1Labels = mixedMoment B raw39985step2 raw39985step2Labels := by
      have ha : raw39985step2 = (fun i j => raw39985step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39985step2 raw39985step1; decide +kernel
      have hl : raw39985step2Labels = raw39985step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39985step1 raw39985step1Labels permutation31 permutation6
    _ = mixedMoment B node18 node18Labels := by rfl

theorem canonical39986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39986 raw39986Labels = mixedMoment B node270 node270Labels := by
  calc
    mixedMoment B raw39986 raw39986Labels = mixedMoment B raw39986step0 raw39986step0Labels := by
      have hz : ∀ j, raw39986 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39986step0 = (fun i j => raw39986 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39986step0 raw39986; decide +kernel
      have hl : raw39986step0Labels = raw39986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39986 raw39986Labels permutation520 hz
    mixedMoment B raw39986step0 raw39986step0Labels = mixedMoment B raw39986step1 raw39986step1Labels := by
      have hz : ∀ j, raw39986step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39986step1 = (fun i j => raw39986step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39986step1 raw39986step0; decide +kernel
      have hl : raw39986step1Labels = raw39986step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39986step0 raw39986step0Labels permutation104 hz
    mixedMoment B raw39986step1 raw39986step1Labels = mixedMoment B raw39986step2 raw39986step2Labels := by
      have hz : ∀ j, raw39986step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39986step2 = (fun i j => raw39986step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39986step2 raw39986step1; decide +kernel
      have hl : raw39986step2Labels = raw39986step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39986step1 raw39986step1Labels permutation20 hz
    mixedMoment B raw39986step2 raw39986step2Labels = mixedMoment B raw39986step3 raw39986step3Labels := by
      have ha : raw39986step3 = (fun i j => raw39986step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39986step3 raw39986step2; decide +kernel
      have hl : raw39986step3Labels = raw39986step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39986step2 raw39986step2Labels permutation5 permutation6
    _ = mixedMoment B node270 node270Labels := by rfl

theorem canonical39987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39987 raw39987Labels = mixedMoment B node249 node249Labels := by
  calc
    mixedMoment B raw39987 raw39987Labels = mixedMoment B raw39987step0 raw39987step0Labels := by
      have hz : ∀ j, raw39987 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39987step0 = (fun i j => raw39987 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39987step0 raw39987; decide +kernel
      have hl : raw39987step0Labels = raw39987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39987 raw39987Labels permutation434 hz
    mixedMoment B raw39987step0 raw39987step0Labels = mixedMoment B raw39987step1 raw39987step1Labels := by
      have hz : ∀ j, raw39987step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39987step1 = (fun i j => raw39987step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39987step1 raw39987step0; decide +kernel
      have hl : raw39987step1Labels = raw39987step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39987step0 raw39987step0Labels permutation80 hz
    mixedMoment B raw39987step1 raw39987step1Labels = mixedMoment B raw39987step2 raw39987step2Labels := by
      have ha : raw39987step2 = (fun i j => raw39987step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39987step2 raw39987step1; decide +kernel
      have hl : raw39987step2Labels = raw39987step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39987step1 raw39987step1Labels permutation19 permutation6
    _ = mixedMoment B node249 node249Labels := by rfl

theorem canonical39988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39988 raw39988Labels = mixedMoment B node187 node187Labels := by
  calc
    mixedMoment B raw39988 raw39988Labels = mixedMoment B raw39988step0 raw39988step0Labels := by
      have hz : ∀ j, raw39988 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39988step0 = (fun i j => raw39988 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39988step0 raw39988; decide +kernel
      have hl : raw39988step0Labels = raw39988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39988 raw39988Labels permutation434 hz
    mixedMoment B raw39988step0 raw39988step0Labels = mixedMoment B raw39988step1 raw39988step1Labels := by
      have hz : ∀ j, raw39988step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39988step1 = (fun i j => raw39988step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39988step1 raw39988step0; decide +kernel
      have hl : raw39988step1Labels = raw39988step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39988step0 raw39988step0Labels permutation80 hz
    mixedMoment B raw39988step1 raw39988step1Labels = mixedMoment B raw39988step2 raw39988step2Labels := by
      have ha : raw39988step2 = (fun i j => raw39988step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39988step2 raw39988step1; decide +kernel
      have hl : raw39988step2Labels = raw39988step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39988step1 raw39988step1Labels permutation19 permutation6
    _ = mixedMoment B node187 node187Labels := by rfl

theorem canonical39989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39989 raw39989Labels = mixedMoment B node236 node236Labels := by
  calc
    mixedMoment B raw39989 raw39989Labels = mixedMoment B raw39989step0 raw39989step0Labels := by
      have hz : ∀ j, raw39989 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39989step0 = (fun i j => raw39989 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39989step0 raw39989; decide +kernel
      have hl : raw39989step0Labels = raw39989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39989 raw39989Labels permutation434 hz
    mixedMoment B raw39989step0 raw39989step0Labels = mixedMoment B raw39989step1 raw39989step1Labels := by
      have hz : ∀ j, raw39989step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39989step1 = (fun i j => raw39989step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39989step1 raw39989step0; decide +kernel
      have hl : raw39989step1Labels = raw39989step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39989step0 raw39989step0Labels permutation80 hz
    mixedMoment B raw39989step1 raw39989step1Labels = mixedMoment B raw39989step2 raw39989step2Labels := by
      have ha : raw39989step2 = (fun i j => raw39989step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39989step2 raw39989step1; decide +kernel
      have hl : raw39989step2Labels = raw39989step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39989step1 raw39989step1Labels permutation17 permutation6
    _ = mixedMoment B node236 node236Labels := by rfl

theorem canonical39990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39990 raw39990Labels = mixedMoment B node262 node262Labels := by
  calc
    mixedMoment B raw39990 raw39990Labels = mixedMoment B raw39990step0 raw39990step0Labels := by
      have hz : ∀ j, raw39990 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39990step0 = (fun i j => raw39990 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39990step0 raw39990; decide +kernel
      have hl : raw39990step0Labels = raw39990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39990 raw39990Labels permutation434 hz
    mixedMoment B raw39990step0 raw39990step0Labels = mixedMoment B raw39990step1 raw39990step1Labels := by
      have hz : ∀ j, raw39990step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39990step1 = (fun i j => raw39990step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39990step1 raw39990step0; decide +kernel
      have hl : raw39990step1Labels = raw39990step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39990step0 raw39990step0Labels permutation80 hz
    mixedMoment B raw39990step1 raw39990step1Labels = mixedMoment B raw39990step2 raw39990step2Labels := by
      have ha : raw39990step2 = (fun i j => raw39990step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39990step2 raw39990step1; decide +kernel
      have hl : raw39990step2Labels = raw39990step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39990step1 raw39990step1Labels permutation17 permutation6
    _ = mixedMoment B node262 node262Labels := by rfl

theorem canonical39991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39991 raw39991Labels = mixedMoment B node180 node180Labels := by
  calc
    mixedMoment B raw39991 raw39991Labels = mixedMoment B raw39991step0 raw39991step0Labels := by
      have hz : ∀ j, raw39991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39991step0 = (fun i j => raw39991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39991step0 raw39991; decide +kernel
      have hl : raw39991step0Labels = raw39991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39991 raw39991Labels permutation346 hz
    mixedMoment B raw39991step0 raw39991step0Labels = mixedMoment B raw39991step1 raw39991step1Labels := by
      have ha : raw39991step1 = (fun i j => raw39991step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39991step1 raw39991step0; decide +kernel
      have hl : raw39991step1Labels = raw39991step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39991step0 raw39991step0Labels permutation77 permutation6
    _ = mixedMoment B node180 node180Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment512 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 512) =
      Integer.Sparse.eval keyMomentRow512 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 512).leftCharge (GramAssembly.key 512).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 379) := by
    have ha : gramCharges (GramAssembly.key 512).leftCharge (GramAssembly.key 512).rightCharge = raw39960 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39960Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39960 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 512).leftCharge (GramAssembly.key 512).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow512, Integer.Sparse.eval]

theorem keyMoment513 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 513) =
      Integer.Sparse.eval keyMomentRow513 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 513).leftCharge (GramAssembly.key 513).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 147) := by
    have ha : gramCharges (GramAssembly.key 513).leftCharge (GramAssembly.key 513).rightCharge = raw39961 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39961Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39961 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 513).leftCharge (GramAssembly.key 513).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow513, Integer.Sparse.eval]

theorem keyMoment514 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 514) =
      Integer.Sparse.eval keyMomentRow514 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 514).leftCharge (GramAssembly.key 514).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 323) := by
    have ha : gramCharges (GramAssembly.key 514).leftCharge (GramAssembly.key 514).rightCharge = raw39962 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39962Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39962 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 514).leftCharge (GramAssembly.key 514).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow514, Integer.Sparse.eval]

theorem keyMoment515 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 515) =
      Integer.Sparse.eval keyMomentRow515 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 515).leftCharge (GramAssembly.key 515).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 374) := by
    have ha : gramCharges (GramAssembly.key 515).leftCharge (GramAssembly.key 515).rightCharge = raw39963 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39963Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39963 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 515).leftCharge (GramAssembly.key 515).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow515, Integer.Sparse.eval]

theorem keyMoment516 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 516) =
      Integer.Sparse.eval keyMomentRow516 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 516).leftCharge (GramAssembly.key 516).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 1) := by
    have ha : gramCharges (GramAssembly.key 516).leftCharge (GramAssembly.key 516).rightCharge = raw39964 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39964Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39964 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 516).leftCharge (GramAssembly.key 516).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow516, Integer.Sparse.eval]

theorem keyMoment517 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 517) =
      Integer.Sparse.eval keyMomentRow517 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 517).leftCharge (GramAssembly.key 517).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 239) := by
    have ha : gramCharges (GramAssembly.key 517).leftCharge (GramAssembly.key 517).rightCharge = raw39965 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39965Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39965 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 517).leftCharge (GramAssembly.key 517).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow517, Integer.Sparse.eval]

theorem keyMoment518 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 518) =
      Integer.Sparse.eval keyMomentRow518 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 518).leftCharge (GramAssembly.key 518).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 176) := by
    have ha : gramCharges (GramAssembly.key 518).leftCharge (GramAssembly.key 518).rightCharge = raw39966 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39966Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39966 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 518).leftCharge (GramAssembly.key 518).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow518, Integer.Sparse.eval]

theorem keyMoment519 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 519) =
      Integer.Sparse.eval keyMomentRow519 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 519).leftCharge (GramAssembly.key 519).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 164) := by
    have ha : gramCharges (GramAssembly.key 519).leftCharge (GramAssembly.key 519).rightCharge = raw39967 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39967Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39967 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 519).leftCharge (GramAssembly.key 519).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow519, Integer.Sparse.eval]

theorem keyMoment520 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 520) =
      Integer.Sparse.eval keyMomentRow520 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 520).leftCharge (GramAssembly.key 520).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 6) := by
    have ha : gramCharges (GramAssembly.key 520).leftCharge (GramAssembly.key 520).rightCharge = raw39968 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39968Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39968 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 520).leftCharge (GramAssembly.key 520).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow520, Integer.Sparse.eval]

theorem keyMoment521 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 521) =
      Integer.Sparse.eval keyMomentRow521 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 521).leftCharge (GramAssembly.key 521).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 297) := by
    have ha : gramCharges (GramAssembly.key 521).leftCharge (GramAssembly.key 521).rightCharge = raw39969 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39969Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39969 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 521).leftCharge (GramAssembly.key 521).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow521, Integer.Sparse.eval]

theorem keyMoment522 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 522) =
      Integer.Sparse.eval keyMomentRow522 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 522).leftCharge (GramAssembly.key 522).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 309) := by
    have ha : gramCharges (GramAssembly.key 522).leftCharge (GramAssembly.key 522).rightCharge = raw39970 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39970Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39970 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 522).leftCharge (GramAssembly.key 522).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow522, Integer.Sparse.eval]

theorem keyMoment523 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 523) =
      Integer.Sparse.eval keyMomentRow523 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 523).leftCharge (GramAssembly.key 523).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 306) := by
    have ha : gramCharges (GramAssembly.key 523).leftCharge (GramAssembly.key 523).rightCharge = raw39971 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39971Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39971 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 523).leftCharge (GramAssembly.key 523).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow523, Integer.Sparse.eval]

theorem keyMoment524 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 524) =
      Integer.Sparse.eval keyMomentRow524 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 524).leftCharge (GramAssembly.key 524).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 281) := by
    have ha : gramCharges (GramAssembly.key 524).leftCharge (GramAssembly.key 524).rightCharge = raw39972 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39972Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39972 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 524).leftCharge (GramAssembly.key 524).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow524, Integer.Sparse.eval]

theorem keyMoment525 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 525) =
      Integer.Sparse.eval keyMomentRow525 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 525).leftCharge (GramAssembly.key 525).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 298) := by
    have ha : gramCharges (GramAssembly.key 525).leftCharge (GramAssembly.key 525).rightCharge = raw39973 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39973Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39973 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 525).leftCharge (GramAssembly.key 525).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow525, Integer.Sparse.eval]

theorem keyMoment526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 526) =
      Integer.Sparse.eval keyMomentRow526 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 526).leftCharge (GramAssembly.key 526).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 300) := by
    have ha : gramCharges (GramAssembly.key 526).leftCharge (GramAssembly.key 526).rightCharge = raw39974 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39974Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39974 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 526).leftCharge (GramAssembly.key 526).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow526, Integer.Sparse.eval]

theorem keyMoment527 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 527) =
      Integer.Sparse.eval keyMomentRow527 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 527).leftCharge (GramAssembly.key 527).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 301) := by
    have ha : gramCharges (GramAssembly.key 527).leftCharge (GramAssembly.key 527).rightCharge = raw39975 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39975Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39975 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 527).leftCharge (GramAssembly.key 527).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow527, Integer.Sparse.eval]

theorem keyMoment528 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 528) =
      Integer.Sparse.eval keyMomentRow528 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 528).leftCharge (GramAssembly.key 528).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 308) := by
    have ha : gramCharges (GramAssembly.key 528).leftCharge (GramAssembly.key 528).rightCharge = raw39976 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39976Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39976 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 528).leftCharge (GramAssembly.key 528).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow528, Integer.Sparse.eval]

theorem keyMoment529 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 529) =
      Integer.Sparse.eval keyMomentRow529 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 529).leftCharge (GramAssembly.key 529).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 303) := by
    have ha : gramCharges (GramAssembly.key 529).leftCharge (GramAssembly.key 529).rightCharge = raw39977 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39977Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39977 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 529).leftCharge (GramAssembly.key 529).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow529, Integer.Sparse.eval]

theorem keyMoment530 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 530) =
      Integer.Sparse.eval keyMomentRow530 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 530).leftCharge (GramAssembly.key 530).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 122) := by
    have ha : gramCharges (GramAssembly.key 530).leftCharge (GramAssembly.key 530).rightCharge = raw39978 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39978Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39978 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 530).leftCharge (GramAssembly.key 530).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow530, Integer.Sparse.eval]

theorem keyMoment531 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 531) =
      Integer.Sparse.eval keyMomentRow531 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 531).leftCharge (GramAssembly.key 531).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 292) := by
    have ha : gramCharges (GramAssembly.key 531).leftCharge (GramAssembly.key 531).rightCharge = raw39979 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39979Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39979 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 531).leftCharge (GramAssembly.key 531).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow531, Integer.Sparse.eval]

theorem keyMoment532 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 532) =
      Integer.Sparse.eval keyMomentRow532 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 532).leftCharge (GramAssembly.key 532).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 299) := by
    have ha : gramCharges (GramAssembly.key 532).leftCharge (GramAssembly.key 532).rightCharge = raw39980 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39980Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39980 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 532).leftCharge (GramAssembly.key 532).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow532, Integer.Sparse.eval]

theorem keyMoment533 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 533) =
      Integer.Sparse.eval keyMomentRow533 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 533).leftCharge (GramAssembly.key 533).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 2) := by
    have ha : gramCharges (GramAssembly.key 533).leftCharge (GramAssembly.key 533).rightCharge = raw39981 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39981Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39981 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 533).leftCharge (GramAssembly.key 533).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow533, Integer.Sparse.eval]

theorem keyMoment534 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 534) =
      Integer.Sparse.eval keyMomentRow534 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 534).leftCharge (GramAssembly.key 534).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 146) := by
    have ha : gramCharges (GramAssembly.key 534).leftCharge (GramAssembly.key 534).rightCharge = raw39982 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39982Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39982 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 534).leftCharge (GramAssembly.key 534).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow534, Integer.Sparse.eval]

theorem keyMoment535 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 535) =
      Integer.Sparse.eval keyMomentRow535 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 535).leftCharge (GramAssembly.key 535).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 11) := by
    have ha : gramCharges (GramAssembly.key 535).leftCharge (GramAssembly.key 535).rightCharge = raw39983 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39983Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39983 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 535).leftCharge (GramAssembly.key 535).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow535, Integer.Sparse.eval]

theorem keyMoment536 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 536) =
      Integer.Sparse.eval keyMomentRow536 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 536).leftCharge (GramAssembly.key 536).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 169) := by
    have ha : gramCharges (GramAssembly.key 536).leftCharge (GramAssembly.key 536).rightCharge = raw39984 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39984Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39984 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 536).leftCharge (GramAssembly.key 536).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow536, Integer.Sparse.eval]

theorem keyMoment537 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 537) =
      Integer.Sparse.eval keyMomentRow537 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 537).leftCharge (GramAssembly.key 537).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 18) := by
    have ha : gramCharges (GramAssembly.key 537).leftCharge (GramAssembly.key 537).rightCharge = raw39985 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39985Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39985 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 537).leftCharge (GramAssembly.key 537).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow537, Integer.Sparse.eval]

theorem keyMoment538 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 538) =
      Integer.Sparse.eval keyMomentRow538 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 538).leftCharge (GramAssembly.key 538).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 270) := by
    have ha : gramCharges (GramAssembly.key 538).leftCharge (GramAssembly.key 538).rightCharge = raw39986 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39986Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39986 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 538).leftCharge (GramAssembly.key 538).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow538, Integer.Sparse.eval]

theorem keyMoment539 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 539) =
      Integer.Sparse.eval keyMomentRow539 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 539).leftCharge (GramAssembly.key 539).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 249) := by
    have ha : gramCharges (GramAssembly.key 539).leftCharge (GramAssembly.key 539).rightCharge = raw39987 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39987Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39987 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 539).leftCharge (GramAssembly.key 539).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow539, Integer.Sparse.eval]

theorem keyMoment540 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 540) =
      Integer.Sparse.eval keyMomentRow540 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 540).leftCharge (GramAssembly.key 540).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 187) := by
    have ha : gramCharges (GramAssembly.key 540).leftCharge (GramAssembly.key 540).rightCharge = raw39988 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39988Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39988 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 540).leftCharge (GramAssembly.key 540).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow540, Integer.Sparse.eval]

theorem keyMoment541 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 541) =
      Integer.Sparse.eval keyMomentRow541 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 541).leftCharge (GramAssembly.key 541).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 236) := by
    have ha : gramCharges (GramAssembly.key 541).leftCharge (GramAssembly.key 541).rightCharge = raw39989 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39989Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39989 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 541).leftCharge (GramAssembly.key 541).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow541, Integer.Sparse.eval]

theorem keyMoment542 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 542) =
      Integer.Sparse.eval keyMomentRow542 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 542).leftCharge (GramAssembly.key 542).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 262) := by
    have ha : gramCharges (GramAssembly.key 542).leftCharge (GramAssembly.key 542).rightCharge = raw39990 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39990Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39990 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 542).leftCharge (GramAssembly.key 542).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow542, Integer.Sparse.eval]

theorem keyMoment543 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 543) =
      Integer.Sparse.eval keyMomentRow543 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 543).leftCharge (GramAssembly.key 543).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 180) := by
    have ha : gramCharges (GramAssembly.key 543).leftCharge (GramAssembly.key 543).rightCharge = raw39991 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39991Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39991 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 543).leftCharge (GramAssembly.key 543).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow543, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt512 : keyMomentRows (512 : Fin 2886) =
    keyMomentRow512 := by decide +kernel

theorem keyMomentRowsAt513 : keyMomentRows (513 : Fin 2886) =
    keyMomentRow513 := by decide +kernel

theorem keyMomentRowsAt514 : keyMomentRows (514 : Fin 2886) =
    keyMomentRow514 := by decide +kernel

theorem keyMomentRowsAt515 : keyMomentRows (515 : Fin 2886) =
    keyMomentRow515 := by decide +kernel

theorem keyMomentRowsAt516 : keyMomentRows (516 : Fin 2886) =
    keyMomentRow516 := by decide +kernel

theorem keyMomentRowsAt517 : keyMomentRows (517 : Fin 2886) =
    keyMomentRow517 := by decide +kernel

theorem keyMomentRowsAt518 : keyMomentRows (518 : Fin 2886) =
    keyMomentRow518 := by decide +kernel

theorem keyMomentRowsAt519 : keyMomentRows (519 : Fin 2886) =
    keyMomentRow519 := by decide +kernel

theorem keyMomentRowsAt520 : keyMomentRows (520 : Fin 2886) =
    keyMomentRow520 := by decide +kernel

theorem keyMomentRowsAt521 : keyMomentRows (521 : Fin 2886) =
    keyMomentRow521 := by decide +kernel

theorem keyMomentRowsAt522 : keyMomentRows (522 : Fin 2886) =
    keyMomentRow522 := by decide +kernel

theorem keyMomentRowsAt523 : keyMomentRows (523 : Fin 2886) =
    keyMomentRow523 := by decide +kernel

theorem keyMomentRowsAt524 : keyMomentRows (524 : Fin 2886) =
    keyMomentRow524 := by decide +kernel

theorem keyMomentRowsAt525 : keyMomentRows (525 : Fin 2886) =
    keyMomentRow525 := by decide +kernel

theorem keyMomentRowsAt526 : keyMomentRows (526 : Fin 2886) =
    keyMomentRow526 := by decide +kernel

theorem keyMomentRowsAt527 : keyMomentRows (527 : Fin 2886) =
    keyMomentRow527 := by decide +kernel

theorem keyMomentRowsAt528 : keyMomentRows (528 : Fin 2886) =
    keyMomentRow528 := by decide +kernel

theorem keyMomentRowsAt529 : keyMomentRows (529 : Fin 2886) =
    keyMomentRow529 := by decide +kernel

theorem keyMomentRowsAt530 : keyMomentRows (530 : Fin 2886) =
    keyMomentRow530 := by decide +kernel

theorem keyMomentRowsAt531 : keyMomentRows (531 : Fin 2886) =
    keyMomentRow531 := by decide +kernel

theorem keyMomentRowsAt532 : keyMomentRows (532 : Fin 2886) =
    keyMomentRow532 := by decide +kernel

theorem keyMomentRowsAt533 : keyMomentRows (533 : Fin 2886) =
    keyMomentRow533 := by decide +kernel

theorem keyMomentRowsAt534 : keyMomentRows (534 : Fin 2886) =
    keyMomentRow534 := by decide +kernel

theorem keyMomentRowsAt535 : keyMomentRows (535 : Fin 2886) =
    keyMomentRow535 := by decide +kernel

theorem keyMomentRowsAt536 : keyMomentRows (536 : Fin 2886) =
    keyMomentRow536 := by decide +kernel

theorem keyMomentRowsAt537 : keyMomentRows (537 : Fin 2886) =
    keyMomentRow537 := by decide +kernel

theorem keyMomentRowsAt538 : keyMomentRows (538 : Fin 2886) =
    keyMomentRow538 := by decide +kernel

theorem keyMomentRowsAt539 : keyMomentRows (539 : Fin 2886) =
    keyMomentRow539 := by decide +kernel

theorem keyMomentRowsAt540 : keyMomentRows (540 : Fin 2886) =
    keyMomentRow540 := by decide +kernel

theorem keyMomentRowsAt541 : keyMomentRows (541 : Fin 2886) =
    keyMomentRow541 := by decide +kernel

theorem keyMomentRowsAt542 : keyMomentRows (542 : Fin 2886) =
    keyMomentRow542 := by decide +kernel

theorem keyMomentRowsAt543 : keyMomentRows (543 : Fin 2886) =
    keyMomentRow543 := by decide +kernel

theorem keyMomentChunkSound16_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 16) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 512 ∨ k.val = 513 ∨ k.val = 514 ∨ k.val = 515 ∨ k.val = 516 ∨ k.val = 517 ∨ k.val = 518 ∨ k.val = 519 ∨ k.val = 520 ∨ k.val = 521 ∨ k.val = 522 ∨ k.val = 523 ∨ k.val = 524 ∨ k.val = 525 ∨ k.val = 526 ∨ k.val = 527 ∨ k.val = 528 ∨ k.val = 529 ∨ k.val = 530 ∨ k.val = 531 ∨ k.val = 532 ∨ k.val = 533 ∨ k.val = 534 ∨ k.val = 535 ∨ k.val = 536 ∨ k.val = 537 ∨ k.val = 538 ∨ k.val = 539 ∨ k.val = 540 ∨ k.val = 541 ∨ k.val = 542 ∨ k.val = 543 := by omega
  rcases heq with h512 | h513 | h514 | h515 | h516 | h517 | h518 | h519 | h520 | h521 | h522 | h523 | h524 | h525 | h526 | h527 | h528 | h529 | h530 | h531 | h532 | h533 | h534 | h535 | h536 | h537 | h538 | h539 | h540 | h541 | h542 | h543
  · have he : k = (512 : Fin 2886) := Fin.ext h512
    subst k
    rw [keyMomentRowsAt512]
    exact keyMoment512 B hB
  · have he : k = (513 : Fin 2886) := Fin.ext h513
    subst k
    rw [keyMomentRowsAt513]
    exact keyMoment513 B hB
  · have he : k = (514 : Fin 2886) := Fin.ext h514
    subst k
    rw [keyMomentRowsAt514]
    exact keyMoment514 B hB
  · have he : k = (515 : Fin 2886) := Fin.ext h515
    subst k
    rw [keyMomentRowsAt515]
    exact keyMoment515 B hB
  · have he : k = (516 : Fin 2886) := Fin.ext h516
    subst k
    rw [keyMomentRowsAt516]
    exact keyMoment516 B hB
  · have he : k = (517 : Fin 2886) := Fin.ext h517
    subst k
    rw [keyMomentRowsAt517]
    exact keyMoment517 B hB
  · have he : k = (518 : Fin 2886) := Fin.ext h518
    subst k
    rw [keyMomentRowsAt518]
    exact keyMoment518 B hB
  · have he : k = (519 : Fin 2886) := Fin.ext h519
    subst k
    rw [keyMomentRowsAt519]
    exact keyMoment519 B hB
  · have he : k = (520 : Fin 2886) := Fin.ext h520
    subst k
    rw [keyMomentRowsAt520]
    exact keyMoment520 B hB
  · have he : k = (521 : Fin 2886) := Fin.ext h521
    subst k
    rw [keyMomentRowsAt521]
    exact keyMoment521 B hB
  · have he : k = (522 : Fin 2886) := Fin.ext h522
    subst k
    rw [keyMomentRowsAt522]
    exact keyMoment522 B hB
  · have he : k = (523 : Fin 2886) := Fin.ext h523
    subst k
    rw [keyMomentRowsAt523]
    exact keyMoment523 B hB
  · have he : k = (524 : Fin 2886) := Fin.ext h524
    subst k
    rw [keyMomentRowsAt524]
    exact keyMoment524 B hB
  · have he : k = (525 : Fin 2886) := Fin.ext h525
    subst k
    rw [keyMomentRowsAt525]
    exact keyMoment525 B hB
  · have he : k = (526 : Fin 2886) := Fin.ext h526
    subst k
    rw [keyMomentRowsAt526]
    exact keyMoment526 B hB
  · have he : k = (527 : Fin 2886) := Fin.ext h527
    subst k
    rw [keyMomentRowsAt527]
    exact keyMoment527 B hB
  · have he : k = (528 : Fin 2886) := Fin.ext h528
    subst k
    rw [keyMomentRowsAt528]
    exact keyMoment528 B hB
  · have he : k = (529 : Fin 2886) := Fin.ext h529
    subst k
    rw [keyMomentRowsAt529]
    exact keyMoment529 B hB
  · have he : k = (530 : Fin 2886) := Fin.ext h530
    subst k
    rw [keyMomentRowsAt530]
    exact keyMoment530 B hB
  · have he : k = (531 : Fin 2886) := Fin.ext h531
    subst k
    rw [keyMomentRowsAt531]
    exact keyMoment531 B hB
  · have he : k = (532 : Fin 2886) := Fin.ext h532
    subst k
    rw [keyMomentRowsAt532]
    exact keyMoment532 B hB
  · have he : k = (533 : Fin 2886) := Fin.ext h533
    subst k
    rw [keyMomentRowsAt533]
    exact keyMoment533 B hB
  · have he : k = (534 : Fin 2886) := Fin.ext h534
    subst k
    rw [keyMomentRowsAt534]
    exact keyMoment534 B hB
  · have he : k = (535 : Fin 2886) := Fin.ext h535
    subst k
    rw [keyMomentRowsAt535]
    exact keyMoment535 B hB
  · have he : k = (536 : Fin 2886) := Fin.ext h536
    subst k
    rw [keyMomentRowsAt536]
    exact keyMoment536 B hB
  · have he : k = (537 : Fin 2886) := Fin.ext h537
    subst k
    rw [keyMomentRowsAt537]
    exact keyMoment537 B hB
  · have he : k = (538 : Fin 2886) := Fin.ext h538
    subst k
    rw [keyMomentRowsAt538]
    exact keyMoment538 B hB
  · have he : k = (539 : Fin 2886) := Fin.ext h539
    subst k
    rw [keyMomentRowsAt539]
    exact keyMoment539 B hB
  · have he : k = (540 : Fin 2886) := Fin.ext h540
    subst k
    rw [keyMomentRowsAt540]
    exact keyMoment540 B hB
  · have he : k = (541 : Fin 2886) := Fin.ext h541
    subst k
    rw [keyMomentRowsAt541]
    exact keyMoment541 B hB
  · have he : k = (542 : Fin 2886) := Fin.ext h542
    subst k
    rw [keyMomentRowsAt542]
    exact keyMoment542 B hB
  · have he : k = (543 : Fin 2886) := Fin.ext h543
    subst k
    rw [keyMomentRowsAt543]
    exact keyMoment543 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound16_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound16_e_oai
