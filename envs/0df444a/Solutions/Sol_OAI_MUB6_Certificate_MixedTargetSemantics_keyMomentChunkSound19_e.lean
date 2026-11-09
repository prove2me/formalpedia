-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound19_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:47:53.551368+00:00
-- url     : https://prove2.me/submissions/b1266f3e-300d-4ce3-9708-037e928d9bea

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

theorem canonical40056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40056 raw40056Labels = mixedMoment B node395 node395Labels := by
  calc
    mixedMoment B raw40056 raw40056Labels = mixedMoment B raw40056step0 raw40056step0Labels := by
      have hz : ∀ j, raw40056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40056step0 = (fun i j => raw40056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40056step0 raw40056; decide +kernel
      have hl : raw40056step0Labels = raw40056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40056 raw40056Labels permutation434 hz
    mixedMoment B raw40056step0 raw40056step0Labels = mixedMoment B raw40056step1 raw40056step1Labels := by
      have ha : raw40056step1 = (fun i j => raw40056step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40056step1 raw40056step0; decide +kernel
      have hl : raw40056step1Labels = raw40056step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40056step0 raw40056step0Labels permutation33 permutation4
    mixedMoment B raw40056step1 raw40056step1Labels = mixedMoment B raw40056step2 raw40056step2Labels := by
      have ha : raw40056step2 = -raw40056step1 := by apply Matrix.ext; change ∀ i j, raw40056step2 i j = -(raw40056step1 i j); unfold raw40056step2 raw40056step1; decide +kernel
      have hl : raw40056step2Labels = raw40056step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node395 node395Labels := by rfl

theorem canonical40057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40057 raw40057Labels = mixedMoment B node394 node394Labels := by
  calc
    mixedMoment B raw40057 raw40057Labels = mixedMoment B raw40057step0 raw40057step0Labels := by
      have ha : raw40057step0 = (fun i j => raw40057 (permutation157 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40057step0 raw40057; decide +kernel
      have hl : raw40057step0Labels = raw40057Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40057 raw40057Labels permutation157 permutation4
    mixedMoment B raw40057step0 raw40057step0Labels = mixedMoment B raw40057step1 raw40057step1Labels := by
      have ha : raw40057step1 = -raw40057step0 := by apply Matrix.ext; change ∀ i j, raw40057step1 i j = -(raw40057step0 i j); unfold raw40057step1 raw40057step0; decide +kernel
      have hl : raw40057step1Labels = raw40057step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node394 node394Labels := by rfl

theorem canonical40058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40058 raw40058Labels = mixedMoment B node358 node358Labels := by
  calc
    mixedMoment B raw40058 raw40058Labels = mixedMoment B raw40058step0 raw40058step0Labels := by
      have ha : raw40058step0 = (fun i j => raw40058 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40058step0 raw40058; decide +kernel
      have hl : raw40058step0Labels = raw40058Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40058 raw40058Labels permutation246 permutation4
    mixedMoment B raw40058step0 raw40058step0Labels = mixedMoment B raw40058step1 raw40058step1Labels := by
      have ha : raw40058step1 = -raw40058step0 := by apply Matrix.ext; change ∀ i j, raw40058step1 i j = -(raw40058step0 i j); unfold raw40058step1 raw40058step0; decide +kernel
      have hl : raw40058step1Labels = raw40058step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node358 node358Labels := by rfl

theorem canonical40059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40059 raw40059Labels = mixedMoment B node357 node357Labels := by
  calc
    mixedMoment B raw40059 raw40059Labels = mixedMoment B raw40059step0 raw40059step0Labels := by
      have ha : raw40059step0 = (fun i j => raw40059 (permutation247 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40059step0 raw40059; decide +kernel
      have hl : raw40059step0Labels = raw40059Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40059 raw40059Labels permutation247 permutation4
    mixedMoment B raw40059step0 raw40059step0Labels = mixedMoment B raw40059step1 raw40059step1Labels := by
      have ha : raw40059step1 = -raw40059step0 := by apply Matrix.ext; change ∀ i j, raw40059step1 i j = -(raw40059step0 i j); unfold raw40059step1 raw40059step0; decide +kernel
      have hl : raw40059step1Labels = raw40059step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node357 node357Labels := by rfl

theorem canonical40060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40060 raw40060Labels = mixedMoment B node400 node400Labels := by
  calc
    mixedMoment B raw40060 raw40060Labels = mixedMoment B raw40060step0 raw40060step0Labels := by
      have hz : ∀ j, raw40060 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40060step0 = (fun i j => raw40060 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40060step0 raw40060; decide +kernel
      have hl : raw40060step0Labels = raw40060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40060 raw40060Labels permutation434 hz
    mixedMoment B raw40060step0 raw40060step0Labels = mixedMoment B raw40060step1 raw40060step1Labels := by
      have ha : raw40060step1 = (fun i j => raw40060step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40060step1 raw40060step0; decide +kernel
      have hl : raw40060step1Labels = raw40060step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40060step0 raw40060step0Labels permutation37 permutation4
    mixedMoment B raw40060step1 raw40060step1Labels = mixedMoment B raw40060step2 raw40060step2Labels := by
      have ha : raw40060step2 = -raw40060step1 := by apply Matrix.ext; change ∀ i j, raw40060step2 i j = -(raw40060step1 i j); unfold raw40060step2 raw40060step1; decide +kernel
      have hl : raw40060step2Labels = raw40060step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node400 node400Labels := by rfl

theorem canonical40061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40061 raw40061Labels = mixedMoment B node362 node362Labels := by
  calc
    mixedMoment B raw40061 raw40061Labels = mixedMoment B raw40061step0 raw40061step0Labels := by
      have hz : ∀ j, raw40061 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40061step0 = (fun i j => raw40061 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40061step0 raw40061; decide +kernel
      have hl : raw40061step0Labels = raw40061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40061 raw40061Labels permutation434 hz
    mixedMoment B raw40061step0 raw40061step0Labels = mixedMoment B raw40061step1 raw40061step1Labels := by
      have ha : raw40061step1 = (fun i j => raw40061step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40061step1 raw40061step0; decide +kernel
      have hl : raw40061step1Labels = raw40061step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40061step0 raw40061step0Labels permutation50 permutation4
    mixedMoment B raw40061step1 raw40061step1Labels = mixedMoment B raw40061step2 raw40061step2Labels := by
      have ha : raw40061step2 = -raw40061step1 := by apply Matrix.ext; change ∀ i j, raw40061step2 i j = -(raw40061step1 i j); unfold raw40061step2 raw40061step1; decide +kernel
      have hl : raw40061step2Labels = raw40061step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node362 node362Labels := by rfl

theorem canonical40062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40062 raw40062Labels = mixedMoment B node359 node359Labels := by
  calc
    mixedMoment B raw40062 raw40062Labels = mixedMoment B raw40062step0 raw40062step0Labels := by
      have ha : raw40062step0 = (fun i j => raw40062 (permutation251 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40062step0 raw40062; decide +kernel
      have hl : raw40062step0Labels = raw40062Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40062 raw40062Labels permutation251 permutation4
    mixedMoment B raw40062step0 raw40062step0Labels = mixedMoment B raw40062step1 raw40062step1Labels := by
      have ha : raw40062step1 = -raw40062step0 := by apply Matrix.ext; change ∀ i j, raw40062step1 i j = -(raw40062step0 i j); unfold raw40062step1 raw40062step0; decide +kernel
      have hl : raw40062step1Labels = raw40062step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node359 node359Labels := by rfl

theorem canonical40063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40063 raw40063Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw40063 raw40063Labels = mixedMoment B raw40063step0 raw40063step0Labels := by
      have hz : ∀ j, raw40063 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40063step0 = (fun i j => raw40063 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40063step0 raw40063; decide +kernel
      have hl : raw40063step0Labels = raw40063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40063 raw40063Labels permutation434 hz
    mixedMoment B raw40063step0 raw40063step0Labels = mixedMoment B raw40063step1 raw40063step1Labels := by
      have hz : ∀ j, raw40063step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40063step1 = (fun i j => raw40063step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40063step1 raw40063step0; decide +kernel
      have hl : raw40063step1Labels = raw40063step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40063step0 raw40063step0Labels permutation80 hz
    mixedMoment B raw40063step1 raw40063step1Labels = mixedMoment B raw40063step2 raw40063step2Labels := by
      have ha : raw40063step2 = (fun i j => raw40063step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40063step2 raw40063step1; decide +kernel
      have hl : raw40063step2Labels = raw40063step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40063step1 raw40063step1Labels permutation8 permutation4
    mixedMoment B raw40063step2 raw40063step2Labels = mixedMoment B raw40063step3 raw40063step3Labels := by
      have ha : raw40063step3 = -raw40063step2 := by apply Matrix.ext; change ∀ i j, raw40063step3 i j = -(raw40063step2 i j); unfold raw40063step3 raw40063step2; decide +kernel
      have hl : raw40063step3Labels = raw40063step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node404 node404Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical313
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40064 raw40064Labels = mixedMoment B node401 node401Labels := by
  calc
    mixedMoment B raw40064 raw40064Labels = mixedMoment B raw40064step0 raw40064step0Labels := by
      have hz : ∀ j, raw40064 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40064step0 = (fun i j => raw40064 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40064step0 raw40064; decide +kernel
      have hl : raw40064step0Labels = raw40064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40064 raw40064Labels permutation346 hz
    mixedMoment B raw40064step0 raw40064step0Labels = mixedMoment B raw40064step1 raw40064step1Labels := by
      have ha : raw40064step1 = (fun i j => raw40064step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40064step1 raw40064step0; decide +kernel
      have hl : raw40064step1Labels = raw40064step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40064step0 raw40064step0Labels permutation36 permutation4
    mixedMoment B raw40064step1 raw40064step1Labels = mixedMoment B raw40064step2 raw40064step2Labels := by
      have ha : raw40064step2 = -raw40064step1 := by apply Matrix.ext; change ∀ i j, raw40064step2 i j = -(raw40064step1 i j); unfold raw40064step2 raw40064step1; decide +kernel
      have hl : raw40064step2Labels = raw40064step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node401 node401Labels := by rfl

theorem canonical40065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40065 raw40065Labels = mixedMoment B node361 node361Labels := by
  calc
    mixedMoment B raw40065 raw40065Labels = mixedMoment B raw40065step0 raw40065step0Labels := by
      have hz : ∀ j, raw40065 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40065step0 = (fun i j => raw40065 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40065step0 raw40065; decide +kernel
      have hl : raw40065step0Labels = raw40065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40065 raw40065Labels permutation346 hz
    mixedMoment B raw40065step0 raw40065step0Labels = mixedMoment B raw40065step1 raw40065step1Labels := by
      have ha : raw40065step1 = (fun i j => raw40065step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40065step1 raw40065step0; decide +kernel
      have hl : raw40065step1Labels = raw40065step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40065step0 raw40065step0Labels permutation50 permutation4
    mixedMoment B raw40065step1 raw40065step1Labels = mixedMoment B raw40065step2 raw40065step2Labels := by
      have ha : raw40065step2 = -raw40065step1 := by apply Matrix.ext; change ∀ i j, raw40065step2 i j = -(raw40065step1 i j); unfold raw40065step2 raw40065step1; decide +kernel
      have hl : raw40065step2Labels = raw40065step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node361 node361Labels := by rfl

theorem canonical40066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40066 raw40066Labels = mixedMoment B node378 node378Labels := by
  calc
    mixedMoment B raw40066 raw40066Labels = mixedMoment B raw40066step0 raw40066step0Labels := by
      have hz : ∀ j, raw40066 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40066step0 = (fun i j => raw40066 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40066step0 raw40066; decide +kernel
      have hl : raw40066step0Labels = raw40066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40066 raw40066Labels permutation346 hz
    mixedMoment B raw40066step0 raw40066step0Labels = mixedMoment B raw40066step1 raw40066step1Labels := by
      have ha : raw40066step1 = (fun i j => raw40066step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40066step1 raw40066step0; decide +kernel
      have hl : raw40066step1Labels = raw40066step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40066step0 raw40066step0Labels permutation44 permutation4
    mixedMoment B raw40066step1 raw40066step1Labels = mixedMoment B raw40066step2 raw40066step2Labels := by
      have ha : raw40066step2 = -raw40066step1 := by apply Matrix.ext; change ∀ i j, raw40066step2 i j = -(raw40066step1 i j); unfold raw40066step2 raw40066step1; decide +kernel
      have hl : raw40066step2Labels = raw40066step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node378 node378Labels := by rfl

theorem canonical40067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40067 raw40067Labels = mixedMoment B node403 node403Labels := by
  calc
    mixedMoment B raw40067 raw40067Labels = mixedMoment B raw40067step0 raw40067step0Labels := by
      have hz : ∀ j, raw40067 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40067step0 = (fun i j => raw40067 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40067step0 raw40067; decide +kernel
      have hl : raw40067step0Labels = raw40067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40067 raw40067Labels permutation346 hz
    mixedMoment B raw40067step0 raw40067step0Labels = mixedMoment B raw40067step1 raw40067step1Labels := by
      have ha : raw40067step1 = (fun i j => raw40067step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40067step1 raw40067step0; decide +kernel
      have hl : raw40067step1Labels = raw40067step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40067step0 raw40067step0Labels permutation35 permutation4
    mixedMoment B raw40067step1 raw40067step1Labels = mixedMoment B raw40067step2 raw40067step2Labels := by
      have ha : raw40067step2 = -raw40067step1 := by apply Matrix.ext; change ∀ i j, raw40067step2 i j = -(raw40067step1 i j); unfold raw40067step2 raw40067step1; decide +kernel
      have hl : raw40067step2Labels = raw40067step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node403 node403Labels := by rfl

theorem canonical40068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40068 raw40068Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw40068 raw40068Labels = mixedMoment B raw40068step0 raw40068step0Labels := by
      have hz : ∀ j, raw40068 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40068step0 = (fun i j => raw40068 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40068step0 raw40068; decide +kernel
      have hl : raw40068step0Labels = raw40068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40068 raw40068Labels permutation346 hz
    mixedMoment B raw40068step0 raw40068step0Labels = mixedMoment B raw40068step1 raw40068step1Labels := by
      have ha : raw40068step1 = (fun i j => raw40068step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40068step1 raw40068step0; decide +kernel
      have hl : raw40068step1Labels = raw40068step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40068step0 raw40068step0Labels permutation45 permutation4
    mixedMoment B raw40068step1 raw40068step1Labels = mixedMoment B raw40068step2 raw40068step2Labels := by
      have ha : raw40068step2 = -raw40068step1 := by apply Matrix.ext; change ∀ i j, raw40068step2 i j = -(raw40068step1 i j); unfold raw40068step2 raw40068step1; decide +kernel
      have hl : raw40068step2Labels = raw40068step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node377 node377Labels := by rfl

theorem canonical40069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40069 raw40069Labels = mixedMoment B node360 node360Labels := by
  calc
    mixedMoment B raw40069 raw40069Labels = mixedMoment B raw40069step0 raw40069step0Labels := by
      have ha : raw40069step0 = (fun i j => raw40069 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40069step0 raw40069; decide +kernel
      have hl : raw40069step0Labels = raw40069Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40069 raw40069Labels permutation246 permutation4
    mixedMoment B raw40069step0 raw40069step0Labels = mixedMoment B raw40069step1 raw40069step1Labels := by
      have ha : raw40069step1 = -raw40069step0 := by apply Matrix.ext; change ∀ i j, raw40069step1 i j = -(raw40069step0 i j); unfold raw40069step1 raw40069step0; decide +kernel
      have hl : raw40069step1Labels = raw40069step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node360 node360Labels := by rfl

theorem canonical40070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40070 raw40070Labels = mixedMoment B node376 node376Labels := by
  calc
    mixedMoment B raw40070 raw40070Labels = mixedMoment B raw40070step0 raw40070step0Labels := by
      have ha : raw40070step0 = (fun i j => raw40070 (permutation228 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40070step0 raw40070; decide +kernel
      have hl : raw40070step0Labels = raw40070Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40070 raw40070Labels permutation228 permutation4
    mixedMoment B raw40070step0 raw40070step0Labels = mixedMoment B raw40070step1 raw40070step1Labels := by
      have ha : raw40070step1 = -raw40070step0 := by apply Matrix.ext; change ∀ i j, raw40070step1 i j = -(raw40070step0 i j); unfold raw40070step1 raw40070step0; decide +kernel
      have hl : raw40070step1Labels = raw40070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node376 node376Labels := by rfl

theorem canonical40071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40071 raw40071Labels = mixedMoment B node367 node367Labels := by
  calc
    mixedMoment B raw40071 raw40071Labels = mixedMoment B raw40071step0 raw40071step0Labels := by
      have hz : ∀ j, raw40071 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40071step0 = (fun i j => raw40071 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40071step0 raw40071; decide +kernel
      have hl : raw40071step0Labels = raw40071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40071 raw40071Labels permutation434 hz
    mixedMoment B raw40071step0 raw40071step0Labels = mixedMoment B raw40071step1 raw40071step1Labels := by
      have ha : raw40071step1 = (fun i j => raw40071step0 (permutation54 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40071step1 raw40071step0; decide +kernel
      have hl : raw40071step1Labels = raw40071step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40071step0 raw40071step0Labels permutation54 permutation4
    mixedMoment B raw40071step1 raw40071step1Labels = mixedMoment B raw40071step2 raw40071step2Labels := by
      have ha : raw40071step2 = -raw40071step1 := by apply Matrix.ext; change ∀ i j, raw40071step2 i j = -(raw40071step1 i j); unfold raw40071step2 raw40071step1; decide +kernel
      have hl : raw40071step2Labels = raw40071step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node367 node367Labels := by rfl

theorem canonical40072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40072 raw40072Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw40072 raw40072Labels = mixedMoment B raw40072step0 raw40072step0Labels := by
      have hz : ∀ j, raw40072 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40072step0 = (fun i j => raw40072 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40072step0 raw40072; decide +kernel
      have hl : raw40072step0Labels = raw40072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40072 raw40072Labels permutation520 hz
    mixedMoment B raw40072step0 raw40072step0Labels = mixedMoment B raw40072step1 raw40072step1Labels := by
      have hz : ∀ j, raw40072step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40072step1 = (fun i j => raw40072step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40072step1 raw40072step0; decide +kernel
      have hl : raw40072step1Labels = raw40072step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40072step0 raw40072step0Labels permutation104 hz
    mixedMoment B raw40072step1 raw40072step1Labels = mixedMoment B raw40072step2 raw40072step2Labels := by
      have hz : ∀ j, raw40072step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40072step2 = (fun i j => raw40072step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40072step2 raw40072step1; decide +kernel
      have hl : raw40072step2Labels = raw40072step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40072step1 raw40072step1Labels permutation20 hz
    mixedMoment B raw40072step2 raw40072step2Labels = mixedMoment B raw40072step3 raw40072step3Labels := by
      have ha : raw40072step3 = (fun i j => raw40072step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40072step3 raw40072step2; decide +kernel
      have hl : raw40072step3Labels = raw40072step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40072step2 raw40072step2Labels permutation2 permutation4
    mixedMoment B raw40072step3 raw40072step3Labels = mixedMoment B raw40072step4 raw40072step4Labels := by
      have ha : raw40072step4 = -raw40072step3 := by apply Matrix.ext; change ∀ i j, raw40072step4 i j = -(raw40072step3 i j); unfold raw40072step4 raw40072step3; decide +kernel
      have hl : raw40072step4Labels = raw40072step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node420 node420Labels := by rfl

theorem canonical40073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40073 raw40073Labels = mixedMoment B node414 node414Labels := by
  calc
    mixedMoment B raw40073 raw40073Labels = mixedMoment B raw40073step0 raw40073step0Labels := by
      have hz : ∀ j, raw40073 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40073step0 = (fun i j => raw40073 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40073step0 raw40073; decide +kernel
      have hl : raw40073step0Labels = raw40073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40073 raw40073Labels permutation434 hz
    mixedMoment B raw40073step0 raw40073step0Labels = mixedMoment B raw40073step1 raw40073step1Labels := by
      have hz : ∀ j, raw40073step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40073step1 = (fun i j => raw40073step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40073step1 raw40073step0; decide +kernel
      have hl : raw40073step1Labels = raw40073step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40073step0 raw40073step0Labels permutation80 hz
    mixedMoment B raw40073step1 raw40073step1Labels = mixedMoment B raw40073step2 raw40073step2Labels := by
      have ha : raw40073step2 = (fun i j => raw40073step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40073step2 raw40073step1; decide +kernel
      have hl : raw40073step2Labels = raw40073step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40073step1 raw40073step1Labels permutation13 permutation4
    mixedMoment B raw40073step2 raw40073step2Labels = mixedMoment B raw40073step3 raw40073step3Labels := by
      have ha : raw40073step3 = -raw40073step2 := by apply Matrix.ext; change ∀ i j, raw40073step3 i j = -(raw40073step2 i j); unfold raw40073step3 raw40073step2; decide +kernel
      have hl : raw40073step3Labels = raw40073step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node414 node414Labels := by rfl

theorem canonical40074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40074 raw40074Labels = mixedMoment B node369 node369Labels := by
  calc
    mixedMoment B raw40074 raw40074Labels = mixedMoment B raw40074step0 raw40074step0Labels := by
      have hz : ∀ j, raw40074 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40074step0 = (fun i j => raw40074 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40074step0 raw40074; decide +kernel
      have hl : raw40074step0Labels = raw40074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40074 raw40074Labels permutation434 hz
    mixedMoment B raw40074step0 raw40074step0Labels = mixedMoment B raw40074step1 raw40074step1Labels := by
      have hz : ∀ j, raw40074step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40074step1 = (fun i j => raw40074step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40074step1 raw40074step0; decide +kernel
      have hl : raw40074step1Labels = raw40074step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40074step0 raw40074step0Labels permutation80 hz
    mixedMoment B raw40074step1 raw40074step1Labels = mixedMoment B raw40074step2 raw40074step2Labels := by
      have ha : raw40074step2 = (fun i j => raw40074step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40074step2 raw40074step1; decide +kernel
      have hl : raw40074step2Labels = raw40074step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40074step1 raw40074step1Labels permutation12 permutation4
    mixedMoment B raw40074step2 raw40074step2Labels = mixedMoment B raw40074step3 raw40074step3Labels := by
      have ha : raw40074step3 = -raw40074step2 := by apply Matrix.ext; change ∀ i j, raw40074step3 i j = -(raw40074step2 i j); unfold raw40074step3 raw40074step2; decide +kernel
      have hl : raw40074step3Labels = raw40074step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node369 node369Labels := by rfl

theorem canonical40075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40075 raw40075Labels = mixedMoment B node390 node390Labels := by
  calc
    mixedMoment B raw40075 raw40075Labels = mixedMoment B raw40075step0 raw40075step0Labels := by
      have hz : ∀ j, raw40075 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40075step0 = (fun i j => raw40075 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40075step0 raw40075; decide +kernel
      have hl : raw40075step0Labels = raw40075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40075 raw40075Labels permutation434 hz
    mixedMoment B raw40075step0 raw40075step0Labels = mixedMoment B raw40075step1 raw40075step1Labels := by
      have hz : ∀ j, raw40075step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40075step1 = (fun i j => raw40075step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40075step1 raw40075step0; decide +kernel
      have hl : raw40075step1Labels = raw40075step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40075step0 raw40075step0Labels permutation80 hz
    mixedMoment B raw40075step1 raw40075step1Labels = mixedMoment B raw40075step2 raw40075step2Labels := by
      have ha : raw40075step2 = (fun i j => raw40075step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40075step2 raw40075step1; decide +kernel
      have hl : raw40075step2Labels = raw40075step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40075step1 raw40075step1Labels permutation10 permutation4
    mixedMoment B raw40075step2 raw40075step2Labels = mixedMoment B raw40075step3 raw40075step3Labels := by
      have ha : raw40075step3 = -raw40075step2 := by apply Matrix.ext; change ∀ i j, raw40075step3 i j = -(raw40075step2 i j); unfold raw40075step3 raw40075step2; decide +kernel
      have hl : raw40075step3Labels = raw40075step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node390 node390Labels := by rfl

theorem canonical40076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40076 raw40076Labels = mixedMoment B node416 node416Labels := by
  calc
    mixedMoment B raw40076 raw40076Labels = mixedMoment B raw40076step0 raw40076step0Labels := by
      have hz : ∀ j, raw40076 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40076step0 = (fun i j => raw40076 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40076step0 raw40076; decide +kernel
      have hl : raw40076step0Labels = raw40076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40076 raw40076Labels permutation434 hz
    mixedMoment B raw40076step0 raw40076step0Labels = mixedMoment B raw40076step1 raw40076step1Labels := by
      have hz : ∀ j, raw40076step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40076step1 = (fun i j => raw40076step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40076step1 raw40076step0; decide +kernel
      have hl : raw40076step1Labels = raw40076step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40076step0 raw40076step0Labels permutation80 hz
    mixedMoment B raw40076step1 raw40076step1Labels = mixedMoment B raw40076step2 raw40076step2Labels := by
      have ha : raw40076step2 = (fun i j => raw40076step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40076step2 raw40076step1; decide +kernel
      have hl : raw40076step2Labels = raw40076step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40076step1 raw40076step1Labels permutation11 permutation4
    mixedMoment B raw40076step2 raw40076step2Labels = mixedMoment B raw40076step3 raw40076step3Labels := by
      have ha : raw40076step3 = -raw40076step2 := by apply Matrix.ext; change ∀ i j, raw40076step3 i j = -(raw40076step2 i j); unfold raw40076step3 raw40076step2; decide +kernel
      have hl : raw40076step3Labels = raw40076step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node416 node416Labels := by rfl

theorem canonical40077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40077 raw40077Labels = mixedMoment B node368 node368Labels := by
  calc
    mixedMoment B raw40077 raw40077Labels = mixedMoment B raw40077step0 raw40077step0Labels := by
      have hz : ∀ j, raw40077 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40077step0 = (fun i j => raw40077 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40077step0 raw40077; decide +kernel
      have hl : raw40077step0Labels = raw40077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40077 raw40077Labels permutation346 hz
    mixedMoment B raw40077step0 raw40077step0Labels = mixedMoment B raw40077step1 raw40077step1Labels := by
      have ha : raw40077step1 = (fun i j => raw40077step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40077step1 raw40077step0; decide +kernel
      have hl : raw40077step1Labels = raw40077step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40077step0 raw40077step0Labels permutation53 permutation4
    mixedMoment B raw40077step1 raw40077step1Labels = mixedMoment B raw40077step2 raw40077step2Labels := by
      have ha : raw40077step2 = -raw40077step1 := by apply Matrix.ext; change ∀ i j, raw40077step2 i j = -(raw40077step1 i j); unfold raw40077step2 raw40077step1; decide +kernel
      have hl : raw40077step2Labels = raw40077step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node368 node368Labels := by rfl

theorem canonical40078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40078 raw40078Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw40078 raw40078Labels = mixedMoment B raw40078step0 raw40078step0Labels := by
      have hz : ∀ j, raw40078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40078step0 = (fun i j => raw40078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40078step0 raw40078; decide +kernel
      have hl : raw40078step0Labels = raw40078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40078 raw40078Labels permutation346 hz
    mixedMoment B raw40078step0 raw40078step0Labels = mixedMoment B raw40078step1 raw40078step1Labels := by
      have ha : raw40078step1 = (fun i j => raw40078step0 (permutation49 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40078step1 raw40078step0; decide +kernel
      have hl : raw40078step1Labels = raw40078step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40078step0 raw40078step0Labels permutation49 permutation4
    mixedMoment B raw40078step1 raw40078step1Labels = mixedMoment B raw40078step2 raw40078step2Labels := by
      have ha : raw40078step2 = -raw40078step1 := by apply Matrix.ext; change ∀ i j, raw40078step2 i j = -(raw40078step1 i j); unfold raw40078step2 raw40078step1; decide +kernel
      have hl : raw40078step2Labels = raw40078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node387 node387Labels := by rfl

theorem canonical40079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40079 raw40079Labels = mixedMoment B node371 node371Labels := by
  calc
    mixedMoment B raw40079 raw40079Labels = mixedMoment B raw40079step0 raw40079step0Labels := by
      have ha : raw40079step0 = (fun i j => raw40079 (permutation243 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40079step0 raw40079; decide +kernel
      have hl : raw40079step0Labels = raw40079Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40079 raw40079Labels permutation243 permutation4
    mixedMoment B raw40079step0 raw40079step0Labels = mixedMoment B raw40079step1 raw40079step1Labels := by
      have ha : raw40079step1 = -raw40079step0 := by apply Matrix.ext; change ∀ i j, raw40079step1 i j = -(raw40079step0 i j); unfold raw40079step1 raw40079step0; decide +kernel
      have hl : raw40079step1Labels = raw40079step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node371 node371Labels := by rfl

theorem canonical40080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40080 raw40080Labels = mixedMoment B node415 node415Labels := by
  calc
    mixedMoment B raw40080 raw40080Labels = mixedMoment B raw40080step0 raw40080step0Labels := by
      have hz : ∀ j, raw40080 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40080step0 = (fun i j => raw40080 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40080step0 raw40080; decide +kernel
      have hl : raw40080step0Labels = raw40080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40080 raw40080Labels permutation520 hz
    mixedMoment B raw40080step0 raw40080step0Labels = mixedMoment B raw40080step1 raw40080step1Labels := by
      have hz : ∀ j, raw40080step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40080step1 = (fun i j => raw40080step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40080step1 raw40080step0; decide +kernel
      have hl : raw40080step1Labels = raw40080step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40080step0 raw40080step0Labels permutation104 hz
    mixedMoment B raw40080step1 raw40080step1Labels = mixedMoment B raw40080step2 raw40080step2Labels := by
      have hz : ∀ j, raw40080step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40080step2 = (fun i j => raw40080step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40080step2 raw40080step1; decide +kernel
      have hl : raw40080step2Labels = raw40080step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40080step1 raw40080step1Labels permutation20 hz
    mixedMoment B raw40080step2 raw40080step2Labels = mixedMoment B raw40080step3 raw40080step3Labels := by
      have ha : raw40080step3 = (fun i j => raw40080step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40080step3 raw40080step2; decide +kernel
      have hl : raw40080step3Labels = raw40080step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40080step2 raw40080step2Labels permutation3 permutation4
    mixedMoment B raw40080step3 raw40080step3Labels = mixedMoment B raw40080step4 raw40080step4Labels := by
      have ha : raw40080step4 = -raw40080step3 := by apply Matrix.ext; change ∀ i j, raw40080step4 i j = -(raw40080step3 i j); unfold raw40080step4 raw40080step3; decide +kernel
      have hl : raw40080step4Labels = raw40080step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node415 node415Labels := by rfl

theorem canonical40081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40081 raw40081Labels = mixedMoment B node316 node316Labels := by
  calc
    mixedMoment B raw40081 raw40081Labels = mixedMoment B raw40081step0 raw40081step0Labels := by
      have hz : ∀ j, raw40081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40081step0 = (fun i j => raw40081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40081step0 raw40081; decide +kernel
      have hl : raw40081step0Labels = raw40081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40081 raw40081Labels permutation434 hz
    mixedMoment B raw40081step0 raw40081step0Labels = mixedMoment B raw40081step1 raw40081step1Labels := by
      have hz : ∀ j, raw40081step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40081step1 = (fun i j => raw40081step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40081step1 raw40081step0; decide +kernel
      have hl : raw40081step1Labels = raw40081step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40081step0 raw40081step0Labels permutation80 hz
    mixedMoment B raw40081step1 raw40081step1Labels = mixedMoment B raw40081step2 raw40081step2Labels := by
      have ha : raw40081step2 = (fun i j => raw40081step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40081step2 raw40081step1; decide +kernel
      have hl : raw40081step2Labels = raw40081step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40081step1 raw40081step1Labels permutation17 permutation6
    mixedMoment B raw40081step2 raw40081step2Labels = mixedMoment B raw40081step3 raw40081step3Labels := by
      have ha : raw40081step3 = -raw40081step2 := by apply Matrix.ext; change ∀ i j, raw40081step3 i j = -(raw40081step2 i j); unfold raw40081step3 raw40081step2; decide +kernel
      have hl : raw40081step3Labels = raw40081step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node316 node316Labels := by rfl

theorem canonical40082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40082 raw40082Labels = mixedMoment B node388 node388Labels := by
  calc
    mixedMoment B raw40082 raw40082Labels = mixedMoment B raw40082step0 raw40082step0Labels := by
      have hz : ∀ j, raw40082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40082step0 = (fun i j => raw40082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40082step0 raw40082; decide +kernel
      have hl : raw40082step0Labels = raw40082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40082 raw40082Labels permutation434 hz
    mixedMoment B raw40082step0 raw40082step0Labels = mixedMoment B raw40082step1 raw40082step1Labels := by
      have hz : ∀ j, raw40082step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40082step1 = (fun i j => raw40082step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40082step1 raw40082step0; decide +kernel
      have hl : raw40082step1Labels = raw40082step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40082step0 raw40082step0Labels permutation80 hz
    mixedMoment B raw40082step1 raw40082step1Labels = mixedMoment B raw40082step2 raw40082step2Labels := by
      have ha : raw40082step2 = (fun i j => raw40082step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40082step2 raw40082step1; decide +kernel
      have hl : raw40082step2Labels = raw40082step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40082step1 raw40082step1Labels permutation11 permutation4
    mixedMoment B raw40082step2 raw40082step2Labels = mixedMoment B raw40082step3 raw40082step3Labels := by
      have ha : raw40082step3 = -raw40082step2 := by apply Matrix.ext; change ∀ i j, raw40082step3 i j = -(raw40082step2 i j); unfold raw40082step3 raw40082step2; decide +kernel
      have hl : raw40082step3Labels = raw40082step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node388 node388Labels := by rfl

theorem canonical40083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40083 raw40083Labels = mixedMoment B node113 node113Labels := by
  calc
    mixedMoment B raw40083 raw40083Labels = mixedMoment B raw40083step0 raw40083step0Labels := by
      have hz : ∀ j, raw40083 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40083step0 = (fun i j => raw40083 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40083step0 raw40083; decide +kernel
      have hl : raw40083step0Labels = raw40083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40083 raw40083Labels permutation520 hz
    mixedMoment B raw40083step0 raw40083step0Labels = mixedMoment B raw40083step1 raw40083step1Labels := by
      have hz : ∀ j, raw40083step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40083step1 = (fun i j => raw40083step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40083step1 raw40083step0; decide +kernel
      have hl : raw40083step1Labels = raw40083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40083step0 raw40083step0Labels permutation104 hz
    mixedMoment B raw40083step1 raw40083step1Labels = mixedMoment B raw40083step2 raw40083step2Labels := by
      have hz : ∀ j, raw40083step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40083step2 = (fun i j => raw40083step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40083step2 raw40083step1; decide +kernel
      have hl : raw40083step2Labels = raw40083step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40083step1 raw40083step1Labels permutation20 hz
    mixedMoment B raw40083step2 raw40083step2Labels = mixedMoment B raw40083step3 raw40083step3Labels := by
      have ha : raw40083step3 = (fun i j => raw40083step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40083step3 raw40083step2; decide +kernel
      have hl : raw40083step3Labels = raw40083step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40083step2 raw40083step2Labels permutation5 permutation6
    mixedMoment B raw40083step3 raw40083step3Labels = mixedMoment B raw40083step4 raw40083step4Labels := by
      have ha : raw40083step4 = -raw40083step3 := by apply Matrix.ext; change ∀ i j, raw40083step4 i j = -(raw40083step3 i j); unfold raw40083step4 raw40083step3; decide +kernel
      have hl : raw40083step4Labels = raw40083step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node113 node113Labels := by rfl

theorem canonical40084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40084 raw40084Labels = mixedMoment B node5506 node5506Labels := by
  calc
    mixedMoment B raw40084 raw40084Labels = mixedMoment B raw40084step0 raw40084step0Labels := by
      have hz : ∀ j, raw40084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40084step0 = (fun i j => raw40084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40084step0 raw40084; decide +kernel
      have hl : raw40084step0Labels = raw40084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40084 raw40084Labels permutation434 hz
    mixedMoment B raw40084step0 raw40084step0Labels = mixedMoment B raw40084step1 raw40084step1Labels := by
      have hz : ∀ j, raw40084step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40084step1 = (fun i j => raw40084step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40084step1 raw40084step0; decide +kernel
      have hl : raw40084step1Labels = raw40084step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40084step0 raw40084step0Labels permutation80 hz
    mixedMoment B raw40084step1 raw40084step1Labels = mixedMoment B raw40084step2 raw40084step2Labels := by
      have ha : raw40084step2 = (fun i j => raw40084step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw40084step2 raw40084step1; decide +kernel
      have hl : raw40084step2Labels = raw40084step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40084step1 raw40084step1Labels permutation31 permutation5
    _ = mixedMoment B node5506 node5506Labels := by rfl

theorem canonical40085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40085 raw40085Labels = mixedMoment B node489 node489Labels := by
  calc
    mixedMoment B raw40085 raw40085Labels = mixedMoment B raw40085step0 raw40085step0Labels := by
      have hz : ∀ j, raw40085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40085step0 = (fun i j => raw40085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40085step0 raw40085; decide +kernel
      have hl : raw40085step0Labels = raw40085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40085 raw40085Labels permutation346 hz
    mixedMoment B raw40085step0 raw40085step0Labels = mixedMoment B raw40085step1 raw40085step1Labels := by
      have ha : raw40085step1 = (fun i j => raw40085step0 (permutation103 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40085step1 raw40085step0; decide +kernel
      have hl : raw40085step1Labels = raw40085step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40085step0 raw40085step0Labels permutation103 permutation4
    _ = mixedMoment B node489 node489Labels := by rfl

theorem canonical40086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40086 raw40086Labels = mixedMoment B node521 node521Labels := by
  calc
    mixedMoment B raw40086 raw40086Labels = mixedMoment B raw40086step0 raw40086step0Labels := by
      have hz : ∀ j, raw40086 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40086step0 = (fun i j => raw40086 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40086step0 raw40086; decide +kernel
      have hl : raw40086step0Labels = raw40086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40086 raw40086Labels permutation434 hz
    mixedMoment B raw40086step0 raw40086step0Labels = mixedMoment B raw40086step1 raw40086step1Labels := by
      have ha : raw40086step1 = (fun i j => raw40086step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40086step1 raw40086step0; decide +kernel
      have hl : raw40086step1Labels = raw40086step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40086step0 raw40086step0Labels permutation38 permutation4
    mixedMoment B raw40086step1 raw40086step1Labels = mixedMoment B raw40086step2 raw40086step2Labels := by
      have ha : raw40086step2 = -raw40086step1 := by apply Matrix.ext; change ∀ i j, raw40086step2 i j = -(raw40086step1 i j); unfold raw40086step2 raw40086step1; decide +kernel
      have hl : raw40086step2Labels = raw40086step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node521 node521Labels := by rfl

theorem canonical40087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40087 raw40087Labels = mixedMoment B node518 node518Labels := by
  calc
    mixedMoment B raw40087 raw40087Labels = mixedMoment B raw40087step0 raw40087step0Labels := by
      have ha : raw40087step0 = (fun i j => raw40087 (permutation654 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40087step0 raw40087; decide +kernel
      have hl : raw40087step0Labels = raw40087Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40087 raw40087Labels permutation654 permutation4
    _ = mixedMoment B node518 node518Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 608) =
      Integer.Sparse.eval keyMomentRow608 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 608).leftCharge (GramAssembly.key 608).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 395) := by
    have ha : gramCharges (GramAssembly.key 608).leftCharge (GramAssembly.key 608).rightCharge = raw40056 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40056Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40056 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 608).leftCharge (GramAssembly.key 608).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow608, Integer.Sparse.eval]

theorem keyMoment609 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 609) =
      Integer.Sparse.eval keyMomentRow609 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 609).leftCharge (GramAssembly.key 609).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 394) := by
    have ha : gramCharges (GramAssembly.key 609).leftCharge (GramAssembly.key 609).rightCharge = raw40057 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40057Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40057 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 609).leftCharge (GramAssembly.key 609).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow609, Integer.Sparse.eval]

theorem keyMoment610 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 610) =
      Integer.Sparse.eval keyMomentRow610 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 610).leftCharge (GramAssembly.key 610).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 358) := by
    have ha : gramCharges (GramAssembly.key 610).leftCharge (GramAssembly.key 610).rightCharge = raw40058 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40058Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40058 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 610).leftCharge (GramAssembly.key 610).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow610, Integer.Sparse.eval]

theorem keyMoment611 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 611) =
      Integer.Sparse.eval keyMomentRow611 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 611).leftCharge (GramAssembly.key 611).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 357) := by
    have ha : gramCharges (GramAssembly.key 611).leftCharge (GramAssembly.key 611).rightCharge = raw40059 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40059Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40059 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 611).leftCharge (GramAssembly.key 611).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow611, Integer.Sparse.eval]

theorem keyMoment612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 612) =
      Integer.Sparse.eval keyMomentRow612 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 612).leftCharge (GramAssembly.key 612).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 400) := by
    have ha : gramCharges (GramAssembly.key 612).leftCharge (GramAssembly.key 612).rightCharge = raw40060 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40060Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40060 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 612).leftCharge (GramAssembly.key 612).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow612, Integer.Sparse.eval]

theorem keyMoment613 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 613) =
      Integer.Sparse.eval keyMomentRow613 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 613).leftCharge (GramAssembly.key 613).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 362) := by
    have ha : gramCharges (GramAssembly.key 613).leftCharge (GramAssembly.key 613).rightCharge = raw40061 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40061Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40061 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 613).leftCharge (GramAssembly.key 613).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow613, Integer.Sparse.eval]

theorem keyMoment614 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 614) =
      Integer.Sparse.eval keyMomentRow614 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 614).leftCharge (GramAssembly.key 614).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 359) := by
    have ha : gramCharges (GramAssembly.key 614).leftCharge (GramAssembly.key 614).rightCharge = raw40062 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40062Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40062 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 614).leftCharge (GramAssembly.key 614).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow614, Integer.Sparse.eval]

theorem keyMoment615 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 615) =
      Integer.Sparse.eval keyMomentRow615 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 615).leftCharge (GramAssembly.key 615).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 404) := by
    have ha : gramCharges (GramAssembly.key 615).leftCharge (GramAssembly.key 615).rightCharge = raw40063 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40063Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40063 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 615).leftCharge (GramAssembly.key 615).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow615, Integer.Sparse.eval]

theorem keyMoment616 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 616) =
      Integer.Sparse.eval keyMomentRow616 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 616).leftCharge (GramAssembly.key 616).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 401) := by
    have ha : gramCharges (GramAssembly.key 616).leftCharge (GramAssembly.key 616).rightCharge = raw40064 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40064Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40064 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 616).leftCharge (GramAssembly.key 616).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow616, Integer.Sparse.eval]

theorem keyMoment617 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 617) =
      Integer.Sparse.eval keyMomentRow617 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 617).leftCharge (GramAssembly.key 617).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 361) := by
    have ha : gramCharges (GramAssembly.key 617).leftCharge (GramAssembly.key 617).rightCharge = raw40065 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40065Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40065 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 617).leftCharge (GramAssembly.key 617).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow617, Integer.Sparse.eval]

theorem keyMoment618 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 618) =
      Integer.Sparse.eval keyMomentRow618 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 618).leftCharge (GramAssembly.key 618).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 378) := by
    have ha : gramCharges (GramAssembly.key 618).leftCharge (GramAssembly.key 618).rightCharge = raw40066 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40066Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40066 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 618).leftCharge (GramAssembly.key 618).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow618, Integer.Sparse.eval]

theorem keyMoment619 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 619) =
      Integer.Sparse.eval keyMomentRow619 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 619).leftCharge (GramAssembly.key 619).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 403) := by
    have ha : gramCharges (GramAssembly.key 619).leftCharge (GramAssembly.key 619).rightCharge = raw40067 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40067Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40067 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 619).leftCharge (GramAssembly.key 619).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow619, Integer.Sparse.eval]

theorem keyMoment620 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 620) =
      Integer.Sparse.eval keyMomentRow620 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 620).leftCharge (GramAssembly.key 620).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 377) := by
    have ha : gramCharges (GramAssembly.key 620).leftCharge (GramAssembly.key 620).rightCharge = raw40068 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40068Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40068 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 620).leftCharge (GramAssembly.key 620).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow620, Integer.Sparse.eval]

theorem keyMoment621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 621) =
      Integer.Sparse.eval keyMomentRow621 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 621).leftCharge (GramAssembly.key 621).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 360) := by
    have ha : gramCharges (GramAssembly.key 621).leftCharge (GramAssembly.key 621).rightCharge = raw40069 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40069Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40069 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 621).leftCharge (GramAssembly.key 621).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow621, Integer.Sparse.eval]

theorem keyMoment622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 622) =
      Integer.Sparse.eval keyMomentRow622 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 622).leftCharge (GramAssembly.key 622).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 376) := by
    have ha : gramCharges (GramAssembly.key 622).leftCharge (GramAssembly.key 622).rightCharge = raw40070 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40070Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40070 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 622).leftCharge (GramAssembly.key 622).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow622, Integer.Sparse.eval]

theorem keyMoment623 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 623) =
      Integer.Sparse.eval keyMomentRow623 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 623).leftCharge (GramAssembly.key 623).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 367) := by
    have ha : gramCharges (GramAssembly.key 623).leftCharge (GramAssembly.key 623).rightCharge = raw40071 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40071Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40071 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 623).leftCharge (GramAssembly.key 623).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow623, Integer.Sparse.eval]

theorem keyMoment624 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 624) =
      Integer.Sparse.eval keyMomentRow624 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 624).leftCharge (GramAssembly.key 624).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 420) := by
    have ha : gramCharges (GramAssembly.key 624).leftCharge (GramAssembly.key 624).rightCharge = raw40072 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40072Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40072 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 624).leftCharge (GramAssembly.key 624).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow624, Integer.Sparse.eval]

theorem keyMoment625 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 625) =
      Integer.Sparse.eval keyMomentRow625 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 625).leftCharge (GramAssembly.key 625).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 414) := by
    have ha : gramCharges (GramAssembly.key 625).leftCharge (GramAssembly.key 625).rightCharge = raw40073 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40073Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40073 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 625).leftCharge (GramAssembly.key 625).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow625, Integer.Sparse.eval]

theorem keyMoment626 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 626) =
      Integer.Sparse.eval keyMomentRow626 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 626).leftCharge (GramAssembly.key 626).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 369) := by
    have ha : gramCharges (GramAssembly.key 626).leftCharge (GramAssembly.key 626).rightCharge = raw40074 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40074Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40074 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 626).leftCharge (GramAssembly.key 626).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow626, Integer.Sparse.eval]

theorem keyMoment627 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 627) =
      Integer.Sparse.eval keyMomentRow627 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 627).leftCharge (GramAssembly.key 627).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 390) := by
    have ha : gramCharges (GramAssembly.key 627).leftCharge (GramAssembly.key 627).rightCharge = raw40075 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40075Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40075 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 627).leftCharge (GramAssembly.key 627).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow627, Integer.Sparse.eval]

theorem keyMoment628 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 628) =
      Integer.Sparse.eval keyMomentRow628 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 628).leftCharge (GramAssembly.key 628).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 416) := by
    have ha : gramCharges (GramAssembly.key 628).leftCharge (GramAssembly.key 628).rightCharge = raw40076 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40076Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40076 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 628).leftCharge (GramAssembly.key 628).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow628, Integer.Sparse.eval]

theorem keyMoment629 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 629) =
      Integer.Sparse.eval keyMomentRow629 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 629).leftCharge (GramAssembly.key 629).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 368) := by
    have ha : gramCharges (GramAssembly.key 629).leftCharge (GramAssembly.key 629).rightCharge = raw40077 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40077Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40077 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 629).leftCharge (GramAssembly.key 629).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow629, Integer.Sparse.eval]

theorem keyMoment630 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 630) =
      Integer.Sparse.eval keyMomentRow630 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 630).leftCharge (GramAssembly.key 630).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 387) := by
    have ha : gramCharges (GramAssembly.key 630).leftCharge (GramAssembly.key 630).rightCharge = raw40078 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40078Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40078 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 630).leftCharge (GramAssembly.key 630).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow630, Integer.Sparse.eval]

theorem keyMoment631 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 631) =
      Integer.Sparse.eval keyMomentRow631 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 631).leftCharge (GramAssembly.key 631).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 371) := by
    have ha : gramCharges (GramAssembly.key 631).leftCharge (GramAssembly.key 631).rightCharge = raw40079 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40079Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40079 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 631).leftCharge (GramAssembly.key 631).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow631, Integer.Sparse.eval]

theorem keyMoment632 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 632) =
      Integer.Sparse.eval keyMomentRow632 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 632).leftCharge (GramAssembly.key 632).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 415) := by
    have ha : gramCharges (GramAssembly.key 632).leftCharge (GramAssembly.key 632).rightCharge = raw40080 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40080Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40080 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 632).leftCharge (GramAssembly.key 632).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow632, Integer.Sparse.eval]

theorem keyMoment633 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 633) =
      Integer.Sparse.eval keyMomentRow633 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 633).leftCharge (GramAssembly.key 633).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 316) := by
    have ha : gramCharges (GramAssembly.key 633).leftCharge (GramAssembly.key 633).rightCharge = raw40081 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40081Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40081 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 633).leftCharge (GramAssembly.key 633).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow633, Integer.Sparse.eval]

theorem keyMoment634 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 634) =
      Integer.Sparse.eval keyMomentRow634 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 634).leftCharge (GramAssembly.key 634).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 388) := by
    have ha : gramCharges (GramAssembly.key 634).leftCharge (GramAssembly.key 634).rightCharge = raw40082 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40082Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40082 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 634).leftCharge (GramAssembly.key 634).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow634, Integer.Sparse.eval]

theorem keyMoment635 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 635) =
      Integer.Sparse.eval keyMomentRow635 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 635).leftCharge (GramAssembly.key 635).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 113) := by
    have ha : gramCharges (GramAssembly.key 635).leftCharge (GramAssembly.key 635).rightCharge = raw40083 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40083Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40083 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 635).leftCharge (GramAssembly.key 635).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow635, Integer.Sparse.eval]

theorem keyMoment636 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 636) =
      Integer.Sparse.eval keyMomentRow636 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 636).leftCharge (GramAssembly.key 636).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 4) := by
    have ha : gramCharges (GramAssembly.key 636).leftCharge (GramAssembly.key 636).rightCharge = raw40084 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40084Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40084 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 636).leftCharge (GramAssembly.key 636).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow636, Integer.Sparse.eval]

theorem keyMoment637 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 637) =
      Integer.Sparse.eval keyMomentRow637 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 637).leftCharge (GramAssembly.key 637).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 489) := by
    have ha : gramCharges (GramAssembly.key 637).leftCharge (GramAssembly.key 637).rightCharge = raw40085 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40085Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40085 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 637).leftCharge (GramAssembly.key 637).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow637, Integer.Sparse.eval]

theorem keyMoment638 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 638) =
      Integer.Sparse.eval keyMomentRow638 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 638).leftCharge (GramAssembly.key 638).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 521) := by
    have ha : gramCharges (GramAssembly.key 638).leftCharge (GramAssembly.key 638).rightCharge = raw40086 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40086Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40086 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 638).leftCharge (GramAssembly.key 638).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow638, Integer.Sparse.eval]

theorem keyMoment639 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 639) =
      Integer.Sparse.eval keyMomentRow639 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 639).leftCharge (GramAssembly.key 639).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 518) := by
    have ha : gramCharges (GramAssembly.key 639).leftCharge (GramAssembly.key 639).rightCharge = raw40087 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40087Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40087 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 639).leftCharge (GramAssembly.key 639).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow639, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt608 : keyMomentRows (608 : Fin 2886) =
    keyMomentRow608 := by decide +kernel

theorem keyMomentRowsAt609 : keyMomentRows (609 : Fin 2886) =
    keyMomentRow609 := by decide +kernel

theorem keyMomentRowsAt610 : keyMomentRows (610 : Fin 2886) =
    keyMomentRow610 := by decide +kernel

theorem keyMomentRowsAt611 : keyMomentRows (611 : Fin 2886) =
    keyMomentRow611 := by decide +kernel

theorem keyMomentRowsAt612 : keyMomentRows (612 : Fin 2886) =
    keyMomentRow612 := by decide +kernel

theorem keyMomentRowsAt613 : keyMomentRows (613 : Fin 2886) =
    keyMomentRow613 := by decide +kernel

theorem keyMomentRowsAt614 : keyMomentRows (614 : Fin 2886) =
    keyMomentRow614 := by decide +kernel

theorem keyMomentRowsAt615 : keyMomentRows (615 : Fin 2886) =
    keyMomentRow615 := by decide +kernel

theorem keyMomentRowsAt616 : keyMomentRows (616 : Fin 2886) =
    keyMomentRow616 := by decide +kernel

theorem keyMomentRowsAt617 : keyMomentRows (617 : Fin 2886) =
    keyMomentRow617 := by decide +kernel

theorem keyMomentRowsAt618 : keyMomentRows (618 : Fin 2886) =
    keyMomentRow618 := by decide +kernel

theorem keyMomentRowsAt619 : keyMomentRows (619 : Fin 2886) =
    keyMomentRow619 := by decide +kernel

theorem keyMomentRowsAt620 : keyMomentRows (620 : Fin 2886) =
    keyMomentRow620 := by decide +kernel

theorem keyMomentRowsAt621 : keyMomentRows (621 : Fin 2886) =
    keyMomentRow621 := by decide +kernel

theorem keyMomentRowsAt622 : keyMomentRows (622 : Fin 2886) =
    keyMomentRow622 := by decide +kernel

theorem keyMomentRowsAt623 : keyMomentRows (623 : Fin 2886) =
    keyMomentRow623 := by decide +kernel

theorem keyMomentRowsAt624 : keyMomentRows (624 : Fin 2886) =
    keyMomentRow624 := by decide +kernel

theorem keyMomentRowsAt625 : keyMomentRows (625 : Fin 2886) =
    keyMomentRow625 := by decide +kernel

theorem keyMomentRowsAt626 : keyMomentRows (626 : Fin 2886) =
    keyMomentRow626 := by decide +kernel

theorem keyMomentRowsAt627 : keyMomentRows (627 : Fin 2886) =
    keyMomentRow627 := by decide +kernel

theorem keyMomentRowsAt628 : keyMomentRows (628 : Fin 2886) =
    keyMomentRow628 := by decide +kernel

theorem keyMomentRowsAt629 : keyMomentRows (629 : Fin 2886) =
    keyMomentRow629 := by decide +kernel

theorem keyMomentRowsAt630 : keyMomentRows (630 : Fin 2886) =
    keyMomentRow630 := by decide +kernel

theorem keyMomentRowsAt631 : keyMomentRows (631 : Fin 2886) =
    keyMomentRow631 := by decide +kernel

theorem keyMomentRowsAt632 : keyMomentRows (632 : Fin 2886) =
    keyMomentRow632 := by decide +kernel

theorem keyMomentRowsAt633 : keyMomentRows (633 : Fin 2886) =
    keyMomentRow633 := by decide +kernel

theorem keyMomentRowsAt634 : keyMomentRows (634 : Fin 2886) =
    keyMomentRow634 := by decide +kernel

theorem keyMomentRowsAt635 : keyMomentRows (635 : Fin 2886) =
    keyMomentRow635 := by decide +kernel

theorem keyMomentRowsAt636 : keyMomentRows (636 : Fin 2886) =
    keyMomentRow636 := by decide +kernel

theorem keyMomentRowsAt637 : keyMomentRows (637 : Fin 2886) =
    keyMomentRow637 := by decide +kernel

theorem keyMomentRowsAt638 : keyMomentRows (638 : Fin 2886) =
    keyMomentRow638 := by decide +kernel

theorem keyMomentRowsAt639 : keyMomentRows (639 : Fin 2886) =
    keyMomentRow639 := by decide +kernel

theorem keyMomentChunkSound19_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 19) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 608 ∨ k.val = 609 ∨ k.val = 610 ∨ k.val = 611 ∨ k.val = 612 ∨ k.val = 613 ∨ k.val = 614 ∨ k.val = 615 ∨ k.val = 616 ∨ k.val = 617 ∨ k.val = 618 ∨ k.val = 619 ∨ k.val = 620 ∨ k.val = 621 ∨ k.val = 622 ∨ k.val = 623 ∨ k.val = 624 ∨ k.val = 625 ∨ k.val = 626 ∨ k.val = 627 ∨ k.val = 628 ∨ k.val = 629 ∨ k.val = 630 ∨ k.val = 631 ∨ k.val = 632 ∨ k.val = 633 ∨ k.val = 634 ∨ k.val = 635 ∨ k.val = 636 ∨ k.val = 637 ∨ k.val = 638 ∨ k.val = 639 := by omega
  rcases heq with h608 | h609 | h610 | h611 | h612 | h613 | h614 | h615 | h616 | h617 | h618 | h619 | h620 | h621 | h622 | h623 | h624 | h625 | h626 | h627 | h628 | h629 | h630 | h631 | h632 | h633 | h634 | h635 | h636 | h637 | h638 | h639
  · have he : k = (608 : Fin 2886) := Fin.ext h608
    subst k
    rw [keyMomentRowsAt608]
    exact keyMoment608 B hB
  · have he : k = (609 : Fin 2886) := Fin.ext h609
    subst k
    rw [keyMomentRowsAt609]
    exact keyMoment609 B hB
  · have he : k = (610 : Fin 2886) := Fin.ext h610
    subst k
    rw [keyMomentRowsAt610]
    exact keyMoment610 B hB
  · have he : k = (611 : Fin 2886) := Fin.ext h611
    subst k
    rw [keyMomentRowsAt611]
    exact keyMoment611 B hB
  · have he : k = (612 : Fin 2886) := Fin.ext h612
    subst k
    rw [keyMomentRowsAt612]
    exact keyMoment612 B hB
  · have he : k = (613 : Fin 2886) := Fin.ext h613
    subst k
    rw [keyMomentRowsAt613]
    exact keyMoment613 B hB
  · have he : k = (614 : Fin 2886) := Fin.ext h614
    subst k
    rw [keyMomentRowsAt614]
    exact keyMoment614 B hB
  · have he : k = (615 : Fin 2886) := Fin.ext h615
    subst k
    rw [keyMomentRowsAt615]
    exact keyMoment615 B hB
  · have he : k = (616 : Fin 2886) := Fin.ext h616
    subst k
    rw [keyMomentRowsAt616]
    exact keyMoment616 B hB
  · have he : k = (617 : Fin 2886) := Fin.ext h617
    subst k
    rw [keyMomentRowsAt617]
    exact keyMoment617 B hB
  · have he : k = (618 : Fin 2886) := Fin.ext h618
    subst k
    rw [keyMomentRowsAt618]
    exact keyMoment618 B hB
  · have he : k = (619 : Fin 2886) := Fin.ext h619
    subst k
    rw [keyMomentRowsAt619]
    exact keyMoment619 B hB
  · have he : k = (620 : Fin 2886) := Fin.ext h620
    subst k
    rw [keyMomentRowsAt620]
    exact keyMoment620 B hB
  · have he : k = (621 : Fin 2886) := Fin.ext h621
    subst k
    rw [keyMomentRowsAt621]
    exact keyMoment621 B hB
  · have he : k = (622 : Fin 2886) := Fin.ext h622
    subst k
    rw [keyMomentRowsAt622]
    exact keyMoment622 B hB
  · have he : k = (623 : Fin 2886) := Fin.ext h623
    subst k
    rw [keyMomentRowsAt623]
    exact keyMoment623 B hB
  · have he : k = (624 : Fin 2886) := Fin.ext h624
    subst k
    rw [keyMomentRowsAt624]
    exact keyMoment624 B hB
  · have he : k = (625 : Fin 2886) := Fin.ext h625
    subst k
    rw [keyMomentRowsAt625]
    exact keyMoment625 B hB
  · have he : k = (626 : Fin 2886) := Fin.ext h626
    subst k
    rw [keyMomentRowsAt626]
    exact keyMoment626 B hB
  · have he : k = (627 : Fin 2886) := Fin.ext h627
    subst k
    rw [keyMomentRowsAt627]
    exact keyMoment627 B hB
  · have he : k = (628 : Fin 2886) := Fin.ext h628
    subst k
    rw [keyMomentRowsAt628]
    exact keyMoment628 B hB
  · have he : k = (629 : Fin 2886) := Fin.ext h629
    subst k
    rw [keyMomentRowsAt629]
    exact keyMoment629 B hB
  · have he : k = (630 : Fin 2886) := Fin.ext h630
    subst k
    rw [keyMomentRowsAt630]
    exact keyMoment630 B hB
  · have he : k = (631 : Fin 2886) := Fin.ext h631
    subst k
    rw [keyMomentRowsAt631]
    exact keyMoment631 B hB
  · have he : k = (632 : Fin 2886) := Fin.ext h632
    subst k
    rw [keyMomentRowsAt632]
    exact keyMoment632 B hB
  · have he : k = (633 : Fin 2886) := Fin.ext h633
    subst k
    rw [keyMomentRowsAt633]
    exact keyMoment633 B hB
  · have he : k = (634 : Fin 2886) := Fin.ext h634
    subst k
    rw [keyMomentRowsAt634]
    exact keyMoment634 B hB
  · have he : k = (635 : Fin 2886) := Fin.ext h635
    subst k
    rw [keyMomentRowsAt635]
    exact keyMoment635 B hB
  · have he : k = (636 : Fin 2886) := Fin.ext h636
    subst k
    rw [keyMomentRowsAt636]
    exact keyMoment636 B hB
  · have he : k = (637 : Fin 2886) := Fin.ext h637
    subst k
    rw [keyMomentRowsAt637]
    exact keyMoment637 B hB
  · have he : k = (638 : Fin 2886) := Fin.ext h638
    subst k
    rw [keyMomentRowsAt638]
    exact keyMoment638 B hB
  · have he : k = (639 : Fin 2886) := Fin.ext h639
    subst k
    rw [keyMomentRowsAt639]
    exact keyMoment639 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound19_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound19_e_oai
