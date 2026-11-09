-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound64_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:59:47.264195+00:00
-- url     : https://prove2.me/submissions/fff047ed-dff4-47bb-962e-ddc512587c83

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E112
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical323
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41461 raw41461Labels = mixedMoment B node603 node603Labels := by
  calc
    mixedMoment B raw41461 raw41461Labels = mixedMoment B raw41461step0 raw41461step0Labels := by
      have hz : ∀ j, raw41461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41461step0 = (fun i j => raw41461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41461step0 raw41461; decide +kernel
      have hl : raw41461step0Labels = raw41461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41461 raw41461Labels permutation346 hz
    mixedMoment B raw41461step0 raw41461step0Labels = mixedMoment B raw41461step1 raw41461step1Labels := by
      have ha : raw41461step1 = (fun i j => raw41461step0 (permutation131 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41461step1 raw41461step0; decide +kernel
      have hl : raw41461step1Labels = raw41461step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41461step0 raw41461step0Labels permutation131 permutation6
    _ = mixedMoment B node603 node603Labels := by rfl

theorem canonical41462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41462 raw41462Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw41462 raw41462Labels = mixedMoment B raw41462step0 raw41462step0Labels := by
      have hz : ∀ j, raw41462 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41462step0 = (fun i j => raw41462 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41462step0 raw41462; decide +kernel
      have hl : raw41462step0Labels = raw41462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41462 raw41462Labels permutation346 hz
    mixedMoment B raw41462step0 raw41462step0Labels = mixedMoment B raw41462step1 raw41462step1Labels := by
      have ha : raw41462step1 = (fun i j => raw41462step0 (permutation123 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41462step1 raw41462step0; decide +kernel
      have hl : raw41462step1Labels = raw41462step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41462step0 raw41462step0Labels permutation123 permutation6
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical41463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41463 raw41463Labels = mixedMoment B node2337 node2337Labels := by
  calc
    mixedMoment B raw41463 raw41463Labels = mixedMoment B raw41463step0 raw41463step0Labels := by
      have hz : ∀ j, raw41463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41463step0 = (fun i j => raw41463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41463step0 raw41463; decide +kernel
      have hl : raw41463step0Labels = raw41463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41463 raw41463Labels permutation346 hz
    mixedMoment B raw41463step0 raw41463step0Labels = mixedMoment B raw41463step1 raw41463step1Labels := by
      have ha : raw41463step1 = (fun i j => raw41463step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41463step1 raw41463step0; decide +kernel
      have hl : raw41463step1Labels = raw41463step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41463step0 raw41463step0Labels permutation122 permutation6
    _ = mixedMoment B node2337 node2337Labels := by rfl

theorem canonical41464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41464 raw41464Labels = mixedMoment B node922 node922Labels := by
  calc
    mixedMoment B raw41464 raw41464Labels = mixedMoment B raw41464step0 raw41464step0Labels := by
      have ha : raw41464step0 = (fun i j => raw41464 (permutation572 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41464step0 raw41464; decide +kernel
      have hl : raw41464step0Labels = raw41464Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41464 raw41464Labels permutation572 permutation6
    _ = mixedMoment B node922 node922Labels := by rfl

theorem canonical41465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41465 raw41465Labels = mixedMoment B node2332 node2332Labels := by
  calc
    mixedMoment B raw41465 raw41465Labels = mixedMoment B raw41465step0 raw41465step0Labels := by
      have ha : raw41465step0 = (fun i j => raw41465 (permutation572 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41465step0 raw41465; decide +kernel
      have hl : raw41465step0Labels = raw41465Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41465 raw41465Labels permutation572 permutation6
    _ = mixedMoment B node2332 node2332Labels := by rfl

theorem canonical41466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41466 raw41466Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw41466 raw41466Labels = mixedMoment B raw41466step0 raw41466step0Labels := by
      have hz : ∀ j, raw41466 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41466step0 = (fun i j => raw41466 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41466step0 raw41466; decide +kernel
      have hl : raw41466step0Labels = raw41466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41466 raw41466Labels permutation520 hz
    mixedMoment B raw41466step0 raw41466step0Labels = mixedMoment B raw41466step1 raw41466step1Labels := by
      have hz : ∀ j, raw41466step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41466step1 = (fun i j => raw41466step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41466step1 raw41466step0; decide +kernel
      have hl : raw41466step1Labels = raw41466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41466step0 raw41466step0Labels permutation104 hz
    mixedMoment B raw41466step1 raw41466step1Labels = mixedMoment B raw41466step2 raw41466step2Labels := by
      have ha : raw41466step2 = (fun i j => raw41466step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41466step2 raw41466step1; decide +kernel
      have hl : raw41466step2Labels = raw41466step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41466step1 raw41466step1Labels permutation24 permutation6
    _ = mixedMoment B node2109 node2109Labels := by rfl

theorem canonical41467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41467 raw41467Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw41467 raw41467Labels = mixedMoment B raw41467step0 raw41467step0Labels := by
      have hz : ∀ j, raw41467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41467step0 = (fun i j => raw41467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41467step0 raw41467; decide +kernel
      have hl : raw41467step0Labels = raw41467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41467 raw41467Labels permutation434 hz
    mixedMoment B raw41467step0 raw41467step0Labels = mixedMoment B raw41467step1 raw41467step1Labels := by
      have ha : raw41467step1 = (fun i j => raw41467step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41467step1 raw41467step0; decide +kernel
      have hl : raw41467step1Labels = raw41467step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41467step0 raw41467step0Labels permutation99 permutation6
    _ = mixedMoment B node1807 node1807Labels := by rfl

theorem canonical41468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41468 raw41468Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw41468 raw41468Labels = mixedMoment B raw41468step0 raw41468step0Labels := by
      have hz : ∀ j, raw41468 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41468step0 = (fun i j => raw41468 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41468step0 raw41468; decide +kernel
      have hl : raw41468step0Labels = raw41468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41468 raw41468Labels permutation434 hz
    mixedMoment B raw41468step0 raw41468step0Labels = mixedMoment B raw41468step1 raw41468step1Labels := by
      have ha : raw41468step1 = (fun i j => raw41468step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41468step1 raw41468step0; decide +kernel
      have hl : raw41468step1Labels = raw41468step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41468step0 raw41468step0Labels permutation96 permutation6
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical41469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41469 raw41469Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw41469 raw41469Labels = mixedMoment B raw41469step0 raw41469step0Labels := by
      have hz : ∀ j, raw41469 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41469step0 = (fun i j => raw41469 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41469step0 raw41469; decide +kernel
      have hl : raw41469step0Labels = raw41469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41469 raw41469Labels permutation520 hz
    mixedMoment B raw41469step0 raw41469step0Labels = mixedMoment B raw41469step1 raw41469step1Labels := by
      have ha : raw41469step1 = (fun i j => raw41469step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41469step1 raw41469step0; decide +kernel
      have hl : raw41469step1Labels = raw41469step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41469step0 raw41469step0Labels permutation61 permutation6
    mixedMoment B raw41469step1 raw41469step1Labels = mixedMoment B raw41469step2 raw41469step2Labels := by
      have ha : raw41469step2 = -raw41469step1 := by apply Matrix.ext; change ∀ i j, raw41469step2 i j = -(raw41469step1 i j); unfold raw41469step2 raw41469step1; decide +kernel
      have hl : raw41469step2Labels = raw41469step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2590 node2590Labels := by rfl

theorem canonical41470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41470 raw41470Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw41470 raw41470Labels = mixedMoment B raw41470step0 raw41470step0Labels := by
      have ha : raw41470step0 = (fun i j => raw41470 (permutation323 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41470step0 raw41470; decide +kernel
      have hl : raw41470step0Labels = raw41470Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41470 raw41470Labels permutation323 permutation6
    mixedMoment B raw41470step0 raw41470step0Labels = mixedMoment B raw41470step1 raw41470step1Labels := by
      have ha : raw41470step1 = -raw41470step0 := by apply Matrix.ext; change ∀ i j, raw41470step1 i j = -(raw41470step0 i j); unfold raw41470step1 raw41470step0; decide +kernel
      have hl : raw41470step1Labels = raw41470step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2431 node2431Labels := by rfl

theorem canonical41471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41471 raw41471Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw41471 raw41471Labels = mixedMoment B raw41471step0 raw41471step0Labels := by
      have ha : raw41471step0 = (fun i j => raw41471 (permutation288 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41471step0 raw41471; decide +kernel
      have hl : raw41471step0Labels = raw41471Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41471 raw41471Labels permutation288 permutation6
    mixedMoment B raw41471step0 raw41471step0Labels = mixedMoment B raw41471step1 raw41471step1Labels := by
      have ha : raw41471step1 = -raw41471step0 := by apply Matrix.ext; change ∀ i j, raw41471step1 i j = -(raw41471step0 i j); unfold raw41471step1 raw41471step0; decide +kernel
      have hl : raw41471step1Labels = raw41471step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2553 node2553Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical324
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41472 raw41472Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw41472 raw41472Labels = mixedMoment B raw41472step0 raw41472step0Labels := by
      have hz : ∀ j, raw41472 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41472step0 = (fun i j => raw41472 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41472step0 raw41472; decide +kernel
      have hl : raw41472step0Labels = raw41472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41472 raw41472Labels permutation434 hz
    mixedMoment B raw41472step0 raw41472step0Labels = mixedMoment B raw41472step1 raw41472step1Labels := by
      have ha : raw41472step1 = (fun i j => raw41472step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41472step1 raw41472step0; decide +kernel
      have hl : raw41472step1Labels = raw41472step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41472step0 raw41472step0Labels permutation68 permutation6
    mixedMoment B raw41472step1 raw41472step1Labels = mixedMoment B raw41472step2 raw41472step2Labels := by
      have ha : raw41472step2 = -raw41472step1 := by apply Matrix.ext; change ∀ i j, raw41472step2 i j = -(raw41472step1 i j); unfold raw41472step2 raw41472step1; decide +kernel
      have hl : raw41472step2Labels = raw41472step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2434 node2434Labels := by rfl

theorem canonical41473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41473 raw41473Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw41473 raw41473Labels = mixedMoment B raw41473step0 raw41473step0Labels := by
      have hz : ∀ j, raw41473 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41473step0 = (fun i j => raw41473 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41473step0 raw41473; decide +kernel
      have hl : raw41473step0Labels = raw41473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41473 raw41473Labels permutation434 hz
    mixedMoment B raw41473step0 raw41473step0Labels = mixedMoment B raw41473step1 raw41473step1Labels := by
      have ha : raw41473step1 = (fun i j => raw41473step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41473step1 raw41473step0; decide +kernel
      have hl : raw41473step1Labels = raw41473step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41473step0 raw41473step0Labels permutation61 permutation6
    mixedMoment B raw41473step1 raw41473step1Labels = mixedMoment B raw41473step2 raw41473step2Labels := by
      have ha : raw41473step2 = -raw41473step1 := by apply Matrix.ext; change ∀ i j, raw41473step2 i j = -(raw41473step1 i j); unfold raw41473step2 raw41473step1; decide +kernel
      have hl : raw41473step2Labels = raw41473step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2561 node2561Labels := by rfl

theorem canonical41474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41474 raw41474Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw41474 raw41474Labels = mixedMoment B raw41474step0 raw41474step0Labels := by
      have ha : raw41474step0 = (fun i j => raw41474 (permutation310 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41474step0 raw41474; decide +kernel
      have hl : raw41474step0Labels = raw41474Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41474 raw41474Labels permutation310 permutation6
    mixedMoment B raw41474step0 raw41474step0Labels = mixedMoment B raw41474step1 raw41474step1Labels := by
      have ha : raw41474step1 = -raw41474step0 := by apply Matrix.ext; change ∀ i j, raw41474step1 i j = -(raw41474step0 i j); unfold raw41474step1 raw41474step0; decide +kernel
      have hl : raw41474step1Labels = raw41474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2428 node2428Labels := by rfl

theorem canonical41475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41475 raw41475Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw41475 raw41475Labels = mixedMoment B raw41475step0 raw41475step0Labels := by
      have ha : raw41475step0 = (fun i j => raw41475 (permutation283 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41475step0 raw41475; decide +kernel
      have hl : raw41475step0Labels = raw41475Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41475 raw41475Labels permutation283 permutation6
    mixedMoment B raw41475step0 raw41475step0Labels = mixedMoment B raw41475step1 raw41475step1Labels := by
      have ha : raw41475step1 = -raw41475step0 := by apply Matrix.ext; change ∀ i j, raw41475step1 i j = -(raw41475step0 i j); unfold raw41475step1 raw41475step0; decide +kernel
      have hl : raw41475step1Labels = raw41475step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2589 node2589Labels := by rfl

theorem canonical41476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41476 raw41476Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw41476 raw41476Labels = mixedMoment B raw41476step0 raw41476step0Labels := by
      have ha : raw41476step0 = (fun i j => raw41476 (permutation322 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41476step0 raw41476; decide +kernel
      have hl : raw41476step0Labels = raw41476Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41476 raw41476Labels permutation322 permutation6
    mixedMoment B raw41476step0 raw41476step0Labels = mixedMoment B raw41476step1 raw41476step1Labels := by
      have ha : raw41476step1 = -raw41476step0 := by apply Matrix.ext; change ∀ i j, raw41476step1 i j = -(raw41476step0 i j); unfold raw41476step1 raw41476step0; decide +kernel
      have hl : raw41476step1Labels = raw41476step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2429 node2429Labels := by rfl

theorem canonical41477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41477 raw41477Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw41477 raw41477Labels = mixedMoment B raw41477step0 raw41477step0Labels := by
      have hz : ∀ j, raw41477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41477step0 = (fun i j => raw41477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41477step0 raw41477; decide +kernel
      have hl : raw41477step0Labels = raw41477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41477 raw41477Labels permutation434 hz
    mixedMoment B raw41477step0 raw41477step0Labels = mixedMoment B raw41477step1 raw41477step1Labels := by
      have ha : raw41477step1 = (fun i j => raw41477step0 (permutation141 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41477step1 raw41477step0; decide +kernel
      have hl : raw41477step1Labels = raw41477step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41477step0 raw41477step0Labels permutation141 permutation6
    _ = mixedMoment B node1131 node1131Labels := by rfl

theorem canonical41478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41478 raw41478Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw41478 raw41478Labels = mixedMoment B raw41478step0 raw41478step0Labels := by
      have hz : ∀ j, raw41478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41478step0 = (fun i j => raw41478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41478step0 raw41478; decide +kernel
      have hl : raw41478step0Labels = raw41478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41478 raw41478Labels permutation434 hz
    mixedMoment B raw41478step0 raw41478step0Labels = mixedMoment B raw41478step1 raw41478step1Labels := by
      have ha : raw41478step1 = (fun i j => raw41478step0 (permutation120 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41478step1 raw41478step0; decide +kernel
      have hl : raw41478step1Labels = raw41478step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41478step0 raw41478step0Labels permutation120 permutation6
    _ = mixedMoment B node2482 node2482Labels := by rfl

theorem canonical41479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41479 raw41479Labels = mixedMoment B node2425 node2425Labels := by
  calc
    mixedMoment B raw41479 raw41479Labels = mixedMoment B raw41479step0 raw41479step0Labels := by
      have ha : raw41479step0 = (fun i j => raw41479 (permutation548 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41479step0 raw41479; decide +kernel
      have hl : raw41479step0Labels = raw41479Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41479 raw41479Labels permutation548 permutation6
    _ = mixedMoment B node2425 node2425Labels := by rfl

theorem canonical41480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41480 raw41480Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw41480 raw41480Labels = mixedMoment B raw41480step0 raw41480step0Labels := by
      have hz : ∀ j, raw41480 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41480step0 = (fun i j => raw41480 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41480step0 raw41480; decide +kernel
      have hl : raw41480step0Labels = raw41480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41480 raw41480Labels permutation434 hz
    mixedMoment B raw41480step0 raw41480step0Labels = mixedMoment B raw41480step1 raw41480step1Labels := by
      have hz : ∀ j, raw41480step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41480step1 = (fun i j => raw41480step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41480step1 raw41480step0; decide +kernel
      have hl : raw41480step1Labels = raw41480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41480step0 raw41480step0Labels permutation80 hz
    mixedMoment B raw41480step1 raw41480step1Labels = mixedMoment B raw41480step2 raw41480step2Labels := by
      have ha : raw41480step2 = (fun i j => raw41480step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41480step2 raw41480step1; decide +kernel
      have hl : raw41480step2Labels = raw41480step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41480step1 raw41480step1Labels permutation27 permutation6
    _ = mixedMoment B node605 node605Labels := by rfl

theorem canonical41481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41481 raw41481Labels = mixedMoment B node937 node937Labels := by
  calc
    mixedMoment B raw41481 raw41481Labels = mixedMoment B raw41481step0 raw41481step0Labels := by
      have hz : ∀ j, raw41481 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41481step0 = (fun i j => raw41481 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41481step0 raw41481; decide +kernel
      have hl : raw41481step0Labels = raw41481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41481 raw41481Labels permutation520 hz
    mixedMoment B raw41481step0 raw41481step0Labels = mixedMoment B raw41481step1 raw41481step1Labels := by
      have hz : ∀ j, raw41481step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41481step1 = (fun i j => raw41481step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41481step1 raw41481step0; decide +kernel
      have hl : raw41481step1Labels = raw41481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41481step0 raw41481step0Labels permutation104 hz
    mixedMoment B raw41481step1 raw41481step1Labels = mixedMoment B raw41481step2 raw41481step2Labels := by
      have ha : raw41481step2 = (fun i j => raw41481step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41481step2 raw41481step1; decide +kernel
      have hl : raw41481step2Labels = raw41481step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41481step1 raw41481step1Labels permutation15 permutation6
    mixedMoment B raw41481step2 raw41481step2Labels = mixedMoment B raw41481step3 raw41481step3Labels := by
      have ha : raw41481step3 = -raw41481step2 := by apply Matrix.ext; change ∀ i j, raw41481step3 i j = -(raw41481step2 i j); unfold raw41481step3 raw41481step2; decide +kernel
      have hl : raw41481step3Labels = raw41481step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node937 node937Labels := by rfl

theorem canonical41482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41482 raw41482Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw41482 raw41482Labels = mixedMoment B raw41482step0 raw41482step0Labels := by
      have hz : ∀ j, raw41482 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41482step0 = (fun i j => raw41482 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41482step0 raw41482; decide +kernel
      have hl : raw41482step0Labels = raw41482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41482 raw41482Labels permutation520 hz
    mixedMoment B raw41482step0 raw41482step0Labels = mixedMoment B raw41482step1 raw41482step1Labels := by
      have ha : raw41482step1 = (fun i j => raw41482step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41482step1 raw41482step0; decide +kernel
      have hl : raw41482step1Labels = raw41482step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41482step0 raw41482step0Labels permutation59 permutation6
    mixedMoment B raw41482step1 raw41482step1Labels = mixedMoment B raw41482step2 raw41482step2Labels := by
      have ha : raw41482step2 = -raw41482step1 := by apply Matrix.ext; change ∀ i j, raw41482step2 i j = -(raw41482step1 i j); unfold raw41482step2 raw41482step1; decide +kernel
      have hl : raw41482step2Labels = raw41482step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node932 node932Labels := by rfl

theorem canonical41483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41483 raw41483Labels = mixedMoment B node939 node939Labels := by
  calc
    mixedMoment B raw41483 raw41483Labels = mixedMoment B raw41483step0 raw41483step0Labels := by
      have hz : ∀ j, raw41483 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41483step0 = (fun i j => raw41483 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41483step0 raw41483; decide +kernel
      have hl : raw41483step0Labels = raw41483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41483 raw41483Labels permutation520 hz
    mixedMoment B raw41483step0 raw41483step0Labels = mixedMoment B raw41483step1 raw41483step1Labels := by
      have hz : ∀ j, raw41483step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41483step1 = (fun i j => raw41483step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41483step1 raw41483step0; decide +kernel
      have hl : raw41483step1Labels = raw41483step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41483step0 raw41483step0Labels permutation104 hz
    mixedMoment B raw41483step1 raw41483step1Labels = mixedMoment B raw41483step2 raw41483step2Labels := by
      have ha : raw41483step2 = (fun i j => raw41483step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41483step2 raw41483step1; decide +kernel
      have hl : raw41483step2Labels = raw41483step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41483step1 raw41483step1Labels permutation14 permutation6
    mixedMoment B raw41483step2 raw41483step2Labels = mixedMoment B raw41483step3 raw41483step3Labels := by
      have ha : raw41483step3 = -raw41483step2 := by apply Matrix.ext; change ∀ i j, raw41483step3 i j = -(raw41483step2 i j); unfold raw41483step3 raw41483step2; decide +kernel
      have hl : raw41483step3Labels = raw41483step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node939 node939Labels := by rfl

theorem canonical41484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41484 raw41484Labels = mixedMoment B node929 node929Labels := by
  calc
    mixedMoment B raw41484 raw41484Labels = mixedMoment B raw41484step0 raw41484step0Labels := by
      have ha : raw41484step0 = (fun i j => raw41484 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41484step0 raw41484; decide +kernel
      have hl : raw41484step0Labels = raw41484Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41484 raw41484Labels permutation265 permutation6
    mixedMoment B raw41484step0 raw41484step0Labels = mixedMoment B raw41484step1 raw41484step1Labels := by
      have ha : raw41484step1 = -raw41484step0 := by apply Matrix.ext; change ∀ i j, raw41484step1 i j = -(raw41484step0 i j); unfold raw41484step1 raw41484step0; decide +kernel
      have hl : raw41484step1Labels = raw41484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node929 node929Labels := by rfl

theorem canonical41485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41485 raw41485Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw41485 raw41485Labels = mixedMoment B raw41485step0 raw41485step0Labels := by
      have hz : ∀ j, raw41485 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41485step0 = (fun i j => raw41485 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41485step0 raw41485; decide +kernel
      have hl : raw41485step0Labels = raw41485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41485 raw41485Labels permutation520 hz
    mixedMoment B raw41485step0 raw41485step0Labels = mixedMoment B raw41485step1 raw41485step1Labels := by
      have ha : raw41485step1 = (fun i j => raw41485step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41485step1 raw41485step0; decide +kernel
      have hl : raw41485step1Labels = raw41485step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41485step0 raw41485step0Labels permutation56 permutation6
    mixedMoment B raw41485step1 raw41485step1Labels = mixedMoment B raw41485step2 raw41485step2Labels := by
      have ha : raw41485step2 = -raw41485step1 := by apply Matrix.ext; change ∀ i j, raw41485step2 i j = -(raw41485step1 i j); unfold raw41485step2 raw41485step1; decide +kernel
      have hl : raw41485step2Labels = raw41485step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node930 node930Labels := by rfl

theorem canonical41486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41486 raw41486Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw41486 raw41486Labels = mixedMoment B raw41486step0 raw41486step0Labels := by
      have hz : ∀ j, raw41486 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41486step0 = (fun i j => raw41486 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41486step0 raw41486; decide +kernel
      have hl : raw41486step0Labels = raw41486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41486 raw41486Labels permutation520 hz
    mixedMoment B raw41486step0 raw41486step0Labels = mixedMoment B raw41486step1 raw41486step1Labels := by
      have hz : ∀ j, raw41486step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41486step1 = (fun i j => raw41486step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41486step1 raw41486step0; decide +kernel
      have hl : raw41486step1Labels = raw41486step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41486step0 raw41486step0Labels permutation104 hz
    mixedMoment B raw41486step1 raw41486step1Labels = mixedMoment B raw41486step2 raw41486step2Labels := by
      have ha : raw41486step2 = (fun i j => raw41486step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41486step2 raw41486step1; decide +kernel
      have hl : raw41486step2Labels = raw41486step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41486step1 raw41486step1Labels permutation14 permutation6
    mixedMoment B raw41486step2 raw41486step2Labels = mixedMoment B raw41486step3 raw41486step3Labels := by
      have ha : raw41486step3 = -raw41486step2 := by apply Matrix.ext; change ∀ i j, raw41486step3 i j = -(raw41486step2 i j); unfold raw41486step3 raw41486step2; decide +kernel
      have hl : raw41486step3Labels = raw41486step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node934 node934Labels := by rfl

theorem canonical41487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41487 raw41487Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw41487 raw41487Labels = mixedMoment B raw41487step0 raw41487step0Labels := by
      have hz : ∀ j, raw41487 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41487step0 = (fun i j => raw41487 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41487step0 raw41487; decide +kernel
      have hl : raw41487step0Labels = raw41487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41487 raw41487Labels permutation520 hz
    mixedMoment B raw41487step0 raw41487step0Labels = mixedMoment B raw41487step1 raw41487step1Labels := by
      have hz : ∀ j, raw41487step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41487step1 = (fun i j => raw41487step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41487step1 raw41487step0; decide +kernel
      have hl : raw41487step1Labels = raw41487step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41487step0 raw41487step0Labels permutation104 hz
    mixedMoment B raw41487step1 raw41487step1Labels = mixedMoment B raw41487step2 raw41487step2Labels := by
      have ha : raw41487step2 = (fun i j => raw41487step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41487step2 raw41487step1; decide +kernel
      have hl : raw41487step2Labels = raw41487step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41487step1 raw41487step1Labels permutation24 permutation6
    _ = mixedMoment B node2116 node2116Labels := by rfl

theorem canonical41488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41488 raw41488Labels = mixedMoment B node1815 node1815Labels := by
  calc
    mixedMoment B raw41488 raw41488Labels = mixedMoment B raw41488step0 raw41488step0Labels := by
      have hz : ∀ j, raw41488 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41488step0 = (fun i j => raw41488 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41488step0 raw41488; decide +kernel
      have hl : raw41488step0Labels = raw41488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41488 raw41488Labels permutation434 hz
    mixedMoment B raw41488step0 raw41488step0Labels = mixedMoment B raw41488step1 raw41488step1Labels := by
      have ha : raw41488step1 = (fun i j => raw41488step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41488step1 raw41488step0; decide +kernel
      have hl : raw41488step1Labels = raw41488step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41488step0 raw41488step0Labels permutation102 permutation6
    _ = mixedMoment B node1815 node1815Labels := by rfl

theorem canonical41489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41489 raw41489Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw41489 raw41489Labels = mixedMoment B raw41489step0 raw41489step0Labels := by
      have hz : ∀ j, raw41489 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41489step0 = (fun i j => raw41489 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41489step0 raw41489; decide +kernel
      have hl : raw41489step0Labels = raw41489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41489 raw41489Labels permutation434 hz
    mixedMoment B raw41489step0 raw41489step0Labels = mixedMoment B raw41489step1 raw41489step1Labels := by
      have ha : raw41489step1 = (fun i j => raw41489step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41489step1 raw41489step0; decide +kernel
      have hl : raw41489step1Labels = raw41489step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41489step0 raw41489step0Labels permutation96 permutation6
    _ = mixedMoment B node2029 node2029Labels := by rfl

theorem canonical41490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41490 raw41490Labels = mixedMoment B node1967 node1967Labels := by
  calc
    mixedMoment B raw41490 raw41490Labels = mixedMoment B raw41490step0 raw41490step0Labels := by
      have ha : raw41490step0 = (fun i j => raw41490 (permutation413 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41490step0 raw41490; decide +kernel
      have hl : raw41490step0Labels = raw41490Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41490 raw41490Labels permutation413 permutation6
    _ = mixedMoment B node1967 node1967Labels := by rfl

theorem canonical41491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41491 raw41491Labels = mixedMoment B node3709 node3709Labels := by
  calc
    mixedMoment B raw41491 raw41491Labels = mixedMoment B raw41491step0 raw41491step0Labels := by
      have ha : raw41491step0 = (fun i j => raw41491 (permutation426 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41491step0 raw41491; decide +kernel
      have hl : raw41491step0Labels = raw41491Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41491 raw41491Labels permutation426 permutation6
    _ = mixedMoment B node3709 node3709Labels := by rfl

theorem canonical41492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41492 raw41492Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw41492 raw41492Labels = mixedMoment B raw41492step0 raw41492step0Labels := by
      have ha : raw41492step0 = (fun i j => raw41492 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41492step0 raw41492; decide +kernel
      have hl : raw41492step0Labels = raw41492Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41492 raw41492Labels permutation393 permutation6
    _ = mixedMoment B node3779 node3779Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2048 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2048) =
      Integer.Sparse.eval keyMomentRow2048 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2048).leftCharge (GramAssembly.key 2048).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 603) := by
    have ha : gramCharges (GramAssembly.key 2048).leftCharge (GramAssembly.key 2048).rightCharge = raw41461 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41461Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41461 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2048).leftCharge (GramAssembly.key 2048).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2048, Integer.Sparse.eval]

theorem keyMoment2049 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2049) =
      Integer.Sparse.eval keyMomentRow2049 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2049).leftCharge (GramAssembly.key 2049).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1041) := by
    have ha : gramCharges (GramAssembly.key 2049).leftCharge (GramAssembly.key 2049).rightCharge = raw41462 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41462Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41462 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2049).leftCharge (GramAssembly.key 2049).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2049, Integer.Sparse.eval]

theorem keyMoment2050 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2050) =
      Integer.Sparse.eval keyMomentRow2050 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2050).leftCharge (GramAssembly.key 2050).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2337) := by
    have ha : gramCharges (GramAssembly.key 2050).leftCharge (GramAssembly.key 2050).rightCharge = raw41463 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41463Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41463 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2050).leftCharge (GramAssembly.key 2050).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2050, Integer.Sparse.eval]

theorem keyMoment2051 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2051) =
      Integer.Sparse.eval keyMomentRow2051 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2051).leftCharge (GramAssembly.key 2051).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 922) := by
    have ha : gramCharges (GramAssembly.key 2051).leftCharge (GramAssembly.key 2051).rightCharge = raw41464 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41464Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41464 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2051).leftCharge (GramAssembly.key 2051).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2051, Integer.Sparse.eval]

theorem keyMoment2052 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2052) =
      Integer.Sparse.eval keyMomentRow2052 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2052).leftCharge (GramAssembly.key 2052).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2332) := by
    have ha : gramCharges (GramAssembly.key 2052).leftCharge (GramAssembly.key 2052).rightCharge = raw41465 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41465Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41465 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2052).leftCharge (GramAssembly.key 2052).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2052, Integer.Sparse.eval]

theorem keyMoment2053 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2053) =
      Integer.Sparse.eval keyMomentRow2053 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2053).leftCharge (GramAssembly.key 2053).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2109) := by
    have ha : gramCharges (GramAssembly.key 2053).leftCharge (GramAssembly.key 2053).rightCharge = raw41466 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41466Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41466 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2053).leftCharge (GramAssembly.key 2053).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2053, Integer.Sparse.eval]

theorem keyMoment2054 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2054) =
      Integer.Sparse.eval keyMomentRow2054 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2054).leftCharge (GramAssembly.key 2054).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1807) := by
    have ha : gramCharges (GramAssembly.key 2054).leftCharge (GramAssembly.key 2054).rightCharge = raw41467 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41467Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41467 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2054).leftCharge (GramAssembly.key 2054).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2054, Integer.Sparse.eval]

theorem keyMoment2055 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2055) =
      Integer.Sparse.eval keyMomentRow2055 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2055).leftCharge (GramAssembly.key 2055).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2022) := by
    have ha : gramCharges (GramAssembly.key 2055).leftCharge (GramAssembly.key 2055).rightCharge = raw41468 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41468Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41468 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2055).leftCharge (GramAssembly.key 2055).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2055, Integer.Sparse.eval]

theorem keyMoment2056 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2056) =
      Integer.Sparse.eval keyMomentRow2056 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2056).leftCharge (GramAssembly.key 2056).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2590) := by
    have ha : gramCharges (GramAssembly.key 2056).leftCharge (GramAssembly.key 2056).rightCharge = raw41469 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41469Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41469 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2056).leftCharge (GramAssembly.key 2056).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2056, Integer.Sparse.eval]

theorem keyMoment2057 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2057) =
      Integer.Sparse.eval keyMomentRow2057 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2057).leftCharge (GramAssembly.key 2057).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2431) := by
    have ha : gramCharges (GramAssembly.key 2057).leftCharge (GramAssembly.key 2057).rightCharge = raw41470 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41470Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41470 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2057).leftCharge (GramAssembly.key 2057).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2057, Integer.Sparse.eval]

theorem keyMoment2058 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2058) =
      Integer.Sparse.eval keyMomentRow2058 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2058).leftCharge (GramAssembly.key 2058).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2553) := by
    have ha : gramCharges (GramAssembly.key 2058).leftCharge (GramAssembly.key 2058).rightCharge = raw41471 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41471Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41471 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2058).leftCharge (GramAssembly.key 2058).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2058, Integer.Sparse.eval]

theorem keyMoment2059 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2059) =
      Integer.Sparse.eval keyMomentRow2059 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2059).leftCharge (GramAssembly.key 2059).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2434) := by
    have ha : gramCharges (GramAssembly.key 2059).leftCharge (GramAssembly.key 2059).rightCharge = raw41472 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41472Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41472 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2059).leftCharge (GramAssembly.key 2059).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2059, Integer.Sparse.eval]

theorem keyMoment2060 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2060) =
      Integer.Sparse.eval keyMomentRow2060 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2060).leftCharge (GramAssembly.key 2060).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2561) := by
    have ha : gramCharges (GramAssembly.key 2060).leftCharge (GramAssembly.key 2060).rightCharge = raw41473 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41473Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41473 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2060).leftCharge (GramAssembly.key 2060).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2060, Integer.Sparse.eval]

theorem keyMoment2061 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2061) =
      Integer.Sparse.eval keyMomentRow2061 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2061).leftCharge (GramAssembly.key 2061).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2428) := by
    have ha : gramCharges (GramAssembly.key 2061).leftCharge (GramAssembly.key 2061).rightCharge = raw41474 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41474Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41474 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2061).leftCharge (GramAssembly.key 2061).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2061, Integer.Sparse.eval]

theorem keyMoment2062 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2062) =
      Integer.Sparse.eval keyMomentRow2062 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2062).leftCharge (GramAssembly.key 2062).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2589) := by
    have ha : gramCharges (GramAssembly.key 2062).leftCharge (GramAssembly.key 2062).rightCharge = raw41475 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41475Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41475 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2062).leftCharge (GramAssembly.key 2062).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2062, Integer.Sparse.eval]

theorem keyMoment2063 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2063) =
      Integer.Sparse.eval keyMomentRow2063 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2063).leftCharge (GramAssembly.key 2063).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2429) := by
    have ha : gramCharges (GramAssembly.key 2063).leftCharge (GramAssembly.key 2063).rightCharge = raw41476 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41476Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41476 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2063).leftCharge (GramAssembly.key 2063).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2063, Integer.Sparse.eval]

theorem keyMoment2064 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2064) =
      Integer.Sparse.eval keyMomentRow2064 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2064).leftCharge (GramAssembly.key 2064).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1131) := by
    have ha : gramCharges (GramAssembly.key 2064).leftCharge (GramAssembly.key 2064).rightCharge = raw41477 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41477Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41477 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2064).leftCharge (GramAssembly.key 2064).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2064, Integer.Sparse.eval]

theorem keyMoment2065 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2065) =
      Integer.Sparse.eval keyMomentRow2065 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2065).leftCharge (GramAssembly.key 2065).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2482) := by
    have ha : gramCharges (GramAssembly.key 2065).leftCharge (GramAssembly.key 2065).rightCharge = raw41478 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41478Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41478 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2065).leftCharge (GramAssembly.key 2065).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2065, Integer.Sparse.eval]

theorem keyMoment2066 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2066) =
      Integer.Sparse.eval keyMomentRow2066 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2066).leftCharge (GramAssembly.key 2066).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2425) := by
    have ha : gramCharges (GramAssembly.key 2066).leftCharge (GramAssembly.key 2066).rightCharge = raw41479 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41479Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41479 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2066).leftCharge (GramAssembly.key 2066).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2066, Integer.Sparse.eval]

theorem keyMoment2067 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2067) =
      Integer.Sparse.eval keyMomentRow2067 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2067).leftCharge (GramAssembly.key 2067).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 605) := by
    have ha : gramCharges (GramAssembly.key 2067).leftCharge (GramAssembly.key 2067).rightCharge = raw41480 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41480Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41480 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2067).leftCharge (GramAssembly.key 2067).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2067, Integer.Sparse.eval]

theorem keyMoment2068 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2068) =
      Integer.Sparse.eval keyMomentRow2068 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2068).leftCharge (GramAssembly.key 2068).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 937) := by
    have ha : gramCharges (GramAssembly.key 2068).leftCharge (GramAssembly.key 2068).rightCharge = raw41481 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41481Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41481 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2068).leftCharge (GramAssembly.key 2068).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2068, Integer.Sparse.eval]

theorem keyMoment2069 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2069) =
      Integer.Sparse.eval keyMomentRow2069 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2069).leftCharge (GramAssembly.key 2069).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 932) := by
    have ha : gramCharges (GramAssembly.key 2069).leftCharge (GramAssembly.key 2069).rightCharge = raw41482 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41482Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41482 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2069).leftCharge (GramAssembly.key 2069).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2069, Integer.Sparse.eval]

theorem keyMoment2070 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2070) =
      Integer.Sparse.eval keyMomentRow2070 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2070).leftCharge (GramAssembly.key 2070).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 939) := by
    have ha : gramCharges (GramAssembly.key 2070).leftCharge (GramAssembly.key 2070).rightCharge = raw41483 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41483Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41483 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2070).leftCharge (GramAssembly.key 2070).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2070, Integer.Sparse.eval]

theorem keyMoment2071 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2071) =
      Integer.Sparse.eval keyMomentRow2071 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2071).leftCharge (GramAssembly.key 2071).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 929) := by
    have ha : gramCharges (GramAssembly.key 2071).leftCharge (GramAssembly.key 2071).rightCharge = raw41484 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41484Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41484 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2071).leftCharge (GramAssembly.key 2071).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2071, Integer.Sparse.eval]

theorem keyMoment2072 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2072) =
      Integer.Sparse.eval keyMomentRow2072 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2072).leftCharge (GramAssembly.key 2072).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 930) := by
    have ha : gramCharges (GramAssembly.key 2072).leftCharge (GramAssembly.key 2072).rightCharge = raw41485 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41485Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41485 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2072).leftCharge (GramAssembly.key 2072).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2072, Integer.Sparse.eval]

theorem keyMoment2073 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2073) =
      Integer.Sparse.eval keyMomentRow2073 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2073).leftCharge (GramAssembly.key 2073).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 934) := by
    have ha : gramCharges (GramAssembly.key 2073).leftCharge (GramAssembly.key 2073).rightCharge = raw41486 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41486Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41486 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2073).leftCharge (GramAssembly.key 2073).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2073, Integer.Sparse.eval]

theorem keyMoment2074 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2074) =
      Integer.Sparse.eval keyMomentRow2074 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2074).leftCharge (GramAssembly.key 2074).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2116) := by
    have ha : gramCharges (GramAssembly.key 2074).leftCharge (GramAssembly.key 2074).rightCharge = raw41487 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41487Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41487 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2074).leftCharge (GramAssembly.key 2074).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2074, Integer.Sparse.eval]

theorem keyMoment2075 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2075) =
      Integer.Sparse.eval keyMomentRow2075 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2075).leftCharge (GramAssembly.key 2075).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1815) := by
    have ha : gramCharges (GramAssembly.key 2075).leftCharge (GramAssembly.key 2075).rightCharge = raw41488 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41488Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41488 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2075).leftCharge (GramAssembly.key 2075).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2075, Integer.Sparse.eval]

theorem keyMoment2076 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2076) =
      Integer.Sparse.eval keyMomentRow2076 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2076).leftCharge (GramAssembly.key 2076).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2029) := by
    have ha : gramCharges (GramAssembly.key 2076).leftCharge (GramAssembly.key 2076).rightCharge = raw41489 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41489Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41489 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2076).leftCharge (GramAssembly.key 2076).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2076, Integer.Sparse.eval]

theorem keyMoment2077 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2077) =
      Integer.Sparse.eval keyMomentRow2077 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2077).leftCharge (GramAssembly.key 2077).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1967) := by
    have ha : gramCharges (GramAssembly.key 2077).leftCharge (GramAssembly.key 2077).rightCharge = raw41490 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41490Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41490 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2077).leftCharge (GramAssembly.key 2077).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2077, Integer.Sparse.eval]

theorem keyMoment2078 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2078) =
      Integer.Sparse.eval keyMomentRow2078 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2078).leftCharge (GramAssembly.key 2078).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3709) := by
    have ha : gramCharges (GramAssembly.key 2078).leftCharge (GramAssembly.key 2078).rightCharge = raw41491 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41491Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41491 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2078).leftCharge (GramAssembly.key 2078).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2078, Integer.Sparse.eval]

theorem keyMoment2079 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2079) =
      Integer.Sparse.eval keyMomentRow2079 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2079).leftCharge (GramAssembly.key 2079).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3779) := by
    have ha : gramCharges (GramAssembly.key 2079).leftCharge (GramAssembly.key 2079).rightCharge = raw41492 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41492Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41492 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2079).leftCharge (GramAssembly.key 2079).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2079, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2048 : keyMomentRows (2048 : Fin 2886) =
    keyMomentRow2048 := by decide +kernel

theorem keyMomentRowsAt2049 : keyMomentRows (2049 : Fin 2886) =
    keyMomentRow2049 := by decide +kernel

theorem keyMomentRowsAt2050 : keyMomentRows (2050 : Fin 2886) =
    keyMomentRow2050 := by decide +kernel

theorem keyMomentRowsAt2051 : keyMomentRows (2051 : Fin 2886) =
    keyMomentRow2051 := by decide +kernel

theorem keyMomentRowsAt2052 : keyMomentRows (2052 : Fin 2886) =
    keyMomentRow2052 := by decide +kernel

theorem keyMomentRowsAt2053 : keyMomentRows (2053 : Fin 2886) =
    keyMomentRow2053 := by decide +kernel

theorem keyMomentRowsAt2054 : keyMomentRows (2054 : Fin 2886) =
    keyMomentRow2054 := by decide +kernel

theorem keyMomentRowsAt2055 : keyMomentRows (2055 : Fin 2886) =
    keyMomentRow2055 := by decide +kernel

theorem keyMomentRowsAt2056 : keyMomentRows (2056 : Fin 2886) =
    keyMomentRow2056 := by decide +kernel

theorem keyMomentRowsAt2057 : keyMomentRows (2057 : Fin 2886) =
    keyMomentRow2057 := by decide +kernel

theorem keyMomentRowsAt2058 : keyMomentRows (2058 : Fin 2886) =
    keyMomentRow2058 := by decide +kernel

theorem keyMomentRowsAt2059 : keyMomentRows (2059 : Fin 2886) =
    keyMomentRow2059 := by decide +kernel

theorem keyMomentRowsAt2060 : keyMomentRows (2060 : Fin 2886) =
    keyMomentRow2060 := by decide +kernel

theorem keyMomentRowsAt2061 : keyMomentRows (2061 : Fin 2886) =
    keyMomentRow2061 := by decide +kernel

theorem keyMomentRowsAt2062 : keyMomentRows (2062 : Fin 2886) =
    keyMomentRow2062 := by decide +kernel

theorem keyMomentRowsAt2063 : keyMomentRows (2063 : Fin 2886) =
    keyMomentRow2063 := by decide +kernel

theorem keyMomentRowsAt2064 : keyMomentRows (2064 : Fin 2886) =
    keyMomentRow2064 := by decide +kernel

theorem keyMomentRowsAt2065 : keyMomentRows (2065 : Fin 2886) =
    keyMomentRow2065 := by decide +kernel

theorem keyMomentRowsAt2066 : keyMomentRows (2066 : Fin 2886) =
    keyMomentRow2066 := by decide +kernel

theorem keyMomentRowsAt2067 : keyMomentRows (2067 : Fin 2886) =
    keyMomentRow2067 := by decide +kernel

theorem keyMomentRowsAt2068 : keyMomentRows (2068 : Fin 2886) =
    keyMomentRow2068 := by decide +kernel

theorem keyMomentRowsAt2069 : keyMomentRows (2069 : Fin 2886) =
    keyMomentRow2069 := by decide +kernel

theorem keyMomentRowsAt2070 : keyMomentRows (2070 : Fin 2886) =
    keyMomentRow2070 := by decide +kernel

theorem keyMomentRowsAt2071 : keyMomentRows (2071 : Fin 2886) =
    keyMomentRow2071 := by decide +kernel

theorem keyMomentRowsAt2072 : keyMomentRows (2072 : Fin 2886) =
    keyMomentRow2072 := by decide +kernel

theorem keyMomentRowsAt2073 : keyMomentRows (2073 : Fin 2886) =
    keyMomentRow2073 := by decide +kernel

theorem keyMomentRowsAt2074 : keyMomentRows (2074 : Fin 2886) =
    keyMomentRow2074 := by decide +kernel

theorem keyMomentRowsAt2075 : keyMomentRows (2075 : Fin 2886) =
    keyMomentRow2075 := by decide +kernel

theorem keyMomentRowsAt2076 : keyMomentRows (2076 : Fin 2886) =
    keyMomentRow2076 := by decide +kernel

theorem keyMomentRowsAt2077 : keyMomentRows (2077 : Fin 2886) =
    keyMomentRow2077 := by decide +kernel

theorem keyMomentRowsAt2078 : keyMomentRows (2078 : Fin 2886) =
    keyMomentRow2078 := by decide +kernel

theorem keyMomentRowsAt2079 : keyMomentRows (2079 : Fin 2886) =
    keyMomentRow2079 := by decide +kernel

theorem keyMomentChunkSound64_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 64) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2048 ∨ k.val = 2049 ∨ k.val = 2050 ∨ k.val = 2051 ∨ k.val = 2052 ∨ k.val = 2053 ∨ k.val = 2054 ∨ k.val = 2055 ∨ k.val = 2056 ∨ k.val = 2057 ∨ k.val = 2058 ∨ k.val = 2059 ∨ k.val = 2060 ∨ k.val = 2061 ∨ k.val = 2062 ∨ k.val = 2063 ∨ k.val = 2064 ∨ k.val = 2065 ∨ k.val = 2066 ∨ k.val = 2067 ∨ k.val = 2068 ∨ k.val = 2069 ∨ k.val = 2070 ∨ k.val = 2071 ∨ k.val = 2072 ∨ k.val = 2073 ∨ k.val = 2074 ∨ k.val = 2075 ∨ k.val = 2076 ∨ k.val = 2077 ∨ k.val = 2078 ∨ k.val = 2079 := by omega
  rcases heq with h2048 | h2049 | h2050 | h2051 | h2052 | h2053 | h2054 | h2055 | h2056 | h2057 | h2058 | h2059 | h2060 | h2061 | h2062 | h2063 | h2064 | h2065 | h2066 | h2067 | h2068 | h2069 | h2070 | h2071 | h2072 | h2073 | h2074 | h2075 | h2076 | h2077 | h2078 | h2079
  · have he : k = (2048 : Fin 2886) := Fin.ext h2048
    subst k
    rw [keyMomentRowsAt2048]
    exact keyMoment2048 B hB
  · have he : k = (2049 : Fin 2886) := Fin.ext h2049
    subst k
    rw [keyMomentRowsAt2049]
    exact keyMoment2049 B hB
  · have he : k = (2050 : Fin 2886) := Fin.ext h2050
    subst k
    rw [keyMomentRowsAt2050]
    exact keyMoment2050 B hB
  · have he : k = (2051 : Fin 2886) := Fin.ext h2051
    subst k
    rw [keyMomentRowsAt2051]
    exact keyMoment2051 B hB
  · have he : k = (2052 : Fin 2886) := Fin.ext h2052
    subst k
    rw [keyMomentRowsAt2052]
    exact keyMoment2052 B hB
  · have he : k = (2053 : Fin 2886) := Fin.ext h2053
    subst k
    rw [keyMomentRowsAt2053]
    exact keyMoment2053 B hB
  · have he : k = (2054 : Fin 2886) := Fin.ext h2054
    subst k
    rw [keyMomentRowsAt2054]
    exact keyMoment2054 B hB
  · have he : k = (2055 : Fin 2886) := Fin.ext h2055
    subst k
    rw [keyMomentRowsAt2055]
    exact keyMoment2055 B hB
  · have he : k = (2056 : Fin 2886) := Fin.ext h2056
    subst k
    rw [keyMomentRowsAt2056]
    exact keyMoment2056 B hB
  · have he : k = (2057 : Fin 2886) := Fin.ext h2057
    subst k
    rw [keyMomentRowsAt2057]
    exact keyMoment2057 B hB
  · have he : k = (2058 : Fin 2886) := Fin.ext h2058
    subst k
    rw [keyMomentRowsAt2058]
    exact keyMoment2058 B hB
  · have he : k = (2059 : Fin 2886) := Fin.ext h2059
    subst k
    rw [keyMomentRowsAt2059]
    exact keyMoment2059 B hB
  · have he : k = (2060 : Fin 2886) := Fin.ext h2060
    subst k
    rw [keyMomentRowsAt2060]
    exact keyMoment2060 B hB
  · have he : k = (2061 : Fin 2886) := Fin.ext h2061
    subst k
    rw [keyMomentRowsAt2061]
    exact keyMoment2061 B hB
  · have he : k = (2062 : Fin 2886) := Fin.ext h2062
    subst k
    rw [keyMomentRowsAt2062]
    exact keyMoment2062 B hB
  · have he : k = (2063 : Fin 2886) := Fin.ext h2063
    subst k
    rw [keyMomentRowsAt2063]
    exact keyMoment2063 B hB
  · have he : k = (2064 : Fin 2886) := Fin.ext h2064
    subst k
    rw [keyMomentRowsAt2064]
    exact keyMoment2064 B hB
  · have he : k = (2065 : Fin 2886) := Fin.ext h2065
    subst k
    rw [keyMomentRowsAt2065]
    exact keyMoment2065 B hB
  · have he : k = (2066 : Fin 2886) := Fin.ext h2066
    subst k
    rw [keyMomentRowsAt2066]
    exact keyMoment2066 B hB
  · have he : k = (2067 : Fin 2886) := Fin.ext h2067
    subst k
    rw [keyMomentRowsAt2067]
    exact keyMoment2067 B hB
  · have he : k = (2068 : Fin 2886) := Fin.ext h2068
    subst k
    rw [keyMomentRowsAt2068]
    exact keyMoment2068 B hB
  · have he : k = (2069 : Fin 2886) := Fin.ext h2069
    subst k
    rw [keyMomentRowsAt2069]
    exact keyMoment2069 B hB
  · have he : k = (2070 : Fin 2886) := Fin.ext h2070
    subst k
    rw [keyMomentRowsAt2070]
    exact keyMoment2070 B hB
  · have he : k = (2071 : Fin 2886) := Fin.ext h2071
    subst k
    rw [keyMomentRowsAt2071]
    exact keyMoment2071 B hB
  · have he : k = (2072 : Fin 2886) := Fin.ext h2072
    subst k
    rw [keyMomentRowsAt2072]
    exact keyMoment2072 B hB
  · have he : k = (2073 : Fin 2886) := Fin.ext h2073
    subst k
    rw [keyMomentRowsAt2073]
    exact keyMoment2073 B hB
  · have he : k = (2074 : Fin 2886) := Fin.ext h2074
    subst k
    rw [keyMomentRowsAt2074]
    exact keyMoment2074 B hB
  · have he : k = (2075 : Fin 2886) := Fin.ext h2075
    subst k
    rw [keyMomentRowsAt2075]
    exact keyMoment2075 B hB
  · have he : k = (2076 : Fin 2886) := Fin.ext h2076
    subst k
    rw [keyMomentRowsAt2076]
    exact keyMoment2076 B hB
  · have he : k = (2077 : Fin 2886) := Fin.ext h2077
    subst k
    rw [keyMomentRowsAt2077]
    exact keyMoment2077 B hB
  · have he : k = (2078 : Fin 2886) := Fin.ext h2078
    subst k
    rw [keyMomentRowsAt2078]
    exact keyMoment2078 B hB
  · have he : k = (2079 : Fin 2886) := Fin.ext h2079
    subst k
    rw [keyMomentRowsAt2079]
    exact keyMoment2079 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound64_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound64_e_oai
