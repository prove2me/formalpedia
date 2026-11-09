-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound61_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:59:11.181923+00:00
-- url     : https://prove2.me/submissions/8f91eaac-4ea1-4d79-af88-74487fae979d

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

theorem canonical41365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41365 raw41365Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw41365 raw41365Labels = mixedMoment B raw41365step0 raw41365step0Labels := by
      have ha : raw41365step0 = (fun i j => raw41365 (permutation416 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41365step0 raw41365; decide +kernel
      have hl : raw41365step0Labels = raw41365Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41365 raw41365Labels permutation416 permutation6
    _ = mixedMoment B node3721 node3721Labels := by rfl

theorem canonical41366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41366 raw41366Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw41366 raw41366Labels = mixedMoment B raw41366step0 raw41366step0Labels := by
      have ha : raw41366step0 = (fun i j => raw41366 (permutation402 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41366step0 raw41366; decide +kernel
      have hl : raw41366step0Labels = raw41366Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41366 raw41366Labels permutation402 permutation6
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical41367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41367 raw41367Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw41367 raw41367Labels = mixedMoment B raw41367step0 raw41367step0Labels := by
      have ha : raw41367step0 = (fun i j => raw41367 (permutation454 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41367step0 raw41367; decide +kernel
      have hl : raw41367step0Labels = raw41367Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41367 raw41367Labels permutation454 permutation6
    mixedMoment B raw41367step0 raw41367step0Labels = mixedMoment B raw41367step1 raw41367step1Labels := by
      have ha : raw41367step1 = -raw41367step0 := by apply Matrix.ext; change ∀ i j, raw41367step1 i j = -(raw41367step0 i j); unfold raw41367step1 raw41367step0; decide +kernel
      have hl : raw41367step1Labels = raw41367step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3689 node3689Labels := by rfl

theorem canonical41368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41368 raw41368Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw41368 raw41368Labels = mixedMoment B raw41368step0 raw41368step0Labels := by
      have hz : ∀ j, raw41368 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41368step0 = (fun i j => raw41368 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41368step0 raw41368; decide +kernel
      have hl : raw41368step0Labels = raw41368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41368 raw41368Labels permutation520 hz
    mixedMoment B raw41368step0 raw41368step0Labels = mixedMoment B raw41368step1 raw41368step1Labels := by
      have ha : raw41368step1 = (fun i j => raw41368step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41368step1 raw41368step0; decide +kernel
      have hl : raw41368step1Labels = raw41368step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41368step0 raw41368step0Labels permutation145 permutation3
    mixedMoment B raw41368step1 raw41368step1Labels = mixedMoment B raw41368step2 raw41368step2Labels := by
      have ha : raw41368step2 = -raw41368step1 := by apply Matrix.ext; change ∀ i j, raw41368step2 i j = -(raw41368step1 i j); unfold raw41368step2 raw41368step1; decide +kernel
      have hl : raw41368step2Labels = raw41368step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3910 node3910Labels := by rfl

theorem canonical41369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41369 raw41369Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw41369 raw41369Labels = mixedMoment B raw41369step0 raw41369step0Labels := by
      have ha : raw41369step0 = (fun i j => raw41369 (permutation529 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41369step0 raw41369; decide +kernel
      have hl : raw41369step0Labels = raw41369Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41369 raw41369Labels permutation529 permutation6
    mixedMoment B raw41369step0 raw41369step0Labels = mixedMoment B raw41369step1 raw41369step1Labels := by
      have ha : raw41369step1 = -raw41369step0 := by apply Matrix.ext; change ∀ i j, raw41369step1 i j = -(raw41369step0 i j); unfold raw41369step1 raw41369step0; decide +kernel
      have hl : raw41369step1Labels = raw41369step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3692 node3692Labels := by rfl

theorem canonical41370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41370 raw41370Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw41370 raw41370Labels = mixedMoment B raw41370step0 raw41370step0Labels := by
      have hz : ∀ j, raw41370 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41370step0 = (fun i j => raw41370 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41370step0 raw41370; decide +kernel
      have hl : raw41370step0Labels = raw41370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41370 raw41370Labels permutation434 hz
    mixedMoment B raw41370step0 raw41370step0Labels = mixedMoment B raw41370step1 raw41370step1Labels := by
      have ha : raw41370step1 = (fun i j => raw41370step0 (permutation140 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41370step1 raw41370step0; decide +kernel
      have hl : raw41370step1Labels = raw41370step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41370step0 raw41370step0Labels permutation140 permutation6
    _ = mixedMoment B node2931 node2931Labels := by rfl

theorem canonical41371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41371 raw41371Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw41371 raw41371Labels = mixedMoment B raw41371step0 raw41371step0Labels := by
      have hz : ∀ j, raw41371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41371step0 = (fun i j => raw41371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41371step0 raw41371; decide +kernel
      have hl : raw41371step0Labels = raw41371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41371 raw41371Labels permutation434 hz
    mixedMoment B raw41371step0 raw41371step0Labels = mixedMoment B raw41371step1 raw41371step1Labels := by
      have ha : raw41371step1 = (fun i j => raw41371step0 (permutation74 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41371step1 raw41371step0; decide +kernel
      have hl : raw41371step1Labels = raw41371step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41371step0 raw41371step0Labels permutation74 permutation6
    mixedMoment B raw41371step1 raw41371step1Labels = mixedMoment B raw41371step2 raw41371step2Labels := by
      have ha : raw41371step2 = -raw41371step1 := by apply Matrix.ext; change ∀ i j, raw41371step2 i j = -(raw41371step1 i j); unfold raw41371step2 raw41371step1; decide +kernel
      have hl : raw41371step2Labels = raw41371step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical41372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41372 raw41372Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw41372 raw41372Labels = mixedMoment B raw41372step0 raw41372step0Labels := by
      have hz : ∀ j, raw41372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41372step0 = (fun i j => raw41372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41372step0 raw41372; decide +kernel
      have hl : raw41372step0Labels = raw41372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41372 raw41372Labels permutation434 hz
    mixedMoment B raw41372step0 raw41372step0Labels = mixedMoment B raw41372step1 raw41372step1Labels := by
      have hz : ∀ j, raw41372step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41372step1 = (fun i j => raw41372step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41372step1 raw41372step0; decide +kernel
      have hl : raw41372step1Labels = raw41372step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41372step0 raw41372step0Labels permutation80 hz
    mixedMoment B raw41372step1 raw41372step1Labels = mixedMoment B raw41372step2 raw41372step2Labels := by
      have ha : raw41372step2 = (fun i j => raw41372step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41372step2 raw41372step1; decide +kernel
      have hl : raw41372step2Labels = raw41372step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41372step1 raw41372step1Labels permutation26 permutation6
    _ = mixedMoment B node1246 node1246Labels := by rfl

theorem canonical41373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41373 raw41373Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw41373 raw41373Labels = mixedMoment B raw41373step0 raw41373step0Labels := by
      have hz : ∀ j, raw41373 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41373step0 = (fun i j => raw41373 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41373step0 raw41373; decide +kernel
      have hl : raw41373step0Labels = raw41373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41373 raw41373Labels permutation434 hz
    mixedMoment B raw41373step0 raw41373step0Labels = mixedMoment B raw41373step1 raw41373step1Labels := by
      have hz : ∀ j, raw41373step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41373step1 = (fun i j => raw41373step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41373step1 raw41373step0; decide +kernel
      have hl : raw41373step1Labels = raw41373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41373step0 raw41373step0Labels permutation80 hz
    mixedMoment B raw41373step1 raw41373step1Labels = mixedMoment B raw41373step2 raw41373step2Labels := by
      have ha : raw41373step2 = (fun i j => raw41373step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41373step2 raw41373step1; decide +kernel
      have hl : raw41373step2Labels = raw41373step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41373step1 raw41373step1Labels permutation21 permutation6
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical41374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41374 raw41374Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw41374 raw41374Labels = mixedMoment B raw41374step0 raw41374step0Labels := by
      have hz : ∀ j, raw41374 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41374step0 = (fun i j => raw41374 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41374step0 raw41374; decide +kernel
      have hl : raw41374step0Labels = raw41374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41374 raw41374Labels permutation346 hz
    mixedMoment B raw41374step0 raw41374step0Labels = mixedMoment B raw41374step1 raw41374step1Labels := by
      have ha : raw41374step1 = (fun i j => raw41374step0 (permutation131 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41374step1 raw41374step0; decide +kernel
      have hl : raw41374step1Labels = raw41374step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41374step0 raw41374step0Labels permutation131 permutation6
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical41375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41375 raw41375Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw41375 raw41375Labels = mixedMoment B raw41375step0 raw41375step0Labels := by
      have hz : ∀ j, raw41375 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41375step0 = (fun i j => raw41375 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41375step0 raw41375; decide +kernel
      have hl : raw41375step0Labels = raw41375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41375 raw41375Labels permutation346 hz
    mixedMoment B raw41375step0 raw41375step0Labels = mixedMoment B raw41375step1 raw41375step1Labels := by
      have ha : raw41375step1 = (fun i j => raw41375step0 (permutation109 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41375step1 raw41375step0; decide +kernel
      have hl : raw41375step1Labels = raw41375step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41375step0 raw41375step0Labels permutation109 permutation6
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical41376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41376 raw41376Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw41376 raw41376Labels = mixedMoment B raw41376step0 raw41376step0Labels := by
      have hz : ∀ j, raw41376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41376step0 = (fun i j => raw41376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41376step0 raw41376; decide +kernel
      have hl : raw41376step0Labels = raw41376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41376 raw41376Labels permutation346 hz
    mixedMoment B raw41376step0 raw41376step0Labels = mixedMoment B raw41376step1 raw41376step1Labels := by
      have ha : raw41376step1 = (fun i j => raw41376step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41376step1 raw41376step0; decide +kernel
      have hl : raw41376step1Labels = raw41376step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41376step0 raw41376step0Labels permutation122 permutation6
    _ = mixedMoment B node2561 node2561Labels := by rfl

theorem canonical41377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41377 raw41377Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw41377 raw41377Labels = mixedMoment B raw41377step0 raw41377step0Labels := by
      have ha : raw41377step0 = (fun i j => raw41377 (permutation572 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41377step0 raw41377; decide +kernel
      have hl : raw41377step0Labels = raw41377Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41377 raw41377Labels permutation572 permutation6
    _ = mixedMoment B node2556 node2556Labels := by rfl

theorem canonical41378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41378 raw41378Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw41378 raw41378Labels = mixedMoment B raw41378step0 raw41378step0Labels := by
      have hz : ∀ j, raw41378 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41378step0 = (fun i j => raw41378 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41378step0 raw41378; decide +kernel
      have hl : raw41378step0Labels = raw41378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41378 raw41378Labels permutation520 hz
    mixedMoment B raw41378step0 raw41378step0Labels = mixedMoment B raw41378step1 raw41378step1Labels := by
      have hz : ∀ j, raw41378step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41378step1 = (fun i j => raw41378step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41378step1 raw41378step0; decide +kernel
      have hl : raw41378step1Labels = raw41378step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41378step0 raw41378step0Labels permutation104 hz
    mixedMoment B raw41378step1 raw41378step1Labels = mixedMoment B raw41378step2 raw41378step2Labels := by
      have ha : raw41378step2 = (fun i j => raw41378step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41378step2 raw41378step1; decide +kernel
      have hl : raw41378step2Labels = raw41378step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41378step1 raw41378step1Labels permutation15 permutation6
    mixedMoment B raw41378step2 raw41378step2Labels = mixedMoment B raw41378step3 raw41378step3Labels := by
      have ha : raw41378step3 = -raw41378step2 := by apply Matrix.ext; change ∀ i j, raw41378step3 i j = -(raw41378step2 i j); unfold raw41378step3 raw41378step2; decide +kernel
      have hl : raw41378step3Labels = raw41378step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical41379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41379 raw41379Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw41379 raw41379Labels = mixedMoment B raw41379step0 raw41379step0Labels := by
      have hz : ∀ j, raw41379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41379step0 = (fun i j => raw41379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41379step0 raw41379; decide +kernel
      have hl : raw41379step0Labels = raw41379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41379 raw41379Labels permutation434 hz
    mixedMoment B raw41379step0 raw41379step0Labels = mixedMoment B raw41379step1 raw41379step1Labels := by
      have ha : raw41379step1 = (fun i j => raw41379step0 (permutation69 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41379step1 raw41379step0; decide +kernel
      have hl : raw41379step1Labels = raw41379step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41379step0 raw41379step0Labels permutation69 permutation6
    mixedMoment B raw41379step1 raw41379step1Labels = mixedMoment B raw41379step2 raw41379step2Labels := by
      have ha : raw41379step2 = -raw41379step1 := by apply Matrix.ext; change ∀ i j, raw41379step2 i j = -(raw41379step1 i j); unfold raw41379step2 raw41379step1; decide +kernel
      have hl : raw41379step2Labels = raw41379step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2488 node2488Labels := by rfl

theorem canonical41380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41380 raw41380Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw41380 raw41380Labels = mixedMoment B raw41380step0 raw41380step0Labels := by
      have hz : ∀ j, raw41380 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41380step0 = (fun i j => raw41380 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41380step0 raw41380; decide +kernel
      have hl : raw41380step0Labels = raw41380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41380 raw41380Labels permutation434 hz
    mixedMoment B raw41380step0 raw41380step0Labels = mixedMoment B raw41380step1 raw41380step1Labels := by
      have ha : raw41380step1 = (fun i j => raw41380step0 (permutation75 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41380step1 raw41380step0; decide +kernel
      have hl : raw41380step1Labels = raw41380step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41380step0 raw41380step0Labels permutation75 permutation6
    mixedMoment B raw41380step1 raw41380step1Labels = mixedMoment B raw41380step2 raw41380step2Labels := by
      have ha : raw41380step2 = -raw41380step1 := by apply Matrix.ext; change ∀ i j, raw41380step2 i j = -(raw41380step1 i j); unfold raw41380step2 raw41380step1; decide +kernel
      have hl : raw41380step2Labels = raw41380step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical41381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41381 raw41381Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw41381 raw41381Labels = mixedMoment B raw41381step0 raw41381step0Labels := by
      have ha : raw41381step0 = (fun i j => raw41381 (permutation308 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41381step0 raw41381; decide +kernel
      have hl : raw41381step0Labels = raw41381Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41381 raw41381Labels permutation308 permutation6
    mixedMoment B raw41381step0 raw41381step0Labels = mixedMoment B raw41381step1 raw41381step1Labels := by
      have ha : raw41381step1 = -raw41381step0 := by apply Matrix.ext; change ∀ i j, raw41381step1 i j = -(raw41381step0 i j); unfold raw41381step1 raw41381step0; decide +kernel
      have hl : raw41381step1Labels = raw41381step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2479 node2479Labels := by rfl

theorem canonical41382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41382 raw41382Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw41382 raw41382Labels = mixedMoment B raw41382step0 raw41382step0Labels := by
      have hz : ∀ j, raw41382 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41382step0 = (fun i j => raw41382 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41382step0 raw41382; decide +kernel
      have hl : raw41382step0Labels = raw41382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41382 raw41382Labels permutation520 hz
    mixedMoment B raw41382step0 raw41382step0Labels = mixedMoment B raw41382step1 raw41382step1Labels := by
      have ha : raw41382step1 = (fun i j => raw41382step0 (permutation60 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41382step1 raw41382step0; decide +kernel
      have hl : raw41382step1Labels = raw41382step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41382step0 raw41382step0Labels permutation60 permutation6
    mixedMoment B raw41382step1 raw41382step1Labels = mixedMoment B raw41382step2 raw41382step2Labels := by
      have ha : raw41382step2 = -raw41382step1 := by apply Matrix.ext; change ∀ i j, raw41382step2 i j = -(raw41382step1 i j); unfold raw41382step2 raw41382step1; decide +kernel
      have hl : raw41382step2Labels = raw41382step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical41383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41383 raw41383Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw41383 raw41383Labels = mixedMoment B raw41383step0 raw41383step0Labels := by
      have ha : raw41383step0 = (fun i j => raw41383 (permutation322 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41383step0 raw41383; decide +kernel
      have hl : raw41383step0Labels = raw41383Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41383 raw41383Labels permutation322 permutation6
    mixedMoment B raw41383step0 raw41383step0Labels = mixedMoment B raw41383step1 raw41383step1Labels := by
      have ha : raw41383step1 = -raw41383step0 := by apply Matrix.ext; change ∀ i j, raw41383step1 i j = -(raw41383step0 i j); unfold raw41383step1 raw41383step0; decide +kernel
      have hl : raw41383step1Labels = raw41383step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2483 node2483Labels := by rfl

theorem canonical41384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41384 raw41384Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw41384 raw41384Labels = mixedMoment B raw41384step0 raw41384step0Labels := by
      have hz : ∀ j, raw41384 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41384step0 = (fun i j => raw41384 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41384step0 raw41384; decide +kernel
      have hl : raw41384step0Labels = raw41384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41384 raw41384Labels permutation434 hz
    mixedMoment B raw41384step0 raw41384step0Labels = mixedMoment B raw41384step1 raw41384step1Labels := by
      have hz : ∀ j, raw41384step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41384step1 = (fun i j => raw41384step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41384step1 raw41384step0; decide +kernel
      have hl : raw41384step1Labels = raw41384step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41384step0 raw41384step0Labels permutation80 hz
    mixedMoment B raw41384step1 raw41384step1Labels = mixedMoment B raw41384step2 raw41384step2Labels := by
      have ha : raw41384step2 = (fun i j => raw41384step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41384step2 raw41384step1; decide +kernel
      have hl : raw41384step2Labels = raw41384step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41384step1 raw41384step1Labels permutation27 permutation6
    _ = mixedMoment B node1242 node1242Labels := by rfl

theorem canonical41385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41385 raw41385Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw41385 raw41385Labels = mixedMoment B raw41385step0 raw41385step0Labels := by
      have hz : ∀ j, raw41385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41385step0 = (fun i j => raw41385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41385step0 raw41385; decide +kernel
      have hl : raw41385step0Labels = raw41385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41385 raw41385Labels permutation434 hz
    mixedMoment B raw41385step0 raw41385step0Labels = mixedMoment B raw41385step1 raw41385step1Labels := by
      have hz : ∀ j, raw41385step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41385step1 = (fun i j => raw41385step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41385step1 raw41385step0; decide +kernel
      have hl : raw41385step1Labels = raw41385step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41385step0 raw41385step0Labels permutation80 hz
    mixedMoment B raw41385step1 raw41385step1Labels = mixedMoment B raw41385step2 raw41385step2Labels := by
      have ha : raw41385step2 = (fun i j => raw41385step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41385step2 raw41385step1; decide +kernel
      have hl : raw41385step2Labels = raw41385step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41385step1 raw41385step1Labels permutation21 permutation6
    _ = mixedMoment B node2726 node2726Labels := by rfl

theorem canonical41386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41386 raw41386Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw41386 raw41386Labels = mixedMoment B raw41386step0 raw41386step0Labels := by
      have hz : ∀ j, raw41386 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41386step0 = (fun i j => raw41386 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41386step0 raw41386; decide +kernel
      have hl : raw41386step0Labels = raw41386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41386 raw41386Labels permutation346 hz
    mixedMoment B raw41386step0 raw41386step0Labels = mixedMoment B raw41386step1 raw41386step1Labels := by
      have ha : raw41386step1 = (fun i j => raw41386step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41386step1 raw41386step0; decide +kernel
      have hl : raw41386step1Labels = raw41386step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41386step0 raw41386step0Labels permutation63 permutation6
    mixedMoment B raw41386step1 raw41386step1Labels = mixedMoment B raw41386step2 raw41386step2Labels := by
      have ha : raw41386step2 = -raw41386step1 := by apply Matrix.ext; change ∀ i j, raw41386step2 i j = -(raw41386step1 i j); unfold raw41386step2 raw41386step1; decide +kernel
      have hl : raw41386step2Labels = raw41386step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

theorem canonical41387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41387 raw41387Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw41387 raw41387Labels = mixedMoment B raw41387step0 raw41387step0Labels := by
      have hz : ∀ j, raw41387 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41387step0 = (fun i j => raw41387 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41387step0 raw41387; decide +kernel
      have hl : raw41387step0Labels = raw41387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41387 raw41387Labels permutation520 hz
    mixedMoment B raw41387step0 raw41387step0Labels = mixedMoment B raw41387step1 raw41387step1Labels := by
      have hz : ∀ j, raw41387step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41387step1 = (fun i j => raw41387step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41387step1 raw41387step0; decide +kernel
      have hl : raw41387step1Labels = raw41387step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41387step0 raw41387step0Labels permutation104 hz
    mixedMoment B raw41387step1 raw41387step1Labels = mixedMoment B raw41387step2 raw41387step2Labels := by
      have ha : raw41387step2 = (fun i j => raw41387step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41387step2 raw41387step1; decide +kernel
      have hl : raw41387step2Labels = raw41387step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41387step1 raw41387step1Labels permutation15 permutation6
    mixedMoment B raw41387step2 raw41387step2Labels = mixedMoment B raw41387step3 raw41387step3Labels := by
      have ha : raw41387step3 = -raw41387step2 := by apply Matrix.ext; change ∀ i j, raw41387step3 i j = -(raw41387step2 i j); unfold raw41387step3 raw41387step2; decide +kernel
      have hl : raw41387step3Labels = raw41387step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1049 node1049Labels := by rfl

theorem canonical41388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41388 raw41388Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw41388 raw41388Labels = mixedMoment B raw41388step0 raw41388step0Labels := by
      have hz : ∀ j, raw41388 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41388step0 = (fun i j => raw41388 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41388step0 raw41388; decide +kernel
      have hl : raw41388step0Labels = raw41388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41388 raw41388Labels permutation520 hz
    mixedMoment B raw41388step0 raw41388step0Labels = mixedMoment B raw41388step1 raw41388step1Labels := by
      have ha : raw41388step1 = (fun i j => raw41388step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41388step1 raw41388step0; decide +kernel
      have hl : raw41388step1Labels = raw41388step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41388step0 raw41388step0Labels permutation56 permutation6
    mixedMoment B raw41388step1 raw41388step1Labels = mixedMoment B raw41388step2 raw41388step2Labels := by
      have ha : raw41388step2 = -raw41388step1 := by apply Matrix.ext; change ∀ i j, raw41388step2 i j = -(raw41388step1 i j); unfold raw41388step2 raw41388step1; decide +kernel
      have hl : raw41388step2Labels = raw41388step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1044 node1044Labels := by rfl

theorem canonical41389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41389 raw41389Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw41389 raw41389Labels = mixedMoment B raw41389step0 raw41389step0Labels := by
      have hz : ∀ j, raw41389 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41389step0 = (fun i j => raw41389 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41389step0 raw41389; decide +kernel
      have hl : raw41389step0Labels = raw41389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41389 raw41389Labels permutation520 hz
    mixedMoment B raw41389step0 raw41389step0Labels = mixedMoment B raw41389step1 raw41389step1Labels := by
      have hz : ∀ j, raw41389step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41389step1 = (fun i j => raw41389step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41389step1 raw41389step0; decide +kernel
      have hl : raw41389step1Labels = raw41389step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41389step0 raw41389step0Labels permutation104 hz
    mixedMoment B raw41389step1 raw41389step1Labels = mixedMoment B raw41389step2 raw41389step2Labels := by
      have ha : raw41389step2 = (fun i j => raw41389step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41389step2 raw41389step1; decide +kernel
      have hl : raw41389step2Labels = raw41389step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41389step1 raw41389step1Labels permutation14 permutation6
    mixedMoment B raw41389step2 raw41389step2Labels = mixedMoment B raw41389step3 raw41389step3Labels := by
      have ha : raw41389step3 = -raw41389step2 := by apply Matrix.ext; change ∀ i j, raw41389step3 i j = -(raw41389step2 i j); unfold raw41389step3 raw41389step2; decide +kernel
      have hl : raw41389step3Labels = raw41389step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1046 node1046Labels := by rfl

theorem canonical41390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41390 raw41390Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw41390 raw41390Labels = mixedMoment B raw41390step0 raw41390step0Labels := by
      have hz : ∀ j, raw41390 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41390step0 = (fun i j => raw41390 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41390step0 raw41390; decide +kernel
      have hl : raw41390step0Labels = raw41390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41390 raw41390Labels permutation520 hz
    mixedMoment B raw41390step0 raw41390step0Labels = mixedMoment B raw41390step1 raw41390step1Labels := by
      have hz : ∀ j, raw41390step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41390step1 = (fun i j => raw41390step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41390step1 raw41390step0; decide +kernel
      have hl : raw41390step1Labels = raw41390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41390step0 raw41390step0Labels permutation104 hz
    mixedMoment B raw41390step1 raw41390step1Labels = mixedMoment B raw41390step2 raw41390step2Labels := by
      have hz : ∀ j, raw41390step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41390step2 = (fun i j => raw41390step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41390step2 raw41390step1; decide +kernel
      have hl : raw41390step2Labels = raw41390step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41390step1 raw41390step1Labels permutation20 hz
    mixedMoment B raw41390step2 raw41390step2Labels = mixedMoment B raw41390step3 raw41390step3Labels := by
      have ha : raw41390step3 = (fun i j => raw41390step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41390step3 raw41390step2; decide +kernel
      have hl : raw41390step3Labels = raw41390step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41390step2 raw41390step2Labels permutation4 permutation6
    mixedMoment B raw41390step3 raw41390step3Labels = mixedMoment B raw41390step4 raw41390step4Labels := by
      have ha : raw41390step4 = -raw41390step3 := by apply Matrix.ext; change ∀ i j, raw41390step4 i j = -(raw41390step3 i j); unfold raw41390step4 raw41390step3; decide +kernel
      have hl : raw41390step4Labels = raw41390step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1051 node1051Labels := by rfl

theorem canonical41391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41391 raw41391Labels = mixedMoment B node2131 node2131Labels := by
  calc
    mixedMoment B raw41391 raw41391Labels = mixedMoment B raw41391step0 raw41391step0Labels := by
      have ha : raw41391step0 = (fun i j => raw41391 (permutation505 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41391step0 raw41391; decide +kernel
      have hl : raw41391step0Labels = raw41391Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41391 raw41391Labels permutation505 permutation6
    _ = mixedMoment B node2131 node2131Labels := by rfl

theorem canonical41392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41392 raw41392Labels = mixedMoment B node1821 node1821Labels := by
  calc
    mixedMoment B raw41392 raw41392Labels = mixedMoment B raw41392step0 raw41392step0Labels := by
      have ha : raw41392step0 = (fun i j => raw41392 (permutation505 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41392step0 raw41392; decide +kernel
      have hl : raw41392step0Labels = raw41392Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41392 raw41392Labels permutation505 permutation6
    _ = mixedMoment B node1821 node1821Labels := by rfl

theorem canonical41393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41393 raw41393Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw41393 raw41393Labels = mixedMoment B raw41393step0 raw41393step0Labels := by
      have ha : raw41393step0 = (fun i j => raw41393 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41393step0 raw41393; decide +kernel
      have hl : raw41393step0Labels = raw41393Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41393 raw41393Labels permutation499 permutation6
    _ = mixedMoment B node2252 node2252Labels := by rfl

theorem canonical41394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41394 raw41394Labels = mixedMoment B node2104 node2104Labels := by
  calc
    mixedMoment B raw41394 raw41394Labels = mixedMoment B raw41394step0 raw41394step0Labels := by
      have ha : raw41394step0 = (fun i j => raw41394 (permutation505 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41394step0 raw41394; decide +kernel
      have hl : raw41394step0Labels = raw41394Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41394 raw41394Labels permutation505 permutation6
    _ = mixedMoment B node2104 node2104Labels := by rfl

theorem canonical41395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41395 raw41395Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw41395 raw41395Labels = mixedMoment B raw41395step0 raw41395step0Labels := by
      have ha : raw41395step0 = (fun i j => raw41395 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41395step0 raw41395; decide +kernel
      have hl : raw41395step0Labels = raw41395Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41395 raw41395Labels permutation683 permutation3
    mixedMoment B raw41395step0 raw41395step0Labels = mixedMoment B raw41395step1 raw41395step1Labels := by
      have ha : raw41395step1 = -raw41395step0 := by apply Matrix.ext; change ∀ i j, raw41395step1 i j = -(raw41395step0 i j); unfold raw41395step1 raw41395step0; decide +kernel
      have hl : raw41395step1Labels = raw41395step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2252 node2252Labels := by rfl

theorem canonical41396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41396 raw41396Labels = mixedMoment B node2806 node2806Labels := by
  calc
    mixedMoment B raw41396 raw41396Labels = mixedMoment B raw41396step0 raw41396step0Labels := by
      have ha : raw41396step0 = (fun i j => raw41396 (permutation647 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41396step0 raw41396; decide +kernel
      have hl : raw41396step0Labels = raw41396Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41396 raw41396Labels permutation647 permutation6
    _ = mixedMoment B node2806 node2806Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1952 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1952) =
      Integer.Sparse.eval keyMomentRow1952 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1952).leftCharge (GramAssembly.key 1952).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3721) := by
    have ha : gramCharges (GramAssembly.key 1952).leftCharge (GramAssembly.key 1952).rightCharge = raw41365 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41365Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41365 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1952).leftCharge (GramAssembly.key 1952).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1952, Integer.Sparse.eval]

theorem keyMoment1953 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1953) =
      Integer.Sparse.eval keyMomentRow1953 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1953).leftCharge (GramAssembly.key 1953).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3838) := by
    have ha : gramCharges (GramAssembly.key 1953).leftCharge (GramAssembly.key 1953).rightCharge = raw41366 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41366Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41366 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1953).leftCharge (GramAssembly.key 1953).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1953, Integer.Sparse.eval]

theorem keyMoment1954 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1954) =
      Integer.Sparse.eval keyMomentRow1954 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1954).leftCharge (GramAssembly.key 1954).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3689) := by
    have ha : gramCharges (GramAssembly.key 1954).leftCharge (GramAssembly.key 1954).rightCharge = raw41367 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41367Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41367 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1954).leftCharge (GramAssembly.key 1954).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1954, Integer.Sparse.eval]

theorem keyMoment1955 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1955) =
      Integer.Sparse.eval keyMomentRow1955 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1955).leftCharge (GramAssembly.key 1955).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3910) := by
    have ha : gramCharges (GramAssembly.key 1955).leftCharge (GramAssembly.key 1955).rightCharge = raw41368 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41368Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41368 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1955).leftCharge (GramAssembly.key 1955).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1955, Integer.Sparse.eval]

theorem keyMoment1956 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1956) =
      Integer.Sparse.eval keyMomentRow1956 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1956).leftCharge (GramAssembly.key 1956).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3692) := by
    have ha : gramCharges (GramAssembly.key 1956).leftCharge (GramAssembly.key 1956).rightCharge = raw41369 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41369Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41369 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1956).leftCharge (GramAssembly.key 1956).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1956, Integer.Sparse.eval]

theorem keyMoment1957 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1957) =
      Integer.Sparse.eval keyMomentRow1957 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1957).leftCharge (GramAssembly.key 1957).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2931) := by
    have ha : gramCharges (GramAssembly.key 1957).leftCharge (GramAssembly.key 1957).rightCharge = raw41370 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41370Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41370 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1957).leftCharge (GramAssembly.key 1957).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1957, Integer.Sparse.eval]

theorem keyMoment1958 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1958) =
      Integer.Sparse.eval keyMomentRow1958 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1958).leftCharge (GramAssembly.key 1958).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3958) := by
    have ha : gramCharges (GramAssembly.key 1958).leftCharge (GramAssembly.key 1958).rightCharge = raw41371 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41371Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41371 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1958).leftCharge (GramAssembly.key 1958).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1958, Integer.Sparse.eval]

theorem keyMoment1959 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1959) =
      Integer.Sparse.eval keyMomentRow1959 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1959).leftCharge (GramAssembly.key 1959).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1246) := by
    have ha : gramCharges (GramAssembly.key 1959).leftCharge (GramAssembly.key 1959).rightCharge = raw41372 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41372Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41372 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1959).leftCharge (GramAssembly.key 1959).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1959, Integer.Sparse.eval]

theorem keyMoment1960 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1960) =
      Integer.Sparse.eval keyMomentRow1960 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1960).leftCharge (GramAssembly.key 1960).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2743) := by
    have ha : gramCharges (GramAssembly.key 1960).leftCharge (GramAssembly.key 1960).rightCharge = raw41373 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41373Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41373 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1960).leftCharge (GramAssembly.key 1960).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1960, Integer.Sparse.eval]

theorem keyMoment1961 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1961) =
      Integer.Sparse.eval keyMomentRow1961 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1961).leftCharge (GramAssembly.key 1961).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1240) := by
    have ha : gramCharges (GramAssembly.key 1961).leftCharge (GramAssembly.key 1961).rightCharge = raw41374 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41374Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41374 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1961).leftCharge (GramAssembly.key 1961).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1961, Integer.Sparse.eval]

theorem keyMoment1962 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1962) =
      Integer.Sparse.eval keyMomentRow1962 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1962).leftCharge (GramAssembly.key 1962).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2723) := by
    have ha : gramCharges (GramAssembly.key 1962).leftCharge (GramAssembly.key 1962).rightCharge = raw41375 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41375Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41375 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1962).leftCharge (GramAssembly.key 1962).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1962, Integer.Sparse.eval]

theorem keyMoment1963 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1963) =
      Integer.Sparse.eval keyMomentRow1963 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1963).leftCharge (GramAssembly.key 1963).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2561) := by
    have ha : gramCharges (GramAssembly.key 1963).leftCharge (GramAssembly.key 1963).rightCharge = raw41376 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41376Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41376 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1963).leftCharge (GramAssembly.key 1963).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1963, Integer.Sparse.eval]

theorem keyMoment1964 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1964) =
      Integer.Sparse.eval keyMomentRow1964 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1964).leftCharge (GramAssembly.key 1964).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2556) := by
    have ha : gramCharges (GramAssembly.key 1964).leftCharge (GramAssembly.key 1964).rightCharge = raw41377 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41377Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41377 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1964).leftCharge (GramAssembly.key 1964).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1964, Integer.Sparse.eval]

theorem keyMoment1965 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1965) =
      Integer.Sparse.eval keyMomentRow1965 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1965).leftCharge (GramAssembly.key 1965).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2765) := by
    have ha : gramCharges (GramAssembly.key 1965).leftCharge (GramAssembly.key 1965).rightCharge = raw41378 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41378Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41378 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1965).leftCharge (GramAssembly.key 1965).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1965, Integer.Sparse.eval]

theorem keyMoment1966 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1966) =
      Integer.Sparse.eval keyMomentRow1966 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1966).leftCharge (GramAssembly.key 1966).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2488) := by
    have ha : gramCharges (GramAssembly.key 1966).leftCharge (GramAssembly.key 1966).rightCharge = raw41379 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41379Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41379 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1966).leftCharge (GramAssembly.key 1966).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1966, Integer.Sparse.eval]

theorem keyMoment1967 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1967) =
      Integer.Sparse.eval keyMomentRow1967 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1967).leftCharge (GramAssembly.key 1967).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2722) := by
    have ha : gramCharges (GramAssembly.key 1967).leftCharge (GramAssembly.key 1967).rightCharge = raw41380 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41380Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41380 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1967).leftCharge (GramAssembly.key 1967).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1967, Integer.Sparse.eval]

theorem keyMoment1968 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1968) =
      Integer.Sparse.eval keyMomentRow1968 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1968).leftCharge (GramAssembly.key 1968).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2479) := by
    have ha : gramCharges (GramAssembly.key 1968).leftCharge (GramAssembly.key 1968).rightCharge = raw41381 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41381Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41381 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1968).leftCharge (GramAssembly.key 1968).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1968, Integer.Sparse.eval]

theorem keyMoment1969 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1969) =
      Integer.Sparse.eval keyMomentRow1969 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1969).leftCharge (GramAssembly.key 1969).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2764) := by
    have ha : gramCharges (GramAssembly.key 1969).leftCharge (GramAssembly.key 1969).rightCharge = raw41382 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41382Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41382 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1969).leftCharge (GramAssembly.key 1969).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1969, Integer.Sparse.eval]

theorem keyMoment1970 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1970) =
      Integer.Sparse.eval keyMomentRow1970 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1970).leftCharge (GramAssembly.key 1970).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2483) := by
    have ha : gramCharges (GramAssembly.key 1970).leftCharge (GramAssembly.key 1970).rightCharge = raw41383 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41383Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41383 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1970).leftCharge (GramAssembly.key 1970).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1970, Integer.Sparse.eval]

theorem keyMoment1971 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1971) =
      Integer.Sparse.eval keyMomentRow1971 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1971).leftCharge (GramAssembly.key 1971).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1242) := by
    have ha : gramCharges (GramAssembly.key 1971).leftCharge (GramAssembly.key 1971).rightCharge = raw41384 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41384Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41384 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1971).leftCharge (GramAssembly.key 1971).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1971, Integer.Sparse.eval]

theorem keyMoment1972 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1972) =
      Integer.Sparse.eval keyMomentRow1972 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1972).leftCharge (GramAssembly.key 1972).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2726) := by
    have ha : gramCharges (GramAssembly.key 1972).leftCharge (GramAssembly.key 1972).rightCharge = raw41385 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41385Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41385 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1972).leftCharge (GramAssembly.key 1972).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1972, Integer.Sparse.eval]

theorem keyMoment1973 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1973) =
      Integer.Sparse.eval keyMomentRow1973 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1973).leftCharge (GramAssembly.key 1973).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2482) := by
    have ha : gramCharges (GramAssembly.key 1973).leftCharge (GramAssembly.key 1973).rightCharge = raw41386 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41386Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41386 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1973).leftCharge (GramAssembly.key 1973).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1973, Integer.Sparse.eval]

theorem keyMoment1974 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1974) =
      Integer.Sparse.eval keyMomentRow1974 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1974).leftCharge (GramAssembly.key 1974).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1049) := by
    have ha : gramCharges (GramAssembly.key 1974).leftCharge (GramAssembly.key 1974).rightCharge = raw41387 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41387Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41387 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1974).leftCharge (GramAssembly.key 1974).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1974, Integer.Sparse.eval]

theorem keyMoment1975 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1975) =
      Integer.Sparse.eval keyMomentRow1975 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1975).leftCharge (GramAssembly.key 1975).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1044) := by
    have ha : gramCharges (GramAssembly.key 1975).leftCharge (GramAssembly.key 1975).rightCharge = raw41388 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41388Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41388 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1975).leftCharge (GramAssembly.key 1975).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1975, Integer.Sparse.eval]

theorem keyMoment1976 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1976) =
      Integer.Sparse.eval keyMomentRow1976 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1976).leftCharge (GramAssembly.key 1976).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1046) := by
    have ha : gramCharges (GramAssembly.key 1976).leftCharge (GramAssembly.key 1976).rightCharge = raw41389 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41389Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41389 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1976).leftCharge (GramAssembly.key 1976).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1976, Integer.Sparse.eval]

theorem keyMoment1977 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1977) =
      Integer.Sparse.eval keyMomentRow1977 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1977).leftCharge (GramAssembly.key 1977).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1051) := by
    have ha : gramCharges (GramAssembly.key 1977).leftCharge (GramAssembly.key 1977).rightCharge = raw41390 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41390Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41390 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1977).leftCharge (GramAssembly.key 1977).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1977, Integer.Sparse.eval]

theorem keyMoment1978 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1978) =
      Integer.Sparse.eval keyMomentRow1978 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1978).leftCharge (GramAssembly.key 1978).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2131) := by
    have ha : gramCharges (GramAssembly.key 1978).leftCharge (GramAssembly.key 1978).rightCharge = raw41391 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41391Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41391 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1978).leftCharge (GramAssembly.key 1978).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1978, Integer.Sparse.eval]

theorem keyMoment1979 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1979) =
      Integer.Sparse.eval keyMomentRow1979 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1979).leftCharge (GramAssembly.key 1979).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1821) := by
    have ha : gramCharges (GramAssembly.key 1979).leftCharge (GramAssembly.key 1979).rightCharge = raw41392 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41392Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41392 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1979).leftCharge (GramAssembly.key 1979).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1979, Integer.Sparse.eval]

theorem keyMoment1980 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1980) =
      Integer.Sparse.eval keyMomentRow1980 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1980).leftCharge (GramAssembly.key 1980).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2252) := by
    have ha : gramCharges (GramAssembly.key 1980).leftCharge (GramAssembly.key 1980).rightCharge = raw41393 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41393Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41393 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1980).leftCharge (GramAssembly.key 1980).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1980, Integer.Sparse.eval]

theorem keyMoment1981 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1981) =
      Integer.Sparse.eval keyMomentRow1981 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1981).leftCharge (GramAssembly.key 1981).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2104) := by
    have ha : gramCharges (GramAssembly.key 1981).leftCharge (GramAssembly.key 1981).rightCharge = raw41394 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41394Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41394 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1981).leftCharge (GramAssembly.key 1981).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1981, Integer.Sparse.eval]

theorem keyMoment1982 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1982) =
      Integer.Sparse.eval keyMomentRow1982 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1982).leftCharge (GramAssembly.key 1982).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2252) := by
    have ha : gramCharges (GramAssembly.key 1982).leftCharge (GramAssembly.key 1982).rightCharge = raw41395 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41395Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41395 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1982).leftCharge (GramAssembly.key 1982).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1982, Integer.Sparse.eval]

theorem keyMoment1983 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1983) =
      Integer.Sparse.eval keyMomentRow1983 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1983).leftCharge (GramAssembly.key 1983).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2806) := by
    have ha : gramCharges (GramAssembly.key 1983).leftCharge (GramAssembly.key 1983).rightCharge = raw41396 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41396Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41396 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1983).leftCharge (GramAssembly.key 1983).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1983, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1952 : keyMomentRows (1952 : Fin 2886) =
    keyMomentRow1952 := by decide +kernel

theorem keyMomentRowsAt1953 : keyMomentRows (1953 : Fin 2886) =
    keyMomentRow1953 := by decide +kernel

theorem keyMomentRowsAt1954 : keyMomentRows (1954 : Fin 2886) =
    keyMomentRow1954 := by decide +kernel

theorem keyMomentRowsAt1955 : keyMomentRows (1955 : Fin 2886) =
    keyMomentRow1955 := by decide +kernel

theorem keyMomentRowsAt1956 : keyMomentRows (1956 : Fin 2886) =
    keyMomentRow1956 := by decide +kernel

theorem keyMomentRowsAt1957 : keyMomentRows (1957 : Fin 2886) =
    keyMomentRow1957 := by decide +kernel

theorem keyMomentRowsAt1958 : keyMomentRows (1958 : Fin 2886) =
    keyMomentRow1958 := by decide +kernel

theorem keyMomentRowsAt1959 : keyMomentRows (1959 : Fin 2886) =
    keyMomentRow1959 := by decide +kernel

theorem keyMomentRowsAt1960 : keyMomentRows (1960 : Fin 2886) =
    keyMomentRow1960 := by decide +kernel

theorem keyMomentRowsAt1961 : keyMomentRows (1961 : Fin 2886) =
    keyMomentRow1961 := by decide +kernel

theorem keyMomentRowsAt1962 : keyMomentRows (1962 : Fin 2886) =
    keyMomentRow1962 := by decide +kernel

theorem keyMomentRowsAt1963 : keyMomentRows (1963 : Fin 2886) =
    keyMomentRow1963 := by decide +kernel

theorem keyMomentRowsAt1964 : keyMomentRows (1964 : Fin 2886) =
    keyMomentRow1964 := by decide +kernel

theorem keyMomentRowsAt1965 : keyMomentRows (1965 : Fin 2886) =
    keyMomentRow1965 := by decide +kernel

theorem keyMomentRowsAt1966 : keyMomentRows (1966 : Fin 2886) =
    keyMomentRow1966 := by decide +kernel

theorem keyMomentRowsAt1967 : keyMomentRows (1967 : Fin 2886) =
    keyMomentRow1967 := by decide +kernel

theorem keyMomentRowsAt1968 : keyMomentRows (1968 : Fin 2886) =
    keyMomentRow1968 := by decide +kernel

theorem keyMomentRowsAt1969 : keyMomentRows (1969 : Fin 2886) =
    keyMomentRow1969 := by decide +kernel

theorem keyMomentRowsAt1970 : keyMomentRows (1970 : Fin 2886) =
    keyMomentRow1970 := by decide +kernel

theorem keyMomentRowsAt1971 : keyMomentRows (1971 : Fin 2886) =
    keyMomentRow1971 := by decide +kernel

theorem keyMomentRowsAt1972 : keyMomentRows (1972 : Fin 2886) =
    keyMomentRow1972 := by decide +kernel

theorem keyMomentRowsAt1973 : keyMomentRows (1973 : Fin 2886) =
    keyMomentRow1973 := by decide +kernel

theorem keyMomentRowsAt1974 : keyMomentRows (1974 : Fin 2886) =
    keyMomentRow1974 := by decide +kernel

theorem keyMomentRowsAt1975 : keyMomentRows (1975 : Fin 2886) =
    keyMomentRow1975 := by decide +kernel

theorem keyMomentRowsAt1976 : keyMomentRows (1976 : Fin 2886) =
    keyMomentRow1976 := by decide +kernel

theorem keyMomentRowsAt1977 : keyMomentRows (1977 : Fin 2886) =
    keyMomentRow1977 := by decide +kernel

theorem keyMomentRowsAt1978 : keyMomentRows (1978 : Fin 2886) =
    keyMomentRow1978 := by decide +kernel

theorem keyMomentRowsAt1979 : keyMomentRows (1979 : Fin 2886) =
    keyMomentRow1979 := by decide +kernel

theorem keyMomentRowsAt1980 : keyMomentRows (1980 : Fin 2886) =
    keyMomentRow1980 := by decide +kernel

theorem keyMomentRowsAt1981 : keyMomentRows (1981 : Fin 2886) =
    keyMomentRow1981 := by decide +kernel

theorem keyMomentRowsAt1982 : keyMomentRows (1982 : Fin 2886) =
    keyMomentRow1982 := by decide +kernel

theorem keyMomentRowsAt1983 : keyMomentRows (1983 : Fin 2886) =
    keyMomentRow1983 := by decide +kernel

theorem keyMomentChunkSound61_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 61) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1952 ∨ k.val = 1953 ∨ k.val = 1954 ∨ k.val = 1955 ∨ k.val = 1956 ∨ k.val = 1957 ∨ k.val = 1958 ∨ k.val = 1959 ∨ k.val = 1960 ∨ k.val = 1961 ∨ k.val = 1962 ∨ k.val = 1963 ∨ k.val = 1964 ∨ k.val = 1965 ∨ k.val = 1966 ∨ k.val = 1967 ∨ k.val = 1968 ∨ k.val = 1969 ∨ k.val = 1970 ∨ k.val = 1971 ∨ k.val = 1972 ∨ k.val = 1973 ∨ k.val = 1974 ∨ k.val = 1975 ∨ k.val = 1976 ∨ k.val = 1977 ∨ k.val = 1978 ∨ k.val = 1979 ∨ k.val = 1980 ∨ k.val = 1981 ∨ k.val = 1982 ∨ k.val = 1983 := by omega
  rcases heq with h1952 | h1953 | h1954 | h1955 | h1956 | h1957 | h1958 | h1959 | h1960 | h1961 | h1962 | h1963 | h1964 | h1965 | h1966 | h1967 | h1968 | h1969 | h1970 | h1971 | h1972 | h1973 | h1974 | h1975 | h1976 | h1977 | h1978 | h1979 | h1980 | h1981 | h1982 | h1983
  · have he : k = (1952 : Fin 2886) := Fin.ext h1952
    subst k
    rw [keyMomentRowsAt1952]
    exact keyMoment1952 B hB
  · have he : k = (1953 : Fin 2886) := Fin.ext h1953
    subst k
    rw [keyMomentRowsAt1953]
    exact keyMoment1953 B hB
  · have he : k = (1954 : Fin 2886) := Fin.ext h1954
    subst k
    rw [keyMomentRowsAt1954]
    exact keyMoment1954 B hB
  · have he : k = (1955 : Fin 2886) := Fin.ext h1955
    subst k
    rw [keyMomentRowsAt1955]
    exact keyMoment1955 B hB
  · have he : k = (1956 : Fin 2886) := Fin.ext h1956
    subst k
    rw [keyMomentRowsAt1956]
    exact keyMoment1956 B hB
  · have he : k = (1957 : Fin 2886) := Fin.ext h1957
    subst k
    rw [keyMomentRowsAt1957]
    exact keyMoment1957 B hB
  · have he : k = (1958 : Fin 2886) := Fin.ext h1958
    subst k
    rw [keyMomentRowsAt1958]
    exact keyMoment1958 B hB
  · have he : k = (1959 : Fin 2886) := Fin.ext h1959
    subst k
    rw [keyMomentRowsAt1959]
    exact keyMoment1959 B hB
  · have he : k = (1960 : Fin 2886) := Fin.ext h1960
    subst k
    rw [keyMomentRowsAt1960]
    exact keyMoment1960 B hB
  · have he : k = (1961 : Fin 2886) := Fin.ext h1961
    subst k
    rw [keyMomentRowsAt1961]
    exact keyMoment1961 B hB
  · have he : k = (1962 : Fin 2886) := Fin.ext h1962
    subst k
    rw [keyMomentRowsAt1962]
    exact keyMoment1962 B hB
  · have he : k = (1963 : Fin 2886) := Fin.ext h1963
    subst k
    rw [keyMomentRowsAt1963]
    exact keyMoment1963 B hB
  · have he : k = (1964 : Fin 2886) := Fin.ext h1964
    subst k
    rw [keyMomentRowsAt1964]
    exact keyMoment1964 B hB
  · have he : k = (1965 : Fin 2886) := Fin.ext h1965
    subst k
    rw [keyMomentRowsAt1965]
    exact keyMoment1965 B hB
  · have he : k = (1966 : Fin 2886) := Fin.ext h1966
    subst k
    rw [keyMomentRowsAt1966]
    exact keyMoment1966 B hB
  · have he : k = (1967 : Fin 2886) := Fin.ext h1967
    subst k
    rw [keyMomentRowsAt1967]
    exact keyMoment1967 B hB
  · have he : k = (1968 : Fin 2886) := Fin.ext h1968
    subst k
    rw [keyMomentRowsAt1968]
    exact keyMoment1968 B hB
  · have he : k = (1969 : Fin 2886) := Fin.ext h1969
    subst k
    rw [keyMomentRowsAt1969]
    exact keyMoment1969 B hB
  · have he : k = (1970 : Fin 2886) := Fin.ext h1970
    subst k
    rw [keyMomentRowsAt1970]
    exact keyMoment1970 B hB
  · have he : k = (1971 : Fin 2886) := Fin.ext h1971
    subst k
    rw [keyMomentRowsAt1971]
    exact keyMoment1971 B hB
  · have he : k = (1972 : Fin 2886) := Fin.ext h1972
    subst k
    rw [keyMomentRowsAt1972]
    exact keyMoment1972 B hB
  · have he : k = (1973 : Fin 2886) := Fin.ext h1973
    subst k
    rw [keyMomentRowsAt1973]
    exact keyMoment1973 B hB
  · have he : k = (1974 : Fin 2886) := Fin.ext h1974
    subst k
    rw [keyMomentRowsAt1974]
    exact keyMoment1974 B hB
  · have he : k = (1975 : Fin 2886) := Fin.ext h1975
    subst k
    rw [keyMomentRowsAt1975]
    exact keyMoment1975 B hB
  · have he : k = (1976 : Fin 2886) := Fin.ext h1976
    subst k
    rw [keyMomentRowsAt1976]
    exact keyMoment1976 B hB
  · have he : k = (1977 : Fin 2886) := Fin.ext h1977
    subst k
    rw [keyMomentRowsAt1977]
    exact keyMoment1977 B hB
  · have he : k = (1978 : Fin 2886) := Fin.ext h1978
    subst k
    rw [keyMomentRowsAt1978]
    exact keyMoment1978 B hB
  · have he : k = (1979 : Fin 2886) := Fin.ext h1979
    subst k
    rw [keyMomentRowsAt1979]
    exact keyMoment1979 B hB
  · have he : k = (1980 : Fin 2886) := Fin.ext h1980
    subst k
    rw [keyMomentRowsAt1980]
    exact keyMoment1980 B hB
  · have he : k = (1981 : Fin 2886) := Fin.ext h1981
    subst k
    rw [keyMomentRowsAt1981]
    exact keyMoment1981 B hB
  · have he : k = (1982 : Fin 2886) := Fin.ext h1982
    subst k
    rw [keyMomentRowsAt1982]
    exact keyMoment1982 B hB
  · have he : k = (1983 : Fin 2886) := Fin.ext h1983
    subst k
    rw [keyMomentRowsAt1983]
    exact keyMoment1983 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound61_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound61_e_oai
