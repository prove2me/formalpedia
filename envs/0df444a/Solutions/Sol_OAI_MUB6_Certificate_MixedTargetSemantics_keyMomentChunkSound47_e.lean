-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound47_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:56:10.441742+00:00
-- url     : https://prove2.me/submissions/ea46b436-ec87-4a91-980d-ed82f55c7eea

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical319
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40922 raw40922Labels = mixedMoment B node2350 node2350Labels := by
  calc
    mixedMoment B raw40922 raw40922Labels = mixedMoment B raw40922step0 raw40922step0Labels := by
      have ha : raw40922step0 = (fun i j => raw40922 (permutation280 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40922step0 raw40922; decide +kernel
      have hl : raw40922step0Labels = raw40922Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40922 raw40922Labels permutation280 permutation6
    mixedMoment B raw40922step0 raw40922step0Labels = mixedMoment B raw40922step1 raw40922step1Labels := by
      have ha : raw40922step1 = -raw40922step0 := by apply Matrix.ext; change ∀ i j, raw40922step1 i j = -(raw40922step0 i j); unfold raw40922step1 raw40922step0; decide +kernel
      have hl : raw40922step1Labels = raw40922step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2350 node2350Labels := by rfl

theorem canonical40923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40923 raw40923Labels = mixedMoment B node2356 node2356Labels := by
  calc
    mixedMoment B raw40923 raw40923Labels = mixedMoment B raw40923step0 raw40923step0Labels := by
      have hz : ∀ j, raw40923 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40923step0 = (fun i j => raw40923 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40923step0 raw40923; decide +kernel
      have hl : raw40923step0Labels = raw40923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40923 raw40923Labels permutation434 hz
    mixedMoment B raw40923step0 raw40923step0Labels = mixedMoment B raw40923step1 raw40923step1Labels := by
      have ha : raw40923step1 = (fun i j => raw40923step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40923step1 raw40923step0; decide +kernel
      have hl : raw40923step1Labels = raw40923step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40923step0 raw40923step0Labels permutation61 permutation6
    mixedMoment B raw40923step1 raw40923step1Labels = mixedMoment B raw40923step2 raw40923step2Labels := by
      have ha : raw40923step2 = -raw40923step1 := by apply Matrix.ext; change ∀ i j, raw40923step2 i j = -(raw40923step1 i j); unfold raw40923step2 raw40923step1; decide +kernel
      have hl : raw40923step2Labels = raw40923step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2356 node2356Labels := by rfl

theorem canonical40924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40924 raw40924Labels = mixedMoment B node2352 node2352Labels := by
  calc
    mixedMoment B raw40924 raw40924Labels = mixedMoment B raw40924step0 raw40924step0Labels := by
      have hz : ∀ j, raw40924 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40924step0 = (fun i j => raw40924 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40924step0 raw40924; decide +kernel
      have hl : raw40924step0Labels = raw40924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40924 raw40924Labels permutation434 hz
    mixedMoment B raw40924step0 raw40924step0Labels = mixedMoment B raw40924step1 raw40924step1Labels := by
      have ha : raw40924step1 = (fun i j => raw40924step0 (permutation58 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40924step1 raw40924step0; decide +kernel
      have hl : raw40924step1Labels = raw40924step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40924step0 raw40924step0Labels permutation58 permutation6
    mixedMoment B raw40924step1 raw40924step1Labels = mixedMoment B raw40924step2 raw40924step2Labels := by
      have ha : raw40924step2 = -raw40924step1 := by apply Matrix.ext; change ∀ i j, raw40924step2 i j = -(raw40924step1 i j); unfold raw40924step2 raw40924step1; decide +kernel
      have hl : raw40924step2Labels = raw40924step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2352 node2352Labels := by rfl

theorem canonical40925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40925 raw40925Labels = mixedMoment B node2348 node2348Labels := by
  calc
    mixedMoment B raw40925 raw40925Labels = mixedMoment B raw40925step0 raw40925step0Labels := by
      have ha : raw40925step0 = (fun i j => raw40925 (permutation288 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40925step0 raw40925; decide +kernel
      have hl : raw40925step0Labels = raw40925Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40925 raw40925Labels permutation288 permutation6
    mixedMoment B raw40925step0 raw40925step0Labels = mixedMoment B raw40925step1 raw40925step1Labels := by
      have ha : raw40925step1 = -raw40925step0 := by apply Matrix.ext; change ∀ i j, raw40925step1 i j = -(raw40925step0 i j); unfold raw40925step1 raw40925step0; decide +kernel
      have hl : raw40925step1Labels = raw40925step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2348 node2348Labels := by rfl

theorem canonical40926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40926 raw40926Labels = mixedMoment B node2361 node2361Labels := by
  calc
    mixedMoment B raw40926 raw40926Labels = mixedMoment B raw40926step0 raw40926step0Labels := by
      have ha : raw40926step0 = (fun i j => raw40926 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40926step0 raw40926; decide +kernel
      have hl : raw40926step0Labels = raw40926Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40926 raw40926Labels permutation265 permutation6
    mixedMoment B raw40926step0 raw40926step0Labels = mixedMoment B raw40926step1 raw40926step1Labels := by
      have ha : raw40926step1 = -raw40926step0 := by apply Matrix.ext; change ∀ i j, raw40926step1 i j = -(raw40926step0 i j); unfold raw40926step1 raw40926step0; decide +kernel
      have hl : raw40926step1Labels = raw40926step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2361 node2361Labels := by rfl

theorem canonical40927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40927 raw40927Labels = mixedMoment B node2349 node2349Labels := by
  calc
    mixedMoment B raw40927 raw40927Labels = mixedMoment B raw40927step0 raw40927step0Labels := by
      have ha : raw40927step0 = (fun i j => raw40927 (permutation277 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40927step0 raw40927; decide +kernel
      have hl : raw40927step0Labels = raw40927Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40927 raw40927Labels permutation277 permutation6
    mixedMoment B raw40927step0 raw40927step0Labels = mixedMoment B raw40927step1 raw40927step1Labels := by
      have ha : raw40927step1 = -raw40927step0 := by apply Matrix.ext; change ∀ i j, raw40927step1 i j = -(raw40927step0 i j); unfold raw40927step1 raw40927step0; decide +kernel
      have hl : raw40927step1Labels = raw40927step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2349 node2349Labels := by rfl

theorem canonical40928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40928 raw40928Labels = mixedMoment B node2355 node2355Labels := by
  calc
    mixedMoment B raw40928 raw40928Labels = mixedMoment B raw40928step0 raw40928step0Labels := by
      have hz : ∀ j, raw40928 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40928step0 = (fun i j => raw40928 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40928step0 raw40928; decide +kernel
      have hl : raw40928step0Labels = raw40928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40928 raw40928Labels permutation434 hz
    mixedMoment B raw40928step0 raw40928step0Labels = mixedMoment B raw40928step1 raw40928step1Labels := by
      have ha : raw40928step1 = (fun i j => raw40928step0 (permutation60 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40928step1 raw40928step0; decide +kernel
      have hl : raw40928step1Labels = raw40928step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40928step0 raw40928step0Labels permutation60 permutation6
    mixedMoment B raw40928step1 raw40928step1Labels = mixedMoment B raw40928step2 raw40928step2Labels := by
      have ha : raw40928step2 = -raw40928step1 := by apply Matrix.ext; change ∀ i j, raw40928step2 i j = -(raw40928step1 i j); unfold raw40928step2 raw40928step1; decide +kernel
      have hl : raw40928step2Labels = raw40928step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2355 node2355Labels := by rfl

theorem canonical40929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40929 raw40929Labels = mixedMoment B node1119 node1119Labels := by
  calc
    mixedMoment B raw40929 raw40929Labels = mixedMoment B raw40929step0 raw40929step0Labels := by
      have hz : ∀ j, raw40929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40929step0 = (fun i j => raw40929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40929step0 raw40929; decide +kernel
      have hl : raw40929step0Labels = raw40929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40929 raw40929Labels permutation434 hz
    mixedMoment B raw40929step0 raw40929step0Labels = mixedMoment B raw40929step1 raw40929step1Labels := by
      have ha : raw40929step1 = (fun i j => raw40929step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40929step1 raw40929step0; decide +kernel
      have hl : raw40929step1Labels = raw40929step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40929step0 raw40929step0Labels permutation144 permutation6
    _ = mixedMoment B node1119 node1119Labels := by rfl

theorem canonical40930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40930 raw40930Labels = mixedMoment B node2347 node2347Labels := by
  calc
    mixedMoment B raw40930 raw40930Labels = mixedMoment B raw40930step0 raw40930step0Labels := by
      have ha : raw40930step0 = (fun i j => raw40930 (permutation287 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40930step0 raw40930; decide +kernel
      have hl : raw40930step0Labels = raw40930Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40930 raw40930Labels permutation287 permutation6
    mixedMoment B raw40930step0 raw40930step0Labels = mixedMoment B raw40930step1 raw40930step1Labels := by
      have ha : raw40930step1 = -raw40930step0 := by apply Matrix.ext; change ∀ i j, raw40930step1 i j = -(raw40930step0 i j); unfold raw40930step1 raw40930step0; decide +kernel
      have hl : raw40930step1Labels = raw40930step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2347 node2347Labels := by rfl

theorem canonical40931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40931 raw40931Labels = mixedMoment B node952 node952Labels := by
  calc
    mixedMoment B raw40931 raw40931Labels = mixedMoment B raw40931step0 raw40931step0Labels := by
      have hz : ∀ j, raw40931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40931step0 = (fun i j => raw40931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40931step0 raw40931; decide +kernel
      have hl : raw40931step0Labels = raw40931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40931 raw40931Labels permutation434 hz
    mixedMoment B raw40931step0 raw40931step0Labels = mixedMoment B raw40931step1 raw40931step1Labels := by
      have hz : ∀ j, raw40931step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40931step1 = (fun i j => raw40931step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40931step1 raw40931step0; decide +kernel
      have hl : raw40931step1Labels = raw40931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40931step0 raw40931step0Labels permutation80 hz
    mixedMoment B raw40931step1 raw40931step1Labels = mixedMoment B raw40931step2 raw40931step2Labels := by
      have ha : raw40931step2 = (fun i j => raw40931step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40931step2 raw40931step1; decide +kernel
      have hl : raw40931step2Labels = raw40931step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40931step1 raw40931step1Labels permutation24 permutation6
    _ = mixedMoment B node952 node952Labels := by rfl

theorem canonical40932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40932 raw40932Labels = mixedMoment B node588 node588Labels := by
  calc
    mixedMoment B raw40932 raw40932Labels = mixedMoment B raw40932step0 raw40932step0Labels := by
      have hz : ∀ j, raw40932 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40932step0 = (fun i j => raw40932 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40932step0 raw40932; decide +kernel
      have hl : raw40932step0Labels = raw40932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40932 raw40932Labels permutation434 hz
    mixedMoment B raw40932step0 raw40932step0Labels = mixedMoment B raw40932step1 raw40932step1Labels := by
      have hz : ∀ j, raw40932step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40932step1 = (fun i j => raw40932step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40932step1 raw40932step0; decide +kernel
      have hl : raw40932step1Labels = raw40932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40932step0 raw40932step0Labels permutation80 hz
    mixedMoment B raw40932step1 raw40932step1Labels = mixedMoment B raw40932step2 raw40932step2Labels := by
      have ha : raw40932step2 = (fun i j => raw40932step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40932step2 raw40932step1; decide +kernel
      have hl : raw40932step2Labels = raw40932step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40932step1 raw40932step1Labels permutation30 permutation6
    _ = mixedMoment B node588 node588Labels := by rfl

theorem canonical40933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40933 raw40933Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw40933 raw40933Labels = mixedMoment B raw40933step0 raw40933step0Labels := by
      have hz : ∀ j, raw40933 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40933step0 = (fun i j => raw40933 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40933step0 raw40933; decide +kernel
      have hl : raw40933step0Labels = raw40933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40933 raw40933Labels permutation520 hz
    mixedMoment B raw40933step0 raw40933step0Labels = mixedMoment B raw40933step1 raw40933step1Labels := by
      have hz : ∀ j, raw40933step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40933step1 = (fun i j => raw40933step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40933step1 raw40933step0; decide +kernel
      have hl : raw40933step1Labels = raw40933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40933step0 raw40933step0Labels permutation104 hz
    mixedMoment B raw40933step1 raw40933step1Labels = mixedMoment B raw40933step2 raw40933step2Labels := by
      have hz : ∀ j, raw40933step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40933step2 = (fun i j => raw40933step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40933step2 raw40933step1; decide +kernel
      have hl : raw40933step2Labels = raw40933step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40933step1 raw40933step1Labels permutation20 hz
    mixedMoment B raw40933step2 raw40933step2Labels = mixedMoment B raw40933step3 raw40933step3Labels := by
      have ha : raw40933step3 = (fun i j => raw40933step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40933step3 raw40933step2; decide +kernel
      have hl : raw40933step3Labels = raw40933step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40933step2 raw40933step2Labels permutation5 permutation6
    _ = mixedMoment B node2294 node2294Labels := by rfl

theorem canonical40934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40934 raw40934Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw40934 raw40934Labels = mixedMoment B raw40934step0 raw40934step0Labels := by
      have hz : ∀ j, raw40934 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40934step0 = (fun i j => raw40934 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40934step0 raw40934; decide +kernel
      have hl : raw40934step0Labels = raw40934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40934 raw40934Labels permutation434 hz
    mixedMoment B raw40934step0 raw40934step0Labels = mixedMoment B raw40934step1 raw40934step1Labels := by
      have hz : ∀ j, raw40934step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40934step1 = (fun i j => raw40934step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40934step1 raw40934step0; decide +kernel
      have hl : raw40934step1Labels = raw40934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40934step0 raw40934step0Labels permutation80 hz
    mixedMoment B raw40934step1 raw40934step1Labels = mixedMoment B raw40934step2 raw40934step2Labels := by
      have ha : raw40934step2 = (fun i j => raw40934step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40934step2 raw40934step1; decide +kernel
      have hl : raw40934step2Labels = raw40934step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40934step1 raw40934step1Labels permutation19 permutation6
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical40935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40935 raw40935Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw40935 raw40935Labels = mixedMoment B raw40935step0 raw40935step0Labels := by
      have hz : ∀ j, raw40935 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40935step0 = (fun i j => raw40935 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40935step0 raw40935; decide +kernel
      have hl : raw40935step0Labels = raw40935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40935 raw40935Labels permutation434 hz
    mixedMoment B raw40935step0 raw40935step0Labels = mixedMoment B raw40935step1 raw40935step1Labels := by
      have hz : ∀ j, raw40935step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40935step1 = (fun i j => raw40935step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40935step1 raw40935step0; decide +kernel
      have hl : raw40935step1Labels = raw40935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40935step0 raw40935step0Labels permutation80 hz
    mixedMoment B raw40935step1 raw40935step1Labels = mixedMoment B raw40935step2 raw40935step2Labels := by
      have ha : raw40935step2 = (fun i j => raw40935step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40935step2 raw40935step1; decide +kernel
      have hl : raw40935step2Labels = raw40935step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40935step1 raw40935step1Labels permutation18 permutation6
    _ = mixedMoment B node2115 node2115Labels := by rfl

theorem canonical40936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40936 raw40936Labels = mixedMoment B node1817 node1817Labels := by
  calc
    mixedMoment B raw40936 raw40936Labels = mixedMoment B raw40936step0 raw40936step0Labels := by
      have hz : ∀ j, raw40936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40936step0 = (fun i j => raw40936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40936step0 raw40936; decide +kernel
      have hl : raw40936step0Labels = raw40936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40936 raw40936Labels permutation434 hz
    mixedMoment B raw40936step0 raw40936step0Labels = mixedMoment B raw40936step1 raw40936step1Labels := by
      have hz : ∀ j, raw40936step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40936step1 = (fun i j => raw40936step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40936step1 raw40936step0; decide +kernel
      have hl : raw40936step1Labels = raw40936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40936step0 raw40936step0Labels permutation80 hz
    mixedMoment B raw40936step1 raw40936step1Labels = mixedMoment B raw40936step2 raw40936step2Labels := by
      have ha : raw40936step2 = (fun i j => raw40936step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40936step2 raw40936step1; decide +kernel
      have hl : raw40936step2Labels = raw40936step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40936step1 raw40936step1Labels permutation18 permutation6
    _ = mixedMoment B node1817 node1817Labels := by rfl

theorem canonical40937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40937 raw40937Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw40937 raw40937Labels = mixedMoment B raw40937step0 raw40937step0Labels := by
      have hz : ∀ j, raw40937 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40937step0 = (fun i j => raw40937 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40937step0 raw40937; decide +kernel
      have hl : raw40937step0Labels = raw40937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40937 raw40937Labels permutation434 hz
    mixedMoment B raw40937step0 raw40937step0Labels = mixedMoment B raw40937step1 raw40937step1Labels := by
      have hz : ∀ j, raw40937step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40937step1 = (fun i j => raw40937step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40937step1 raw40937step0; decide +kernel
      have hl : raw40937step1Labels = raw40937step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40937step0 raw40937step0Labels permutation80 hz
    mixedMoment B raw40937step1 raw40937step1Labels = mixedMoment B raw40937step2 raw40937step2Labels := by
      have ha : raw40937step2 = (fun i j => raw40937step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40937step2 raw40937step1; decide +kernel
      have hl : raw40937step2Labels = raw40937step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40937step1 raw40937step1Labels permutation17 permutation6
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical40938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40938 raw40938Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw40938 raw40938Labels = mixedMoment B raw40938step0 raw40938step0Labels := by
      have hz : ∀ j, raw40938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40938step0 = (fun i j => raw40938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40938step0 raw40938; decide +kernel
      have hl : raw40938step0Labels = raw40938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40938 raw40938Labels permutation346 hz
    mixedMoment B raw40938step0 raw40938step0Labels = mixedMoment B raw40938step1 raw40938step1Labels := by
      have ha : raw40938step1 = (fun i j => raw40938step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40938step1 raw40938step0; decide +kernel
      have hl : raw40938step1Labels = raw40938step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40938step0 raw40938step0Labels permutation77 permutation6
    _ = mixedMoment B node2110 node2110Labels := by rfl

theorem canonical40939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40939 raw40939Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw40939 raw40939Labels = mixedMoment B raw40939step0 raw40939step0Labels := by
      have hz : ∀ j, raw40939 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40939step0 = (fun i j => raw40939 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40939step0 raw40939; decide +kernel
      have hl : raw40939step0Labels = raw40939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40939 raw40939Labels permutation346 hz
    mixedMoment B raw40939step0 raw40939step0Labels = mixedMoment B raw40939step1 raw40939step1Labels := by
      have ha : raw40939step1 = (fun i j => raw40939step0 (permutation76 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40939step1 raw40939step0; decide +kernel
      have hl : raw40939step1Labels = raw40939step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40939step0 raw40939step0Labels permutation76 permutation6
    _ = mixedMoment B node1814 node1814Labels := by rfl

theorem canonical40940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40940 raw40940Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw40940 raw40940Labels = mixedMoment B raw40940step0 raw40940step0Labels := by
      have hz : ∀ j, raw40940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40940step0 = (fun i j => raw40940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40940step0 raw40940; decide +kernel
      have hl : raw40940step0Labels = raw40940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40940 raw40940Labels permutation346 hz
    mixedMoment B raw40940step0 raw40940step0Labels = mixedMoment B raw40940step1 raw40940step1Labels := by
      have ha : raw40940step1 = (fun i j => raw40940step0 (permutation71 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40940step1 raw40940step0; decide +kernel
      have hl : raw40940step1Labels = raw40940step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40940step0 raw40940step0Labels permutation71 permutation6
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical40941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40941 raw40941Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw40941 raw40941Labels = mixedMoment B raw40941step0 raw40941step0Labels := by
      have hz : ∀ j, raw40941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40941step0 = (fun i j => raw40941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40941step0 raw40941; decide +kernel
      have hl : raw40941step0Labels = raw40941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40941 raw40941Labels permutation346 hz
    mixedMoment B raw40941step0 raw40941step0Labels = mixedMoment B raw40941step1 raw40941step1Labels := by
      have ha : raw40941step1 = (fun i j => raw40941step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40941step1 raw40941step0; decide +kernel
      have hl : raw40941step1Labels = raw40941step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40941step0 raw40941step0Labels permutation73 permutation6
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical40942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40942 raw40942Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw40942 raw40942Labels = mixedMoment B raw40942step0 raw40942step0Labels := by
      have hz : ∀ j, raw40942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40942step0 = (fun i j => raw40942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40942step0 raw40942; decide +kernel
      have hl : raw40942step0Labels = raw40942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40942 raw40942Labels permutation346 hz
    mixedMoment B raw40942step0 raw40942step0Labels = mixedMoment B raw40942step1 raw40942step1Labels := by
      have ha : raw40942step1 = (fun i j => raw40942step0 (permutation72 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40942step1 raw40942step0; decide +kernel
      have hl : raw40942step1Labels = raw40942step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40942step0 raw40942step0Labels permutation72 permutation6
    _ = mixedMoment B node2028 node2028Labels := by rfl

theorem canonical40943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40943 raw40943Labels = mixedMoment B node1804 node1804Labels := by
  calc
    mixedMoment B raw40943 raw40943Labels = mixedMoment B raw40943step0 raw40943step0Labels := by
      have hz : ∀ j, raw40943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40943step0 = (fun i j => raw40943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40943step0 raw40943; decide +kernel
      have hl : raw40943step0Labels = raw40943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40943 raw40943Labels permutation346 hz
    mixedMoment B raw40943step0 raw40943step0Labels = mixedMoment B raw40943step1 raw40943step1Labels := by
      have ha : raw40943step1 = (fun i j => raw40943step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40943step1 raw40943step0; decide +kernel
      have hl : raw40943step1Labels = raw40943step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40943step0 raw40943step0Labels permutation83 permutation6
    mixedMoment B raw40943step1 raw40943step1Labels = mixedMoment B raw40943step2 raw40943step2Labels := by
      have ha : raw40943step2 = -raw40943step1 := by apply Matrix.ext; change ∀ i j, raw40943step2 i j = -(raw40943step1 i j); unfold raw40943step2 raw40943step1; decide +kernel
      have hl : raw40943step2Labels = raw40943step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1804 node1804Labels := by rfl

theorem canonical40944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40944 raw40944Labels = mixedMoment B node1811 node1811Labels := by
  calc
    mixedMoment B raw40944 raw40944Labels = mixedMoment B raw40944step0 raw40944step0Labels := by
      have ha : raw40944step0 = (fun i j => raw40944 (permutation340 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40944step0 raw40944; decide +kernel
      have hl : raw40944step0Labels = raw40944Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40944 raw40944Labels permutation340 permutation6
    _ = mixedMoment B node1811 node1811Labels := by rfl

theorem canonical40945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40945 raw40945Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw40945 raw40945Labels = mixedMoment B raw40945step0 raw40945step0Labels := by
      have ha : raw40945step0 = (fun i j => raw40945 (permutation332 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40945step0 raw40945; decide +kernel
      have hl : raw40945step0Labels = raw40945Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40945 raw40945Labels permutation332 permutation6
    _ = mixedMoment B node2023 node2023Labels := by rfl

theorem canonical40946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40946 raw40946Labels = mixedMoment B node1966 node1966Labels := by
  calc
    mixedMoment B raw40946 raw40946Labels = mixedMoment B raw40946step0 raw40946step0Labels := by
      have ha : raw40946step0 = (fun i j => raw40946 (permutation331 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40946step0 raw40946; decide +kernel
      have hl : raw40946step0Labels = raw40946Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40946 raw40946Labels permutation331 permutation6
    _ = mixedMoment B node1966 node1966Labels := by rfl

theorem canonical40947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40947 raw40947Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw40947 raw40947Labels = mixedMoment B raw40947step0 raw40947step0Labels := by
      have hz : ∀ j, raw40947 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40947step0 = (fun i j => raw40947 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40947step0 raw40947; decide +kernel
      have hl : raw40947step0Labels = raw40947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40947 raw40947Labels permutation520 hz
    mixedMoment B raw40947step0 raw40947step0Labels = mixedMoment B raw40947step1 raw40947step1Labels := by
      have hz : ∀ j, raw40947step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40947step1 = (fun i j => raw40947step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40947step1 raw40947step0; decide +kernel
      have hl : raw40947step1Labels = raw40947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40947step0 raw40947step0Labels permutation104 hz
    mixedMoment B raw40947step1 raw40947step1Labels = mixedMoment B raw40947step2 raw40947step2Labels := by
      have ha : raw40947step2 = (fun i j => raw40947step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40947step2 raw40947step1; decide +kernel
      have hl : raw40947step2Labels = raw40947step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40947step1 raw40947step1Labels permutation31 permutation3
    mixedMoment B raw40947step2 raw40947step2Labels = mixedMoment B raw40947step3 raw40947step3Labels := by
      have ha : raw40947step3 = -raw40947step2 := by apply Matrix.ext; change ∀ i j, raw40947step3 i j = -(raw40947step2 i j); unfold raw40947step3 raw40947step2; decide +kernel
      have hl : raw40947step3Labels = raw40947step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3626 node3626Labels := by rfl

theorem canonical40948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40948 raw40948Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw40948 raw40948Labels = mixedMoment B raw40948step0 raw40948step0Labels := by
      have hz : ∀ j, raw40948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40948step0 = (fun i j => raw40948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40948step0 raw40948; decide +kernel
      have hl : raw40948step0Labels = raw40948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40948 raw40948Labels permutation434 hz
    mixedMoment B raw40948step0 raw40948step0Labels = mixedMoment B raw40948step1 raw40948step1Labels := by
      have ha : raw40948step1 = (fun i j => raw40948step0 (permutation67 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40948step1 raw40948step0; decide +kernel
      have hl : raw40948step1Labels = raw40948step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40948step0 raw40948step0Labels permutation67 permutation6
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical40949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40949 raw40949Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw40949 raw40949Labels = mixedMoment B raw40949step0 raw40949step0Labels := by
      have hz : ∀ j, raw40949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40949step0 = (fun i j => raw40949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40949step0 raw40949; decide +kernel
      have hl : raw40949step0Labels = raw40949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40949 raw40949Labels permutation434 hz
    mixedMoment B raw40949step0 raw40949step0Labels = mixedMoment B raw40949step1 raw40949step1Labels := by
      have ha : raw40949step1 = (fun i j => raw40949step0 (permutation109 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40949step1 raw40949step0; decide +kernel
      have hl : raw40949step1Labels = raw40949step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40949step0 raw40949step0Labels permutation109 permutation6
    mixedMoment B raw40949step1 raw40949step1Labels = mixedMoment B raw40949step2 raw40949step2Labels := by
      have ha : raw40949step2 = -raw40949step1 := by apply Matrix.ext; change ∀ i j, raw40949step2 i j = -(raw40949step1 i j); unfold raw40949step2 raw40949step1; decide +kernel
      have hl : raw40949step2Labels = raw40949step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3732 node3732Labels := by rfl

theorem canonical40950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40950 raw40950Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw40950 raw40950Labels = mixedMoment B raw40950step0 raw40950step0Labels := by
      have hz : ∀ j, raw40950 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40950step0 = (fun i j => raw40950 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40950step0 raw40950; decide +kernel
      have hl : raw40950step0Labels = raw40950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40950 raw40950Labels permutation434 hz
    mixedMoment B raw40950step0 raw40950step0Labels = mixedMoment B raw40950step1 raw40950step1Labels := by
      have ha : raw40950step1 = (fun i j => raw40950step0 (permutation107 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40950step1 raw40950step0; decide +kernel
      have hl : raw40950step1Labels = raw40950step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40950step0 raw40950step0Labels permutation107 permutation6
    mixedMoment B raw40950step1 raw40950step1Labels = mixedMoment B raw40950step2 raw40950step2Labels := by
      have ha : raw40950step2 = -raw40950step1 := by apply Matrix.ext; change ∀ i j, raw40950step2 i j = -(raw40950step1 i j); unfold raw40950step2 raw40950step1; decide +kernel
      have hl : raw40950step2Labels = raw40950step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1814 node1814Labels := by rfl

theorem canonical40951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40951 raw40951Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw40951 raw40951Labels = mixedMoment B raw40951step0 raw40951step0Labels := by
      have hz : ∀ j, raw40951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40951step0 = (fun i j => raw40951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40951step0 raw40951; decide +kernel
      have hl : raw40951step0Labels = raw40951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40951 raw40951Labels permutation434 hz
    mixedMoment B raw40951step0 raw40951step0Labels = mixedMoment B raw40951step1 raw40951step1Labels := by
      have ha : raw40951step1 = (fun i j => raw40951step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40951step1 raw40951step0; decide +kernel
      have hl : raw40951step1Labels = raw40951step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40951step0 raw40951step0Labels permutation65 permutation6
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical40952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40952 raw40952Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw40952 raw40952Labels = mixedMoment B raw40952step0 raw40952step0Labels := by
      have ha : raw40952step0 = (fun i j => raw40952 (permutation304 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40952step0 raw40952; decide +kernel
      have hl : raw40952step0Labels = raw40952Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40952 raw40952Labels permutation304 permutation6
    _ = mixedMoment B node3789 node3789Labels := by rfl

theorem canonical40953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40953 raw40953Labels = mixedMoment B node3708 node3708Labels := by
  calc
    mixedMoment B raw40953 raw40953Labels = mixedMoment B raw40953step0 raw40953step0Labels := by
      have ha : raw40953step0 = (fun i j => raw40953 (permutation339 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40953step0 raw40953; decide +kernel
      have hl : raw40953step0Labels = raw40953Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40953 raw40953Labels permutation339 permutation6
    _ = mixedMoment B node3708 node3708Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1504 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1504) =
      Integer.Sparse.eval keyMomentRow1504 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1504).leftCharge (GramAssembly.key 1504).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2350) := by
    have ha : gramCharges (GramAssembly.key 1504).leftCharge (GramAssembly.key 1504).rightCharge = raw40922 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40922Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40922 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1504).leftCharge (GramAssembly.key 1504).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1504, Integer.Sparse.eval]

theorem keyMoment1505 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1505) =
      Integer.Sparse.eval keyMomentRow1505 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1505).leftCharge (GramAssembly.key 1505).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2356) := by
    have ha : gramCharges (GramAssembly.key 1505).leftCharge (GramAssembly.key 1505).rightCharge = raw40923 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40923Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40923 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1505).leftCharge (GramAssembly.key 1505).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1505, Integer.Sparse.eval]

theorem keyMoment1506 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1506) =
      Integer.Sparse.eval keyMomentRow1506 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1506).leftCharge (GramAssembly.key 1506).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2352) := by
    have ha : gramCharges (GramAssembly.key 1506).leftCharge (GramAssembly.key 1506).rightCharge = raw40924 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40924Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40924 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1506).leftCharge (GramAssembly.key 1506).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1506, Integer.Sparse.eval]

theorem keyMoment1507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1507) =
      Integer.Sparse.eval keyMomentRow1507 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1507).leftCharge (GramAssembly.key 1507).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2348) := by
    have ha : gramCharges (GramAssembly.key 1507).leftCharge (GramAssembly.key 1507).rightCharge = raw40925 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40925Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40925 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1507).leftCharge (GramAssembly.key 1507).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1507, Integer.Sparse.eval]

theorem keyMoment1508 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1508) =
      Integer.Sparse.eval keyMomentRow1508 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1508).leftCharge (GramAssembly.key 1508).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2361) := by
    have ha : gramCharges (GramAssembly.key 1508).leftCharge (GramAssembly.key 1508).rightCharge = raw40926 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40926Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40926 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1508).leftCharge (GramAssembly.key 1508).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1508, Integer.Sparse.eval]

theorem keyMoment1509 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1509) =
      Integer.Sparse.eval keyMomentRow1509 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1509).leftCharge (GramAssembly.key 1509).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2349) := by
    have ha : gramCharges (GramAssembly.key 1509).leftCharge (GramAssembly.key 1509).rightCharge = raw40927 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40927Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40927 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1509).leftCharge (GramAssembly.key 1509).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1509, Integer.Sparse.eval]

theorem keyMoment1510 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1510) =
      Integer.Sparse.eval keyMomentRow1510 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1510).leftCharge (GramAssembly.key 1510).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2355) := by
    have ha : gramCharges (GramAssembly.key 1510).leftCharge (GramAssembly.key 1510).rightCharge = raw40928 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40928Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40928 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1510).leftCharge (GramAssembly.key 1510).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1510, Integer.Sparse.eval]

theorem keyMoment1511 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1511) =
      Integer.Sparse.eval keyMomentRow1511 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1511).leftCharge (GramAssembly.key 1511).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1119) := by
    have ha : gramCharges (GramAssembly.key 1511).leftCharge (GramAssembly.key 1511).rightCharge = raw40929 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40929Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40929 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1511).leftCharge (GramAssembly.key 1511).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1511, Integer.Sparse.eval]

theorem keyMoment1512 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1512) =
      Integer.Sparse.eval keyMomentRow1512 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1512).leftCharge (GramAssembly.key 1512).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2347) := by
    have ha : gramCharges (GramAssembly.key 1512).leftCharge (GramAssembly.key 1512).rightCharge = raw40930 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40930Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40930 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1512).leftCharge (GramAssembly.key 1512).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1512, Integer.Sparse.eval]

theorem keyMoment1513 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1513) =
      Integer.Sparse.eval keyMomentRow1513 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1513).leftCharge (GramAssembly.key 1513).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 952) := by
    have ha : gramCharges (GramAssembly.key 1513).leftCharge (GramAssembly.key 1513).rightCharge = raw40931 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40931Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40931 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1513).leftCharge (GramAssembly.key 1513).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1513, Integer.Sparse.eval]

theorem keyMoment1514 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1514) =
      Integer.Sparse.eval keyMomentRow1514 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1514).leftCharge (GramAssembly.key 1514).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 588) := by
    have ha : gramCharges (GramAssembly.key 1514).leftCharge (GramAssembly.key 1514).rightCharge = raw40932 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40932Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40932 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1514).leftCharge (GramAssembly.key 1514).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1514, Integer.Sparse.eval]

theorem keyMoment1515 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1515) =
      Integer.Sparse.eval keyMomentRow1515 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1515).leftCharge (GramAssembly.key 1515).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2294) := by
    have ha : gramCharges (GramAssembly.key 1515).leftCharge (GramAssembly.key 1515).rightCharge = raw40933 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40933Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40933 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1515).leftCharge (GramAssembly.key 1515).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1515, Integer.Sparse.eval]

theorem keyMoment1516 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1516) =
      Integer.Sparse.eval keyMomentRow1516 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1516).leftCharge (GramAssembly.key 1516).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2279) := by
    have ha : gramCharges (GramAssembly.key 1516).leftCharge (GramAssembly.key 1516).rightCharge = raw40934 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40934Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40934 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1516).leftCharge (GramAssembly.key 1516).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1516, Integer.Sparse.eval]

theorem keyMoment1517 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1517) =
      Integer.Sparse.eval keyMomentRow1517 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1517).leftCharge (GramAssembly.key 1517).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2115) := by
    have ha : gramCharges (GramAssembly.key 1517).leftCharge (GramAssembly.key 1517).rightCharge = raw40935 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40935Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40935 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1517).leftCharge (GramAssembly.key 1517).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1517, Integer.Sparse.eval]

theorem keyMoment1518 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1518) =
      Integer.Sparse.eval keyMomentRow1518 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1518).leftCharge (GramAssembly.key 1518).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1817) := by
    have ha : gramCharges (GramAssembly.key 1518).leftCharge (GramAssembly.key 1518).rightCharge = raw40936 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40936Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40936 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1518).leftCharge (GramAssembly.key 1518).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1518, Integer.Sparse.eval]

theorem keyMoment1519 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1519) =
      Integer.Sparse.eval keyMomentRow1519 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1519).leftCharge (GramAssembly.key 1519).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2266) := by
    have ha : gramCharges (GramAssembly.key 1519).leftCharge (GramAssembly.key 1519).rightCharge = raw40937 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40937Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40937 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1519).leftCharge (GramAssembly.key 1519).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1519, Integer.Sparse.eval]

theorem keyMoment1520 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1520) =
      Integer.Sparse.eval keyMomentRow1520 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1520).leftCharge (GramAssembly.key 1520).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2110) := by
    have ha : gramCharges (GramAssembly.key 1520).leftCharge (GramAssembly.key 1520).rightCharge = raw40938 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40938Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40938 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1520).leftCharge (GramAssembly.key 1520).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1520, Integer.Sparse.eval]

theorem keyMoment1521 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1521) =
      Integer.Sparse.eval keyMomentRow1521 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1521).leftCharge (GramAssembly.key 1521).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1814) := by
    have ha : gramCharges (GramAssembly.key 1521).leftCharge (GramAssembly.key 1521).rightCharge = raw40939 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40939Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40939 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1521).leftCharge (GramAssembly.key 1521).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1521, Integer.Sparse.eval]

theorem keyMoment1522 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1522) =
      Integer.Sparse.eval keyMomentRow1522 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1522).leftCharge (GramAssembly.key 1522).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2058) := by
    have ha : gramCharges (GramAssembly.key 1522).leftCharge (GramAssembly.key 1522).rightCharge = raw40940 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40940Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40940 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1522).leftCharge (GramAssembly.key 1522).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1522, Integer.Sparse.eval]

theorem keyMoment1523 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1523) =
      Integer.Sparse.eval keyMomentRow1523 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1523).leftCharge (GramAssembly.key 1523).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2245) := by
    have ha : gramCharges (GramAssembly.key 1523).leftCharge (GramAssembly.key 1523).rightCharge = raw40941 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40941Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40941 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1523).leftCharge (GramAssembly.key 1523).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1523, Integer.Sparse.eval]

theorem keyMoment1524 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1524) =
      Integer.Sparse.eval keyMomentRow1524 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1524).leftCharge (GramAssembly.key 1524).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2028) := by
    have ha : gramCharges (GramAssembly.key 1524).leftCharge (GramAssembly.key 1524).rightCharge = raw40942 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40942Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40942 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1524).leftCharge (GramAssembly.key 1524).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1524, Integer.Sparse.eval]

theorem keyMoment1525 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1525) =
      Integer.Sparse.eval keyMomentRow1525 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1525).leftCharge (GramAssembly.key 1525).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1804) := by
    have ha : gramCharges (GramAssembly.key 1525).leftCharge (GramAssembly.key 1525).rightCharge = raw40943 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40943Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40943 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1525).leftCharge (GramAssembly.key 1525).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1525, Integer.Sparse.eval]

theorem keyMoment1526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1526) =
      Integer.Sparse.eval keyMomentRow1526 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1526).leftCharge (GramAssembly.key 1526).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1811) := by
    have ha : gramCharges (GramAssembly.key 1526).leftCharge (GramAssembly.key 1526).rightCharge = raw40944 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40944Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40944 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1526).leftCharge (GramAssembly.key 1526).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1526, Integer.Sparse.eval]

theorem keyMoment1527 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1527) =
      Integer.Sparse.eval keyMomentRow1527 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1527).leftCharge (GramAssembly.key 1527).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2023) := by
    have ha : gramCharges (GramAssembly.key 1527).leftCharge (GramAssembly.key 1527).rightCharge = raw40945 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40945Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40945 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1527).leftCharge (GramAssembly.key 1527).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1527, Integer.Sparse.eval]

theorem keyMoment1528 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1528) =
      Integer.Sparse.eval keyMomentRow1528 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1528).leftCharge (GramAssembly.key 1528).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1966) := by
    have ha : gramCharges (GramAssembly.key 1528).leftCharge (GramAssembly.key 1528).rightCharge = raw40946 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40946Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40946 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1528).leftCharge (GramAssembly.key 1528).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1528, Integer.Sparse.eval]

theorem keyMoment1529 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1529) =
      Integer.Sparse.eval keyMomentRow1529 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1529).leftCharge (GramAssembly.key 1529).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3626) := by
    have ha : gramCharges (GramAssembly.key 1529).leftCharge (GramAssembly.key 1529).rightCharge = raw40947 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40947Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40947 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1529).leftCharge (GramAssembly.key 1529).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1529, Integer.Sparse.eval]

theorem keyMoment1530 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1530) =
      Integer.Sparse.eval keyMomentRow1530 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1530).leftCharge (GramAssembly.key 1530).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3814) := by
    have ha : gramCharges (GramAssembly.key 1530).leftCharge (GramAssembly.key 1530).rightCharge = raw40948 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40948Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40948 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1530).leftCharge (GramAssembly.key 1530).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1530, Integer.Sparse.eval]

theorem keyMoment1531 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1531) =
      Integer.Sparse.eval keyMomentRow1531 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1531).leftCharge (GramAssembly.key 1531).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3732) := by
    have ha : gramCharges (GramAssembly.key 1531).leftCharge (GramAssembly.key 1531).rightCharge = raw40949 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40949Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40949 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1531).leftCharge (GramAssembly.key 1531).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1531, Integer.Sparse.eval]

theorem keyMoment1532 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1532) =
      Integer.Sparse.eval keyMomentRow1532 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1532).leftCharge (GramAssembly.key 1532).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1814) := by
    have ha : gramCharges (GramAssembly.key 1532).leftCharge (GramAssembly.key 1532).rightCharge = raw40950 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40950Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40950 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1532).leftCharge (GramAssembly.key 1532).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1532, Integer.Sparse.eval]

theorem keyMoment1533 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1533) =
      Integer.Sparse.eval keyMomentRow1533 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1533).leftCharge (GramAssembly.key 1533).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3809) := by
    have ha : gramCharges (GramAssembly.key 1533).leftCharge (GramAssembly.key 1533).rightCharge = raw40951 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40951Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40951 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1533).leftCharge (GramAssembly.key 1533).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1533, Integer.Sparse.eval]

theorem keyMoment1534 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1534) =
      Integer.Sparse.eval keyMomentRow1534 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1534).leftCharge (GramAssembly.key 1534).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3789) := by
    have ha : gramCharges (GramAssembly.key 1534).leftCharge (GramAssembly.key 1534).rightCharge = raw40952 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40952Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40952 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1534).leftCharge (GramAssembly.key 1534).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1534, Integer.Sparse.eval]

theorem keyMoment1535 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1535) =
      Integer.Sparse.eval keyMomentRow1535 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1535).leftCharge (GramAssembly.key 1535).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3708) := by
    have ha : gramCharges (GramAssembly.key 1535).leftCharge (GramAssembly.key 1535).rightCharge = raw40953 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40953Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40953 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1535).leftCharge (GramAssembly.key 1535).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1535, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1504 : keyMomentRows (1504 : Fin 2886) =
    keyMomentRow1504 := by decide +kernel

theorem keyMomentRowsAt1505 : keyMomentRows (1505 : Fin 2886) =
    keyMomentRow1505 := by decide +kernel

theorem keyMomentRowsAt1506 : keyMomentRows (1506 : Fin 2886) =
    keyMomentRow1506 := by decide +kernel

theorem keyMomentRowsAt1507 : keyMomentRows (1507 : Fin 2886) =
    keyMomentRow1507 := by decide +kernel

theorem keyMomentRowsAt1508 : keyMomentRows (1508 : Fin 2886) =
    keyMomentRow1508 := by decide +kernel

theorem keyMomentRowsAt1509 : keyMomentRows (1509 : Fin 2886) =
    keyMomentRow1509 := by decide +kernel

theorem keyMomentRowsAt1510 : keyMomentRows (1510 : Fin 2886) =
    keyMomentRow1510 := by decide +kernel

theorem keyMomentRowsAt1511 : keyMomentRows (1511 : Fin 2886) =
    keyMomentRow1511 := by decide +kernel

theorem keyMomentRowsAt1512 : keyMomentRows (1512 : Fin 2886) =
    keyMomentRow1512 := by decide +kernel

theorem keyMomentRowsAt1513 : keyMomentRows (1513 : Fin 2886) =
    keyMomentRow1513 := by decide +kernel

theorem keyMomentRowsAt1514 : keyMomentRows (1514 : Fin 2886) =
    keyMomentRow1514 := by decide +kernel

theorem keyMomentRowsAt1515 : keyMomentRows (1515 : Fin 2886) =
    keyMomentRow1515 := by decide +kernel

theorem keyMomentRowsAt1516 : keyMomentRows (1516 : Fin 2886) =
    keyMomentRow1516 := by decide +kernel

theorem keyMomentRowsAt1517 : keyMomentRows (1517 : Fin 2886) =
    keyMomentRow1517 := by decide +kernel

theorem keyMomentRowsAt1518 : keyMomentRows (1518 : Fin 2886) =
    keyMomentRow1518 := by decide +kernel

theorem keyMomentRowsAt1519 : keyMomentRows (1519 : Fin 2886) =
    keyMomentRow1519 := by decide +kernel

theorem keyMomentRowsAt1520 : keyMomentRows (1520 : Fin 2886) =
    keyMomentRow1520 := by decide +kernel

theorem keyMomentRowsAt1521 : keyMomentRows (1521 : Fin 2886) =
    keyMomentRow1521 := by decide +kernel

theorem keyMomentRowsAt1522 : keyMomentRows (1522 : Fin 2886) =
    keyMomentRow1522 := by decide +kernel

theorem keyMomentRowsAt1523 : keyMomentRows (1523 : Fin 2886) =
    keyMomentRow1523 := by decide +kernel

theorem keyMomentRowsAt1524 : keyMomentRows (1524 : Fin 2886) =
    keyMomentRow1524 := by decide +kernel

theorem keyMomentRowsAt1525 : keyMomentRows (1525 : Fin 2886) =
    keyMomentRow1525 := by decide +kernel

theorem keyMomentRowsAt1526 : keyMomentRows (1526 : Fin 2886) =
    keyMomentRow1526 := by decide +kernel

theorem keyMomentRowsAt1527 : keyMomentRows (1527 : Fin 2886) =
    keyMomentRow1527 := by decide +kernel

theorem keyMomentRowsAt1528 : keyMomentRows (1528 : Fin 2886) =
    keyMomentRow1528 := by decide +kernel

theorem keyMomentRowsAt1529 : keyMomentRows (1529 : Fin 2886) =
    keyMomentRow1529 := by decide +kernel

theorem keyMomentRowsAt1530 : keyMomentRows (1530 : Fin 2886) =
    keyMomentRow1530 := by decide +kernel

theorem keyMomentRowsAt1531 : keyMomentRows (1531 : Fin 2886) =
    keyMomentRow1531 := by decide +kernel

theorem keyMomentRowsAt1532 : keyMomentRows (1532 : Fin 2886) =
    keyMomentRow1532 := by decide +kernel

theorem keyMomentRowsAt1533 : keyMomentRows (1533 : Fin 2886) =
    keyMomentRow1533 := by decide +kernel

theorem keyMomentRowsAt1534 : keyMomentRows (1534 : Fin 2886) =
    keyMomentRow1534 := by decide +kernel

theorem keyMomentRowsAt1535 : keyMomentRows (1535 : Fin 2886) =
    keyMomentRow1535 := by decide +kernel

theorem keyMomentChunkSound47_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 47) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1504 ∨ k.val = 1505 ∨ k.val = 1506 ∨ k.val = 1507 ∨ k.val = 1508 ∨ k.val = 1509 ∨ k.val = 1510 ∨ k.val = 1511 ∨ k.val = 1512 ∨ k.val = 1513 ∨ k.val = 1514 ∨ k.val = 1515 ∨ k.val = 1516 ∨ k.val = 1517 ∨ k.val = 1518 ∨ k.val = 1519 ∨ k.val = 1520 ∨ k.val = 1521 ∨ k.val = 1522 ∨ k.val = 1523 ∨ k.val = 1524 ∨ k.val = 1525 ∨ k.val = 1526 ∨ k.val = 1527 ∨ k.val = 1528 ∨ k.val = 1529 ∨ k.val = 1530 ∨ k.val = 1531 ∨ k.val = 1532 ∨ k.val = 1533 ∨ k.val = 1534 ∨ k.val = 1535 := by omega
  rcases heq with h1504 | h1505 | h1506 | h1507 | h1508 | h1509 | h1510 | h1511 | h1512 | h1513 | h1514 | h1515 | h1516 | h1517 | h1518 | h1519 | h1520 | h1521 | h1522 | h1523 | h1524 | h1525 | h1526 | h1527 | h1528 | h1529 | h1530 | h1531 | h1532 | h1533 | h1534 | h1535
  · have he : k = (1504 : Fin 2886) := Fin.ext h1504
    subst k
    rw [keyMomentRowsAt1504]
    exact keyMoment1504 B hB
  · have he : k = (1505 : Fin 2886) := Fin.ext h1505
    subst k
    rw [keyMomentRowsAt1505]
    exact keyMoment1505 B hB
  · have he : k = (1506 : Fin 2886) := Fin.ext h1506
    subst k
    rw [keyMomentRowsAt1506]
    exact keyMoment1506 B hB
  · have he : k = (1507 : Fin 2886) := Fin.ext h1507
    subst k
    rw [keyMomentRowsAt1507]
    exact keyMoment1507 B hB
  · have he : k = (1508 : Fin 2886) := Fin.ext h1508
    subst k
    rw [keyMomentRowsAt1508]
    exact keyMoment1508 B hB
  · have he : k = (1509 : Fin 2886) := Fin.ext h1509
    subst k
    rw [keyMomentRowsAt1509]
    exact keyMoment1509 B hB
  · have he : k = (1510 : Fin 2886) := Fin.ext h1510
    subst k
    rw [keyMomentRowsAt1510]
    exact keyMoment1510 B hB
  · have he : k = (1511 : Fin 2886) := Fin.ext h1511
    subst k
    rw [keyMomentRowsAt1511]
    exact keyMoment1511 B hB
  · have he : k = (1512 : Fin 2886) := Fin.ext h1512
    subst k
    rw [keyMomentRowsAt1512]
    exact keyMoment1512 B hB
  · have he : k = (1513 : Fin 2886) := Fin.ext h1513
    subst k
    rw [keyMomentRowsAt1513]
    exact keyMoment1513 B hB
  · have he : k = (1514 : Fin 2886) := Fin.ext h1514
    subst k
    rw [keyMomentRowsAt1514]
    exact keyMoment1514 B hB
  · have he : k = (1515 : Fin 2886) := Fin.ext h1515
    subst k
    rw [keyMomentRowsAt1515]
    exact keyMoment1515 B hB
  · have he : k = (1516 : Fin 2886) := Fin.ext h1516
    subst k
    rw [keyMomentRowsAt1516]
    exact keyMoment1516 B hB
  · have he : k = (1517 : Fin 2886) := Fin.ext h1517
    subst k
    rw [keyMomentRowsAt1517]
    exact keyMoment1517 B hB
  · have he : k = (1518 : Fin 2886) := Fin.ext h1518
    subst k
    rw [keyMomentRowsAt1518]
    exact keyMoment1518 B hB
  · have he : k = (1519 : Fin 2886) := Fin.ext h1519
    subst k
    rw [keyMomentRowsAt1519]
    exact keyMoment1519 B hB
  · have he : k = (1520 : Fin 2886) := Fin.ext h1520
    subst k
    rw [keyMomentRowsAt1520]
    exact keyMoment1520 B hB
  · have he : k = (1521 : Fin 2886) := Fin.ext h1521
    subst k
    rw [keyMomentRowsAt1521]
    exact keyMoment1521 B hB
  · have he : k = (1522 : Fin 2886) := Fin.ext h1522
    subst k
    rw [keyMomentRowsAt1522]
    exact keyMoment1522 B hB
  · have he : k = (1523 : Fin 2886) := Fin.ext h1523
    subst k
    rw [keyMomentRowsAt1523]
    exact keyMoment1523 B hB
  · have he : k = (1524 : Fin 2886) := Fin.ext h1524
    subst k
    rw [keyMomentRowsAt1524]
    exact keyMoment1524 B hB
  · have he : k = (1525 : Fin 2886) := Fin.ext h1525
    subst k
    rw [keyMomentRowsAt1525]
    exact keyMoment1525 B hB
  · have he : k = (1526 : Fin 2886) := Fin.ext h1526
    subst k
    rw [keyMomentRowsAt1526]
    exact keyMoment1526 B hB
  · have he : k = (1527 : Fin 2886) := Fin.ext h1527
    subst k
    rw [keyMomentRowsAt1527]
    exact keyMoment1527 B hB
  · have he : k = (1528 : Fin 2886) := Fin.ext h1528
    subst k
    rw [keyMomentRowsAt1528]
    exact keyMoment1528 B hB
  · have he : k = (1529 : Fin 2886) := Fin.ext h1529
    subst k
    rw [keyMomentRowsAt1529]
    exact keyMoment1529 B hB
  · have he : k = (1530 : Fin 2886) := Fin.ext h1530
    subst k
    rw [keyMomentRowsAt1530]
    exact keyMoment1530 B hB
  · have he : k = (1531 : Fin 2886) := Fin.ext h1531
    subst k
    rw [keyMomentRowsAt1531]
    exact keyMoment1531 B hB
  · have he : k = (1532 : Fin 2886) := Fin.ext h1532
    subst k
    rw [keyMomentRowsAt1532]
    exact keyMoment1532 B hB
  · have he : k = (1533 : Fin 2886) := Fin.ext h1533
    subst k
    rw [keyMomentRowsAt1533]
    exact keyMoment1533 B hB
  · have he : k = (1534 : Fin 2886) := Fin.ext h1534
    subst k
    rw [keyMomentRowsAt1534]
    exact keyMoment1534 B hB
  · have he : k = (1535 : Fin 2886) := Fin.ext h1535
    subst k
    rw [keyMomentRowsAt1535]
    exact keyMoment1535 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound47_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound47_e_oai
