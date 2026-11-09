-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound53_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:58:06.774096+00:00
-- url     : https://prove2.me/submissions/8434392d-9aff-4e31-a454-68fe4a5489b8

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical321
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41109 raw41109Labels = mixedMoment B node2339 node2339Labels := by
  calc
    mixedMoment B raw41109 raw41109Labels = mixedMoment B raw41109step0 raw41109step0Labels := by
      have hz : ∀ j, raw41109 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41109step0 = (fun i j => raw41109 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41109step0 raw41109; decide +kernel
      have hl : raw41109step0Labels = raw41109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41109 raw41109Labels permutation265 hz
    mixedMoment B raw41109step0 raw41109step0Labels = mixedMoment B raw41109step1 raw41109step1Labels := by
      have ha : raw41109step1 = (fun i j => raw41109step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41109step1 raw41109step0; decide +kernel
      have hl : raw41109step1Labels = raw41109step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41109step0 raw41109step0Labels permutation125 permutation6
    _ = mixedMoment B node2339 node2339Labels := by rfl

theorem canonical41110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41110 raw41110Labels = mixedMoment B node1310 node1310Labels := by
  calc
    mixedMoment B raw41110 raw41110Labels = mixedMoment B raw41110step0 raw41110step0Labels := by
      have hz : ∀ j, raw41110 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41110step0 = (fun i j => raw41110 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41110step0 raw41110; decide +kernel
      have hl : raw41110step0Labels = raw41110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41110 raw41110Labels permutation520 hz
    mixedMoment B raw41110step0 raw41110step0Labels = mixedMoment B raw41110step1 raw41110step1Labels := by
      have hz : ∀ j, raw41110step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41110step1 = (fun i j => raw41110step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41110step1 raw41110step0; decide +kernel
      have hl : raw41110step1Labels = raw41110step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41110step0 raw41110step0Labels permutation104 hz
    mixedMoment B raw41110step1 raw41110step1Labels = mixedMoment B raw41110step2 raw41110step2Labels := by
      have hz : ∀ j, raw41110step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41110step2 = (fun i j => raw41110step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41110step2 raw41110step1; decide +kernel
      have hl : raw41110step2Labels = raw41110step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41110step1 raw41110step1Labels permutation20 hz
    mixedMoment B raw41110step2 raw41110step2Labels = mixedMoment B raw41110step3 raw41110step3Labels := by
      have ha : raw41110step3 = (fun i j => raw41110step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41110step3 raw41110step2; decide +kernel
      have hl : raw41110step3Labels = raw41110step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41110step2 raw41110step2Labels permutation3 permutation6
    mixedMoment B raw41110step3 raw41110step3Labels = mixedMoment B raw41110step4 raw41110step4Labels := by
      have ha : raw41110step4 = -raw41110step3 := by apply Matrix.ext; change ∀ i j, raw41110step4 i j = -(raw41110step3 i j); unfold raw41110step4 raw41110step3; decide +kernel
      have hl : raw41110step4Labels = raw41110step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1310 node1310Labels := by rfl

theorem canonical41111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41111 raw41111Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw41111 raw41111Labels = mixedMoment B raw41111step0 raw41111step0Labels := by
      have hz : ∀ j, raw41111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41111step0 = (fun i j => raw41111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41111step0 raw41111; decide +kernel
      have hl : raw41111step0Labels = raw41111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41111 raw41111Labels permutation434 hz
    mixedMoment B raw41111step0 raw41111step0Labels = mixedMoment B raw41111step1 raw41111step1Labels := by
      have hz : ∀ j, raw41111step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41111step1 = (fun i j => raw41111step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41111step1 raw41111step0; decide +kernel
      have hl : raw41111step1Labels = raw41111step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41111step0 raw41111step0Labels permutation80 hz
    mixedMoment B raw41111step1 raw41111step1Labels = mixedMoment B raw41111step2 raw41111step2Labels := by
      have ha : raw41111step2 = (fun i j => raw41111step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41111step2 raw41111step1; decide +kernel
      have hl : raw41111step2Labels = raw41111step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41111step1 raw41111step1Labels permutation11 permutation6
    mixedMoment B raw41111step2 raw41111step2Labels = mixedMoment B raw41111step3 raw41111step3Labels := by
      have ha : raw41111step3 = -raw41111step2 := by apply Matrix.ext; change ∀ i j, raw41111step3 i j = -(raw41111step2 i j); unfold raw41111step3 raw41111step2; decide +kernel
      have hl : raw41111step3Labels = raw41111step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1245 node1245Labels := by rfl

theorem canonical41112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41112 raw41112Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw41112 raw41112Labels = mixedMoment B raw41112step0 raw41112step0Labels := by
      have hz : ∀ j, raw41112 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41112step0 = (fun i j => raw41112 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41112step0 raw41112; decide +kernel
      have hl : raw41112step0Labels = raw41112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41112 raw41112Labels permutation520 hz
    mixedMoment B raw41112step0 raw41112step0Labels = mixedMoment B raw41112step1 raw41112step1Labels := by
      have hz : ∀ j, raw41112step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41112step1 = (fun i j => raw41112step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41112step1 raw41112step0; decide +kernel
      have hl : raw41112step1Labels = raw41112step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41112step0 raw41112step0Labels permutation104 hz
    mixedMoment B raw41112step1 raw41112step1Labels = mixedMoment B raw41112step2 raw41112step2Labels := by
      have ha : raw41112step2 = (fun i j => raw41112step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41112step2 raw41112step1; decide +kernel
      have hl : raw41112step2Labels = raw41112step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41112step1 raw41112step1Labels permutation10 permutation6
    mixedMoment B raw41112step2 raw41112step2Labels = mixedMoment B raw41112step3 raw41112step3Labels := by
      have ha : raw41112step3 = -raw41112step2 := by apply Matrix.ext; change ∀ i j, raw41112step3 i j = -(raw41112step2 i j); unfold raw41112step3 raw41112step2; decide +kernel
      have hl : raw41112step3Labels = raw41112step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1306 node1306Labels := by rfl

theorem canonical41113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41113 raw41113Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw41113 raw41113Labels = mixedMoment B raw41113step0 raw41113step0Labels := by
      have hz : ∀ j, raw41113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41113step0 = (fun i j => raw41113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41113step0 raw41113; decide +kernel
      have hl : raw41113step0Labels = raw41113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41113 raw41113Labels permutation434 hz
    mixedMoment B raw41113step0 raw41113step0Labels = mixedMoment B raw41113step1 raw41113step1Labels := by
      have ha : raw41113step1 = (fun i j => raw41113step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41113step1 raw41113step0; decide +kernel
      have hl : raw41113step1Labels = raw41113step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41113step0 raw41113step0Labels permutation55 permutation6
    mixedMoment B raw41113step1 raw41113step1Labels = mixedMoment B raw41113step2 raw41113step2Labels := by
      have ha : raw41113step2 = -raw41113step1 := by apply Matrix.ext; change ∀ i j, raw41113step2 i j = -(raw41113step1 i j); unfold raw41113step2 raw41113step1; decide +kernel
      have hl : raw41113step2Labels = raw41113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1291 node1291Labels := by rfl

theorem canonical41114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41114 raw41114Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw41114 raw41114Labels = mixedMoment B raw41114step0 raw41114step0Labels := by
      have hz : ∀ j, raw41114 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41114step0 = (fun i j => raw41114 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41114step0 raw41114; decide +kernel
      have hl : raw41114step0Labels = raw41114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41114 raw41114Labels permutation434 hz
    mixedMoment B raw41114step0 raw41114step0Labels = mixedMoment B raw41114step1 raw41114step1Labels := by
      have ha : raw41114step1 = (fun i j => raw41114step0 (permutation46 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41114step1 raw41114step0; decide +kernel
      have hl : raw41114step1Labels = raw41114step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41114step0 raw41114step0Labels permutation46 permutation6
    mixedMoment B raw41114step1 raw41114step1Labels = mixedMoment B raw41114step2 raw41114step2Labels := by
      have ha : raw41114step2 = -raw41114step1 := by apply Matrix.ext; change ∀ i j, raw41114step2 i j = -(raw41114step1 i j); unfold raw41114step2 raw41114step1; decide +kernel
      have hl : raw41114step2Labels = raw41114step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1241 node1241Labels := by rfl

theorem canonical41115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41115 raw41115Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw41115 raw41115Labels = mixedMoment B raw41115step0 raw41115step0Labels := by
      have ha : raw41115step0 = (fun i j => raw41115 (permutation259 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41115step0 raw41115; decide +kernel
      have hl : raw41115step0Labels = raw41115Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41115 raw41115Labels permutation259 permutation6
    mixedMoment B raw41115step0 raw41115step0Labels = mixedMoment B raw41115step1 raw41115step1Labels := by
      have ha : raw41115step1 = -raw41115step0 := by apply Matrix.ext; change ∀ i j, raw41115step1 i j = -(raw41115step0 i j); unfold raw41115step1 raw41115step0; decide +kernel
      have hl : raw41115step1Labels = raw41115step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1233 node1233Labels := by rfl

theorem canonical41116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41116 raw41116Labels = mixedMoment B node1295 node1295Labels := by
  calc
    mixedMoment B raw41116 raw41116Labels = mixedMoment B raw41116step0 raw41116step0Labels := by
      have hz : ∀ j, raw41116 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41116step0 = (fun i j => raw41116 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41116step0 raw41116; decide +kernel
      have hl : raw41116step0Labels = raw41116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41116 raw41116Labels permutation434 hz
    mixedMoment B raw41116step0 raw41116step0Labels = mixedMoment B raw41116step1 raw41116step1Labels := by
      have hz : ∀ j, raw41116step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41116step1 = (fun i j => raw41116step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41116step1 raw41116step0; decide +kernel
      have hl : raw41116step1Labels = raw41116step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41116step0 raw41116step0Labels permutation80 hz
    mixedMoment B raw41116step1 raw41116step1Labels = mixedMoment B raw41116step2 raw41116step2Labels := by
      have ha : raw41116step2 = (fun i j => raw41116step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41116step2 raw41116step1; decide +kernel
      have hl : raw41116step2Labels = raw41116step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41116step1 raw41116step1Labels permutation12 permutation6
    mixedMoment B raw41116step2 raw41116step2Labels = mixedMoment B raw41116step3 raw41116step3Labels := by
      have ha : raw41116step3 = -raw41116step2 := by apply Matrix.ext; change ∀ i j, raw41116step3 i j = -(raw41116step2 i j); unfold raw41116step3 raw41116step2; decide +kernel
      have hl : raw41116step3Labels = raw41116step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1295 node1295Labels := by rfl

theorem canonical41117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41117 raw41117Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw41117 raw41117Labels = mixedMoment B raw41117step0 raw41117step0Labels := by
      have hz : ∀ j, raw41117 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41117step0 = (fun i j => raw41117 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41117step0 raw41117; decide +kernel
      have hl : raw41117step0Labels = raw41117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41117 raw41117Labels permutation434 hz
    mixedMoment B raw41117step0 raw41117step0Labels = mixedMoment B raw41117step1 raw41117step1Labels := by
      have hz : ∀ j, raw41117step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41117step1 = (fun i j => raw41117step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41117step1 raw41117step0; decide +kernel
      have hl : raw41117step1Labels = raw41117step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41117step0 raw41117step0Labels permutation80 hz
    mixedMoment B raw41117step1 raw41117step1Labels = mixedMoment B raw41117step2 raw41117step2Labels := by
      have ha : raw41117step2 = (fun i j => raw41117step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41117step2 raw41117step1; decide +kernel
      have hl : raw41117step2Labels = raw41117step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41117step1 raw41117step1Labels permutation10 permutation6
    mixedMoment B raw41117step2 raw41117step2Labels = mixedMoment B raw41117step3 raw41117step3Labels := by
      have ha : raw41117step3 = -raw41117step2 := by apply Matrix.ext; change ∀ i j, raw41117step3 i j = -(raw41117step2 i j); unfold raw41117step3 raw41117step2; decide +kernel
      have hl : raw41117step3Labels = raw41117step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1243 node1243Labels := by rfl

theorem canonical41118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41118 raw41118Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw41118 raw41118Labels = mixedMoment B raw41118step0 raw41118step0Labels := by
      have hz : ∀ j, raw41118 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41118step0 = (fun i j => raw41118 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41118step0 raw41118; decide +kernel
      have hl : raw41118step0Labels = raw41118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41118 raw41118Labels permutation346 hz
    mixedMoment B raw41118step0 raw41118step0Labels = mixedMoment B raw41118step1 raw41118step1Labels := by
      have ha : raw41118step1 = (fun i j => raw41118step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41118step1 raw41118step0; decide +kernel
      have hl : raw41118step1Labels = raw41118step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41118step0 raw41118step0Labels permutation54 permutation6
    mixedMoment B raw41118step1 raw41118step1Labels = mixedMoment B raw41118step2 raw41118step2Labels := by
      have ha : raw41118step2 = -raw41118step1 := by apply Matrix.ext; change ∀ i j, raw41118step2 i j = -(raw41118step1 i j); unfold raw41118step2 raw41118step1; decide +kernel
      have hl : raw41118step2Labels = raw41118step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1237 node1237Labels := by rfl

theorem canonical41119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41119 raw41119Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw41119 raw41119Labels = mixedMoment B raw41119step0 raw41119step0Labels := by
      have hz : ∀ j, raw41119 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41119step0 = (fun i j => raw41119 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41119step0 raw41119; decide +kernel
      have hl : raw41119step0Labels = raw41119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41119 raw41119Labels permutation520 hz
    mixedMoment B raw41119step0 raw41119step0Labels = mixedMoment B raw41119step1 raw41119step1Labels := by
      have hz : ∀ j, raw41119step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41119step1 = (fun i j => raw41119step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41119step1 raw41119step0; decide +kernel
      have hl : raw41119step1Labels = raw41119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41119step0 raw41119step0Labels permutation104 hz
    mixedMoment B raw41119step1 raw41119step1Labels = mixedMoment B raw41119step2 raw41119step2Labels := by
      have ha : raw41119step2 = (fun i j => raw41119step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41119step2 raw41119step1; decide +kernel
      have hl : raw41119step2Labels = raw41119step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41119step1 raw41119step1Labels permutation9 permutation6
    mixedMoment B raw41119step2 raw41119step2Labels = mixedMoment B raw41119step3 raw41119step3Labels := by
      have ha : raw41119step3 = -raw41119step2 := by apply Matrix.ext; change ∀ i j, raw41119step3 i j = -(raw41119step2 i j); unfold raw41119step3 raw41119step2; decide +kernel
      have hl : raw41119step3Labels = raw41119step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1273 node1273Labels := by rfl

theorem canonical41120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41120 raw41120Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw41120 raw41120Labels = mixedMoment B raw41120step0 raw41120step0Labels := by
      have hz : ∀ j, raw41120 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41120step0 = (fun i j => raw41120 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41120step0 raw41120; decide +kernel
      have hl : raw41120step0Labels = raw41120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41120 raw41120Labels permutation434 hz
    mixedMoment B raw41120step0 raw41120step0Labels = mixedMoment B raw41120step1 raw41120step1Labels := by
      have ha : raw41120step1 = (fun i j => raw41120step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41120step1 raw41120step0; decide +kernel
      have hl : raw41120step1Labels = raw41120step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41120step0 raw41120step0Labels permutation37 permutation6
    mixedMoment B raw41120step1 raw41120step1Labels = mixedMoment B raw41120step2 raw41120step2Labels := by
      have ha : raw41120step2 = -raw41120step1 := by apply Matrix.ext; change ∀ i j, raw41120step2 i j = -(raw41120step1 i j); unfold raw41120step2 raw41120step1; decide +kernel
      have hl : raw41120step2Labels = raw41120step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1261 node1261Labels := by rfl

theorem canonical41121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41121 raw41121Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw41121 raw41121Labels = mixedMoment B raw41121step0 raw41121step0Labels := by
      have hz : ∀ j, raw41121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41121step0 = (fun i j => raw41121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41121step0 raw41121; decide +kernel
      have hl : raw41121step0Labels = raw41121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41121 raw41121Labels permutation434 hz
    mixedMoment B raw41121step0 raw41121step0Labels = mixedMoment B raw41121step1 raw41121step1Labels := by
      have ha : raw41121step1 = (fun i j => raw41121step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41121step1 raw41121step0; decide +kernel
      have hl : raw41121step1Labels = raw41121step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41121step0 raw41121step0Labels permutation45 permutation6
    mixedMoment B raw41121step1 raw41121step1Labels = mixedMoment B raw41121step2 raw41121step2Labels := by
      have ha : raw41121step2 = -raw41121step1 := by apply Matrix.ext; change ∀ i j, raw41121step2 i j = -(raw41121step1 i j); unfold raw41121step2 raw41121step1; decide +kernel
      have hl : raw41121step2Labels = raw41121step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1219 node1219Labels := by rfl

theorem canonical41122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41122 raw41122Labels = mixedMoment B node1212 node1212Labels := by
  calc
    mixedMoment B raw41122 raw41122Labels = mixedMoment B raw41122step0 raw41122step0Labels := by
      have ha : raw41122step0 = (fun i j => raw41122 (permutation249 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41122step0 raw41122; decide +kernel
      have hl : raw41122step0Labels = raw41122Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41122 raw41122Labels permutation249 permutation6
    mixedMoment B raw41122step0 raw41122step0Labels = mixedMoment B raw41122step1 raw41122step1Labels := by
      have ha : raw41122step1 = -raw41122step0 := by apply Matrix.ext; change ∀ i j, raw41122step1 i j = -(raw41122step0 i j); unfold raw41122step1 raw41122step0; decide +kernel
      have hl : raw41122step1Labels = raw41122step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1212 node1212Labels := by rfl

theorem canonical41123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41123 raw41123Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw41123 raw41123Labels = mixedMoment B raw41123step0 raw41123step0Labels := by
      have hz : ∀ j, raw41123 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41123step0 = (fun i j => raw41123 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41123step0 raw41123; decide +kernel
      have hl : raw41123step0Labels = raw41123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41123 raw41123Labels permutation520 hz
    mixedMoment B raw41123step0 raw41123step0Labels = mixedMoment B raw41123step1 raw41123step1Labels := by
      have ha : raw41123step1 = (fun i j => raw41123step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41123step1 raw41123step0; decide +kernel
      have hl : raw41123step1Labels = raw41123step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41123step0 raw41123step0Labels permutation32 permutation6
    mixedMoment B raw41123step1 raw41123step1Labels = mixedMoment B raw41123step2 raw41123step2Labels := by
      have ha : raw41123step2 = -raw41123step1 := by apply Matrix.ext; change ∀ i j, raw41123step2 i j = -(raw41123step1 i j); unfold raw41123step2 raw41123step1; decide +kernel
      have hl : raw41123step2Labels = raw41123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1270 node1270Labels := by rfl

theorem canonical41124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41124 raw41124Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw41124 raw41124Labels = mixedMoment B raw41124step0 raw41124step0Labels := by
      have hz : ∀ j, raw41124 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41124step0 = (fun i j => raw41124 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41124step0 raw41124; decide +kernel
      have hl : raw41124step0Labels = raw41124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41124 raw41124Labels permutation434 hz
    mixedMoment B raw41124step0 raw41124step0Labels = mixedMoment B raw41124step1 raw41124step1Labels := by
      have ha : raw41124step1 = (fun i j => raw41124step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41124step1 raw41124step0; decide +kernel
      have hl : raw41124step1Labels = raw41124step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41124step0 raw41124step0Labels permutation44 permutation6
    mixedMoment B raw41124step1 raw41124step1Labels = mixedMoment B raw41124step2 raw41124step2Labels := by
      have ha : raw41124step2 = -raw41124step1 := by apply Matrix.ext; change ∀ i j, raw41124step2 i j = -(raw41124step1 i j); unfold raw41124step2 raw41124step1; decide +kernel
      have hl : raw41124step2Labels = raw41124step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1217 node1217Labels := by rfl

theorem canonical41125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41125 raw41125Labels = mixedMoment B node1264 node1264Labels := by
  calc
    mixedMoment B raw41125 raw41125Labels = mixedMoment B raw41125step0 raw41125step0Labels := by
      have hz : ∀ j, raw41125 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41125step0 = (fun i j => raw41125 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41125step0 raw41125; decide +kernel
      have hl : raw41125step0Labels = raw41125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41125 raw41125Labels permutation434 hz
    mixedMoment B raw41125step0 raw41125step0Labels = mixedMoment B raw41125step1 raw41125step1Labels := by
      have hz : ∀ j, raw41125step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41125step1 = (fun i j => raw41125step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41125step1 raw41125step0; decide +kernel
      have hl : raw41125step1Labels = raw41125step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41125step0 raw41125step0Labels permutation80 hz
    mixedMoment B raw41125step1 raw41125step1Labels = mixedMoment B raw41125step2 raw41125step2Labels := by
      have ha : raw41125step2 = (fun i j => raw41125step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41125step2 raw41125step1; decide +kernel
      have hl : raw41125step2Labels = raw41125step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41125step1 raw41125step1Labels permutation9 permutation6
    mixedMoment B raw41125step2 raw41125step2Labels = mixedMoment B raw41125step3 raw41125step3Labels := by
      have ha : raw41125step3 = -raw41125step2 := by apply Matrix.ext; change ∀ i j, raw41125step3 i j = -(raw41125step2 i j); unfold raw41125step3 raw41125step2; decide +kernel
      have hl : raw41125step3Labels = raw41125step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1264 node1264Labels := by rfl

theorem canonical41126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41126 raw41126Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw41126 raw41126Labels = mixedMoment B raw41126step0 raw41126step0Labels := by
      have hz : ∀ j, raw41126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41126step0 = (fun i j => raw41126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41126step0 raw41126; decide +kernel
      have hl : raw41126step0Labels = raw41126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41126 raw41126Labels permutation434 hz
    mixedMoment B raw41126step0 raw41126step0Labels = mixedMoment B raw41126step1 raw41126step1Labels := by
      have hz : ∀ j, raw41126step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41126step1 = (fun i j => raw41126step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41126step1 raw41126step0; decide +kernel
      have hl : raw41126step1Labels = raw41126step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41126step0 raw41126step0Labels permutation80 hz
    mixedMoment B raw41126step1 raw41126step1Labels = mixedMoment B raw41126step2 raw41126step2Labels := by
      have ha : raw41126step2 = (fun i j => raw41126step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41126step2 raw41126step1; decide +kernel
      have hl : raw41126step2Labels = raw41126step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41126step1 raw41126step1Labels permutation29 permutation6
    _ = mixedMoment B node1221 node1221Labels := by rfl

theorem canonical41127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41127 raw41127Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw41127 raw41127Labels = mixedMoment B raw41127step0 raw41127step0Labels := by
      have hz : ∀ j, raw41127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41127step0 = (fun i j => raw41127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41127step0 raw41127; decide +kernel
      have hl : raw41127step0Labels = raw41127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41127 raw41127Labels permutation346 hz
    mixedMoment B raw41127step0 raw41127step0Labels = mixedMoment B raw41127step1 raw41127step1Labels := by
      have ha : raw41127step1 = (fun i j => raw41127step0 (permutation51 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41127step1 raw41127step0; decide +kernel
      have hl : raw41127step1Labels = raw41127step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41127step0 raw41127step0Labels permutation51 permutation6
    mixedMoment B raw41127step1 raw41127step1Labels = mixedMoment B raw41127step2 raw41127step2Labels := by
      have ha : raw41127step2 = -raw41127step1 := by apply Matrix.ext; change ∀ i j, raw41127step2 i j = -(raw41127step1 i j); unfold raw41127step2 raw41127step1; decide +kernel
      have hl : raw41127step2Labels = raw41127step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1215 node1215Labels := by rfl

theorem canonical41128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41128 raw41128Labels = mixedMoment B node1174 node1174Labels := by
  calc
    mixedMoment B raw41128 raw41128Labels = mixedMoment B raw41128step0 raw41128step0Labels := by
      have hz : ∀ j, raw41128 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41128step0 = (fun i j => raw41128 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41128step0 raw41128; decide +kernel
      have hl : raw41128step0Labels = raw41128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41128 raw41128Labels permutation520 hz
    mixedMoment B raw41128step0 raw41128step0Labels = mixedMoment B raw41128step1 raw41128step1Labels := by
      have hz : ∀ j, raw41128step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41128step1 = (fun i j => raw41128step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41128step1 raw41128step0; decide +kernel
      have hl : raw41128step1Labels = raw41128step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41128step0 raw41128step0Labels permutation104 hz
    mixedMoment B raw41128step1 raw41128step1Labels = mixedMoment B raw41128step2 raw41128step2Labels := by
      have ha : raw41128step2 = (fun i j => raw41128step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41128step2 raw41128step1; decide +kernel
      have hl : raw41128step2Labels = raw41128step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41128step1 raw41128step1Labels permutation9 permutation6
    mixedMoment B raw41128step2 raw41128step2Labels = mixedMoment B raw41128step3 raw41128step3Labels := by
      have ha : raw41128step3 = -raw41128step2 := by apply Matrix.ext; change ∀ i j, raw41128step3 i j = -(raw41128step2 i j); unfold raw41128step3 raw41128step2; decide +kernel
      have hl : raw41128step3Labels = raw41128step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1174 node1174Labels := by rfl

theorem canonical41129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41129 raw41129Labels = mixedMoment B node1153 node1153Labels := by
  calc
    mixedMoment B raw41129 raw41129Labels = mixedMoment B raw41129step0 raw41129step0Labels := by
      have hz : ∀ j, raw41129 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41129step0 = (fun i j => raw41129 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41129step0 raw41129; decide +kernel
      have hl : raw41129step0Labels = raw41129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41129 raw41129Labels permutation434 hz
    mixedMoment B raw41129step0 raw41129step0Labels = mixedMoment B raw41129step1 raw41129step1Labels := by
      have ha : raw41129step1 = (fun i j => raw41129step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41129step1 raw41129step0; decide +kernel
      have hl : raw41129step1Labels = raw41129step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41129step0 raw41129step0Labels permutation35 permutation6
    mixedMoment B raw41129step1 raw41129step1Labels = mixedMoment B raw41129step2 raw41129step2Labels := by
      have ha : raw41129step2 = -raw41129step1 := by apply Matrix.ext; change ∀ i j, raw41129step2 i j = -(raw41129step1 i j); unfold raw41129step2 raw41129step1; decide +kernel
      have hl : raw41129step2Labels = raw41129step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1153 node1153Labels := by rfl

theorem canonical41130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41130 raw41130Labels = mixedMoment B node1171 node1171Labels := by
  calc
    mixedMoment B raw41130 raw41130Labels = mixedMoment B raw41130step0 raw41130step0Labels := by
      have hz : ∀ j, raw41130 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41130step0 = (fun i j => raw41130 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41130step0 raw41130; decide +kernel
      have hl : raw41130step0Labels = raw41130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41130 raw41130Labels permutation520 hz
    mixedMoment B raw41130step0 raw41130step0Labels = mixedMoment B raw41130step1 raw41130step1Labels := by
      have ha : raw41130step1 = (fun i j => raw41130step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41130step1 raw41130step0; decide +kernel
      have hl : raw41130step1Labels = raw41130step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41130step0 raw41130step0Labels permutation35 permutation6
    mixedMoment B raw41130step1 raw41130step1Labels = mixedMoment B raw41130step2 raw41130step2Labels := by
      have ha : raw41130step2 = -raw41130step1 := by apply Matrix.ext; change ∀ i j, raw41130step2 i j = -(raw41130step1 i j); unfold raw41130step2 raw41130step1; decide +kernel
      have hl : raw41130step2Labels = raw41130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1171 node1171Labels := by rfl

theorem canonical41131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41131 raw41131Labels = mixedMoment B node1156 node1156Labels := by
  calc
    mixedMoment B raw41131 raw41131Labels = mixedMoment B raw41131step0 raw41131step0Labels := by
      have ha : raw41131step0 = (fun i j => raw41131 (permutation175 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41131step0 raw41131; decide +kernel
      have hl : raw41131step0Labels = raw41131Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41131 raw41131Labels permutation175 permutation6
    mixedMoment B raw41131step0 raw41131step0Labels = mixedMoment B raw41131step1 raw41131step1Labels := by
      have ha : raw41131step1 = -raw41131step0 := by apply Matrix.ext; change ∀ i j, raw41131step1 i j = -(raw41131step0 i j); unfold raw41131step1 raw41131step0; decide +kernel
      have hl : raw41131step1Labels = raw41131step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1156 node1156Labels := by rfl

theorem canonical41132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41132 raw41132Labels = mixedMoment B node1151 node1151Labels := by
  calc
    mixedMoment B raw41132 raw41132Labels = mixedMoment B raw41132step0 raw41132step0Labels := by
      have ha : raw41132step0 = (fun i j => raw41132 (permutation167 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41132step0 raw41132; decide +kernel
      have hl : raw41132step0Labels = raw41132Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41132 raw41132Labels permutation167 permutation6
    mixedMoment B raw41132step0 raw41132step0Labels = mixedMoment B raw41132step1 raw41132step1Labels := by
      have ha : raw41132step1 = -raw41132step0 := by apply Matrix.ext; change ∀ i j, raw41132step1 i j = -(raw41132step0 i j); unfold raw41132step1 raw41132step0; decide +kernel
      have hl : raw41132step1Labels = raw41132step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1151 node1151Labels := by rfl

theorem canonical41133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41133 raw41133Labels = mixedMoment B node1160 node1160Labels := by
  calc
    mixedMoment B raw41133 raw41133Labels = mixedMoment B raw41133step0 raw41133step0Labels := by
      have hz : ∀ j, raw41133 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41133step0 = (fun i j => raw41133 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41133step0 raw41133; decide +kernel
      have hl : raw41133step0Labels = raw41133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41133 raw41133Labels permutation434 hz
    mixedMoment B raw41133step0 raw41133step0Labels = mixedMoment B raw41133step1 raw41133step1Labels := by
      have ha : raw41133step1 = (fun i j => raw41133step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41133step1 raw41133step0; decide +kernel
      have hl : raw41133step1Labels = raw41133step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41133step0 raw41133step0Labels permutation37 permutation6
    mixedMoment B raw41133step1 raw41133step1Labels = mixedMoment B raw41133step2 raw41133step2Labels := by
      have ha : raw41133step2 = -raw41133step1 := by apply Matrix.ext; change ∀ i j, raw41133step2 i j = -(raw41133step1 i j); unfold raw41133step2 raw41133step1; decide +kernel
      have hl : raw41133step2Labels = raw41133step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1160 node1160Labels := by rfl

theorem canonical41134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41134 raw41134Labels = mixedMoment B node1155 node1155Labels := by
  calc
    mixedMoment B raw41134 raw41134Labels = mixedMoment B raw41134step0 raw41134step0Labels := by
      have hz : ∀ j, raw41134 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41134step0 = (fun i j => raw41134 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41134step0 raw41134; decide +kernel
      have hl : raw41134step0Labels = raw41134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41134 raw41134Labels permutation434 hz
    mixedMoment B raw41134step0 raw41134step0Labels = mixedMoment B raw41134step1 raw41134step1Labels := by
      have ha : raw41134step1 = (fun i j => raw41134step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41134step1 raw41134step0; decide +kernel
      have hl : raw41134step1Labels = raw41134step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41134step0 raw41134step0Labels permutation34 permutation6
    mixedMoment B raw41134step1 raw41134step1Labels = mixedMoment B raw41134step2 raw41134step2Labels := by
      have ha : raw41134step2 = -raw41134step1 := by apply Matrix.ext; change ∀ i j, raw41134step2 i j = -(raw41134step1 i j); unfold raw41134step2 raw41134step1; decide +kernel
      have hl : raw41134step2Labels = raw41134step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1155 node1155Labels := by rfl

theorem canonical41135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41135 raw41135Labels = mixedMoment B node1149 node1149Labels := by
  calc
    mixedMoment B raw41135 raw41135Labels = mixedMoment B raw41135step0 raw41135step0Labels := by
      have ha : raw41135step0 = (fun i j => raw41135 (permutation175 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41135step0 raw41135; decide +kernel
      have hl : raw41135step0Labels = raw41135Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41135 raw41135Labels permutation175 permutation6
    mixedMoment B raw41135step0 raw41135step0Labels = mixedMoment B raw41135step1 raw41135step1Labels := by
      have ha : raw41135step1 = -raw41135step0 := by apply Matrix.ext; change ∀ i j, raw41135step1 i j = -(raw41135step0 i j); unfold raw41135step1 raw41135step0; decide +kernel
      have hl : raw41135step1Labels = raw41135step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1149 node1149Labels := by rfl

theorem canonical41136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41136 raw41136Labels = mixedMoment B node1169 node1169Labels := by
  calc
    mixedMoment B raw41136 raw41136Labels = mixedMoment B raw41136step0 raw41136step0Labels := by
      have ha : raw41136step0 = (fun i j => raw41136 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41136step0 raw41136; decide +kernel
      have hl : raw41136step0Labels = raw41136Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41136 raw41136Labels permutation152 permutation6
    mixedMoment B raw41136step0 raw41136step0Labels = mixedMoment B raw41136step1 raw41136step1Labels := by
      have ha : raw41136step1 = -raw41136step0 := by apply Matrix.ext; change ∀ i j, raw41136step1 i j = -(raw41136step0 i j); unfold raw41136step1 raw41136step0; decide +kernel
      have hl : raw41136step1Labels = raw41136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1169 node1169Labels := by rfl

theorem canonical41137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41137 raw41137Labels = mixedMoment B node1150 node1150Labels := by
  calc
    mixedMoment B raw41137 raw41137Labels = mixedMoment B raw41137step0 raw41137step0Labels := by
      have ha : raw41137step0 = (fun i j => raw41137 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41137step0 raw41137; decide +kernel
      have hl : raw41137step0Labels = raw41137Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41137 raw41137Labels permutation164 permutation6
    mixedMoment B raw41137step0 raw41137step0Labels = mixedMoment B raw41137step1 raw41137step1Labels := by
      have ha : raw41137step1 = -raw41137step0 := by apply Matrix.ext; change ∀ i j, raw41137step1 i j = -(raw41137step0 i j); unfold raw41137step1 raw41137step0; decide +kernel
      have hl : raw41137step1Labels = raw41137step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1150 node1150Labels := by rfl

theorem canonical41138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41138 raw41138Labels = mixedMoment B node1159 node1159Labels := by
  calc
    mixedMoment B raw41138 raw41138Labels = mixedMoment B raw41138step0 raw41138step0Labels := by
      have hz : ∀ j, raw41138 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41138step0 = (fun i j => raw41138 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41138step0 raw41138; decide +kernel
      have hl : raw41138step0Labels = raw41138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41138 raw41138Labels permutation434 hz
    mixedMoment B raw41138step0 raw41138step0Labels = mixedMoment B raw41138step1 raw41138step1Labels := by
      have ha : raw41138step1 = (fun i j => raw41138step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41138step1 raw41138step0; decide +kernel
      have hl : raw41138step1Labels = raw41138step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41138step0 raw41138step0Labels permutation36 permutation6
    mixedMoment B raw41138step1 raw41138step1Labels = mixedMoment B raw41138step2 raw41138step2Labels := by
      have ha : raw41138step2 = -raw41138step1 := by apply Matrix.ext; change ∀ i j, raw41138step2 i j = -(raw41138step1 i j); unfold raw41138step2 raw41138step1; decide +kernel
      have hl : raw41138step2Labels = raw41138step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1159 node1159Labels := by rfl

theorem canonical41139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41139 raw41139Labels = mixedMoment B node1115 node1115Labels := by
  calc
    mixedMoment B raw41139 raw41139Labels = mixedMoment B raw41139step0 raw41139step0Labels := by
      have hz : ∀ j, raw41139 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41139step0 = (fun i j => raw41139 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41139step0 raw41139; decide +kernel
      have hl : raw41139step0Labels = raw41139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41139 raw41139Labels permutation434 hz
    mixedMoment B raw41139step0 raw41139step0Labels = mixedMoment B raw41139step1 raw41139step1Labels := by
      have ha : raw41139step1 = (fun i j => raw41139step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41139step1 raw41139step0; decide +kernel
      have hl : raw41139step1Labels = raw41139step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41139step0 raw41139step0Labels permutation145 permutation6
    _ = mixedMoment B node1115 node1115Labels := by rfl

theorem canonical41140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41140 raw41140Labels = mixedMoment B node1148 node1148Labels := by
  calc
    mixedMoment B raw41140 raw41140Labels = mixedMoment B raw41140step0 raw41140step0Labels := by
      have ha : raw41140step0 = (fun i j => raw41140 (permutation174 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41140step0 raw41140; decide +kernel
      have hl : raw41140step0Labels = raw41140Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41140 raw41140Labels permutation174 permutation6
    mixedMoment B raw41140step0 raw41140step0Labels = mixedMoment B raw41140step1 raw41140step1Labels := by
      have ha : raw41140step1 = -raw41140step0 := by apply Matrix.ext; change ∀ i j, raw41140step1 i j = -(raw41140step0 i j); unfold raw41140step1 raw41140step0; decide +kernel
      have hl : raw41140step1Labels = raw41140step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1148 node1148Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1696 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1696) =
      Integer.Sparse.eval keyMomentRow1696 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1696).leftCharge (GramAssembly.key 1696).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2339) := by
    have ha : gramCharges (GramAssembly.key 1696).leftCharge (GramAssembly.key 1696).rightCharge = raw41109 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41109Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41109 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1696).leftCharge (GramAssembly.key 1696).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1696, Integer.Sparse.eval]

theorem keyMoment1697 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1697) =
      Integer.Sparse.eval keyMomentRow1697 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1697).leftCharge (GramAssembly.key 1697).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1310) := by
    have ha : gramCharges (GramAssembly.key 1697).leftCharge (GramAssembly.key 1697).rightCharge = raw41110 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41110Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41110 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1697).leftCharge (GramAssembly.key 1697).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1697, Integer.Sparse.eval]

theorem keyMoment1698 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1698) =
      Integer.Sparse.eval keyMomentRow1698 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1698).leftCharge (GramAssembly.key 1698).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1245) := by
    have ha : gramCharges (GramAssembly.key 1698).leftCharge (GramAssembly.key 1698).rightCharge = raw41111 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41111Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41111 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1698).leftCharge (GramAssembly.key 1698).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1698, Integer.Sparse.eval]

theorem keyMoment1699 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1699) =
      Integer.Sparse.eval keyMomentRow1699 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1699).leftCharge (GramAssembly.key 1699).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1306) := by
    have ha : gramCharges (GramAssembly.key 1699).leftCharge (GramAssembly.key 1699).rightCharge = raw41112 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41112Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41112 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1699).leftCharge (GramAssembly.key 1699).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1699, Integer.Sparse.eval]

theorem keyMoment1700 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1700) =
      Integer.Sparse.eval keyMomentRow1700 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1700).leftCharge (GramAssembly.key 1700).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1291) := by
    have ha : gramCharges (GramAssembly.key 1700).leftCharge (GramAssembly.key 1700).rightCharge = raw41113 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41113Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41113 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1700).leftCharge (GramAssembly.key 1700).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1700, Integer.Sparse.eval]

theorem keyMoment1701 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1701) =
      Integer.Sparse.eval keyMomentRow1701 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1701).leftCharge (GramAssembly.key 1701).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1241) := by
    have ha : gramCharges (GramAssembly.key 1701).leftCharge (GramAssembly.key 1701).rightCharge = raw41114 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41114Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41114 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1701).leftCharge (GramAssembly.key 1701).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1701, Integer.Sparse.eval]

theorem keyMoment1702 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1702) =
      Integer.Sparse.eval keyMomentRow1702 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1702).leftCharge (GramAssembly.key 1702).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1233) := by
    have ha : gramCharges (GramAssembly.key 1702).leftCharge (GramAssembly.key 1702).rightCharge = raw41115 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41115Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41115 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1702).leftCharge (GramAssembly.key 1702).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1702, Integer.Sparse.eval]

theorem keyMoment1703 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1703) =
      Integer.Sparse.eval keyMomentRow1703 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1703).leftCharge (GramAssembly.key 1703).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1295) := by
    have ha : gramCharges (GramAssembly.key 1703).leftCharge (GramAssembly.key 1703).rightCharge = raw41116 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41116Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41116 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1703).leftCharge (GramAssembly.key 1703).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1703, Integer.Sparse.eval]

theorem keyMoment1704 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1704) =
      Integer.Sparse.eval keyMomentRow1704 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1704).leftCharge (GramAssembly.key 1704).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1243) := by
    have ha : gramCharges (GramAssembly.key 1704).leftCharge (GramAssembly.key 1704).rightCharge = raw41117 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41117Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41117 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1704).leftCharge (GramAssembly.key 1704).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1704, Integer.Sparse.eval]

theorem keyMoment1705 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1705) =
      Integer.Sparse.eval keyMomentRow1705 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1705).leftCharge (GramAssembly.key 1705).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1237) := by
    have ha : gramCharges (GramAssembly.key 1705).leftCharge (GramAssembly.key 1705).rightCharge = raw41118 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41118Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41118 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1705).leftCharge (GramAssembly.key 1705).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1705, Integer.Sparse.eval]

theorem keyMoment1706 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1706) =
      Integer.Sparse.eval keyMomentRow1706 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1706).leftCharge (GramAssembly.key 1706).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1273) := by
    have ha : gramCharges (GramAssembly.key 1706).leftCharge (GramAssembly.key 1706).rightCharge = raw41119 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41119Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41119 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1706).leftCharge (GramAssembly.key 1706).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1706, Integer.Sparse.eval]

theorem keyMoment1707 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1707) =
      Integer.Sparse.eval keyMomentRow1707 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1707).leftCharge (GramAssembly.key 1707).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1261) := by
    have ha : gramCharges (GramAssembly.key 1707).leftCharge (GramAssembly.key 1707).rightCharge = raw41120 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41120Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41120 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1707).leftCharge (GramAssembly.key 1707).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1707, Integer.Sparse.eval]

theorem keyMoment1708 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1708) =
      Integer.Sparse.eval keyMomentRow1708 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1708).leftCharge (GramAssembly.key 1708).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1219) := by
    have ha : gramCharges (GramAssembly.key 1708).leftCharge (GramAssembly.key 1708).rightCharge = raw41121 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41121Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41121 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1708).leftCharge (GramAssembly.key 1708).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1708, Integer.Sparse.eval]

theorem keyMoment1709 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1709) =
      Integer.Sparse.eval keyMomentRow1709 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1709).leftCharge (GramAssembly.key 1709).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1212) := by
    have ha : gramCharges (GramAssembly.key 1709).leftCharge (GramAssembly.key 1709).rightCharge = raw41122 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41122Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41122 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1709).leftCharge (GramAssembly.key 1709).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1709, Integer.Sparse.eval]

theorem keyMoment1710 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1710) =
      Integer.Sparse.eval keyMomentRow1710 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1710).leftCharge (GramAssembly.key 1710).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1270) := by
    have ha : gramCharges (GramAssembly.key 1710).leftCharge (GramAssembly.key 1710).rightCharge = raw41123 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41123Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41123 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1710).leftCharge (GramAssembly.key 1710).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1710, Integer.Sparse.eval]

theorem keyMoment1711 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1711) =
      Integer.Sparse.eval keyMomentRow1711 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1711).leftCharge (GramAssembly.key 1711).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1217) := by
    have ha : gramCharges (GramAssembly.key 1711).leftCharge (GramAssembly.key 1711).rightCharge = raw41124 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41124Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41124 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1711).leftCharge (GramAssembly.key 1711).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1711, Integer.Sparse.eval]

theorem keyMoment1712 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1712) =
      Integer.Sparse.eval keyMomentRow1712 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1712).leftCharge (GramAssembly.key 1712).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1264) := by
    have ha : gramCharges (GramAssembly.key 1712).leftCharge (GramAssembly.key 1712).rightCharge = raw41125 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41125Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41125 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1712).leftCharge (GramAssembly.key 1712).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1712, Integer.Sparse.eval]

theorem keyMoment1713 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1713) =
      Integer.Sparse.eval keyMomentRow1713 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1713).leftCharge (GramAssembly.key 1713).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1221) := by
    have ha : gramCharges (GramAssembly.key 1713).leftCharge (GramAssembly.key 1713).rightCharge = raw41126 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41126Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41126 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1713).leftCharge (GramAssembly.key 1713).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1713, Integer.Sparse.eval]

theorem keyMoment1714 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1714) =
      Integer.Sparse.eval keyMomentRow1714 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1714).leftCharge (GramAssembly.key 1714).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1215) := by
    have ha : gramCharges (GramAssembly.key 1714).leftCharge (GramAssembly.key 1714).rightCharge = raw41127 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41127Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41127 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1714).leftCharge (GramAssembly.key 1714).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1714, Integer.Sparse.eval]

theorem keyMoment1715 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1715) =
      Integer.Sparse.eval keyMomentRow1715 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1715).leftCharge (GramAssembly.key 1715).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1174) := by
    have ha : gramCharges (GramAssembly.key 1715).leftCharge (GramAssembly.key 1715).rightCharge = raw41128 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41128Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41128 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1715).leftCharge (GramAssembly.key 1715).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1715, Integer.Sparse.eval]

theorem keyMoment1716 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1716) =
      Integer.Sparse.eval keyMomentRow1716 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1716).leftCharge (GramAssembly.key 1716).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1153) := by
    have ha : gramCharges (GramAssembly.key 1716).leftCharge (GramAssembly.key 1716).rightCharge = raw41129 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41129Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41129 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1716).leftCharge (GramAssembly.key 1716).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1716, Integer.Sparse.eval]

theorem keyMoment1717 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1717) =
      Integer.Sparse.eval keyMomentRow1717 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1717).leftCharge (GramAssembly.key 1717).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1171) := by
    have ha : gramCharges (GramAssembly.key 1717).leftCharge (GramAssembly.key 1717).rightCharge = raw41130 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41130Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41130 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1717).leftCharge (GramAssembly.key 1717).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1717, Integer.Sparse.eval]

theorem keyMoment1718 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1718) =
      Integer.Sparse.eval keyMomentRow1718 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1718).leftCharge (GramAssembly.key 1718).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1156) := by
    have ha : gramCharges (GramAssembly.key 1718).leftCharge (GramAssembly.key 1718).rightCharge = raw41131 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41131Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41131 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1718).leftCharge (GramAssembly.key 1718).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1718, Integer.Sparse.eval]

theorem keyMoment1719 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1719) =
      Integer.Sparse.eval keyMomentRow1719 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1719).leftCharge (GramAssembly.key 1719).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1151) := by
    have ha : gramCharges (GramAssembly.key 1719).leftCharge (GramAssembly.key 1719).rightCharge = raw41132 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41132Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41132 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1719).leftCharge (GramAssembly.key 1719).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1719, Integer.Sparse.eval]

theorem keyMoment1720 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1720) =
      Integer.Sparse.eval keyMomentRow1720 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1720).leftCharge (GramAssembly.key 1720).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1160) := by
    have ha : gramCharges (GramAssembly.key 1720).leftCharge (GramAssembly.key 1720).rightCharge = raw41133 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41133Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41133 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1720).leftCharge (GramAssembly.key 1720).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1720, Integer.Sparse.eval]

theorem keyMoment1721 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1721) =
      Integer.Sparse.eval keyMomentRow1721 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1721).leftCharge (GramAssembly.key 1721).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1155) := by
    have ha : gramCharges (GramAssembly.key 1721).leftCharge (GramAssembly.key 1721).rightCharge = raw41134 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41134Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41134 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1721).leftCharge (GramAssembly.key 1721).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1721, Integer.Sparse.eval]

theorem keyMoment1722 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1722) =
      Integer.Sparse.eval keyMomentRow1722 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1722).leftCharge (GramAssembly.key 1722).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1149) := by
    have ha : gramCharges (GramAssembly.key 1722).leftCharge (GramAssembly.key 1722).rightCharge = raw41135 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41135Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41135 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1722).leftCharge (GramAssembly.key 1722).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1722, Integer.Sparse.eval]

theorem keyMoment1723 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1723) =
      Integer.Sparse.eval keyMomentRow1723 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1723).leftCharge (GramAssembly.key 1723).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1169) := by
    have ha : gramCharges (GramAssembly.key 1723).leftCharge (GramAssembly.key 1723).rightCharge = raw41136 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41136Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41136 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1723).leftCharge (GramAssembly.key 1723).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1723, Integer.Sparse.eval]

theorem keyMoment1724 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1724) =
      Integer.Sparse.eval keyMomentRow1724 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1724).leftCharge (GramAssembly.key 1724).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1150) := by
    have ha : gramCharges (GramAssembly.key 1724).leftCharge (GramAssembly.key 1724).rightCharge = raw41137 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41137Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41137 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1724).leftCharge (GramAssembly.key 1724).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1724, Integer.Sparse.eval]

theorem keyMoment1725 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1725) =
      Integer.Sparse.eval keyMomentRow1725 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1725).leftCharge (GramAssembly.key 1725).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1159) := by
    have ha : gramCharges (GramAssembly.key 1725).leftCharge (GramAssembly.key 1725).rightCharge = raw41138 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41138Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41138 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1725).leftCharge (GramAssembly.key 1725).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1725, Integer.Sparse.eval]

theorem keyMoment1726 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1726) =
      Integer.Sparse.eval keyMomentRow1726 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1726).leftCharge (GramAssembly.key 1726).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1115) := by
    have ha : gramCharges (GramAssembly.key 1726).leftCharge (GramAssembly.key 1726).rightCharge = raw41139 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41139Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41139 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1726).leftCharge (GramAssembly.key 1726).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1726, Integer.Sparse.eval]

theorem keyMoment1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1727) =
      Integer.Sparse.eval keyMomentRow1727 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1727).leftCharge (GramAssembly.key 1727).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1148) := by
    have ha : gramCharges (GramAssembly.key 1727).leftCharge (GramAssembly.key 1727).rightCharge = raw41140 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41140Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41140 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1727).leftCharge (GramAssembly.key 1727).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1727, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1696 : keyMomentRows (1696 : Fin 2886) =
    keyMomentRow1696 := by decide +kernel

theorem keyMomentRowsAt1697 : keyMomentRows (1697 : Fin 2886) =
    keyMomentRow1697 := by decide +kernel

theorem keyMomentRowsAt1698 : keyMomentRows (1698 : Fin 2886) =
    keyMomentRow1698 := by decide +kernel

theorem keyMomentRowsAt1699 : keyMomentRows (1699 : Fin 2886) =
    keyMomentRow1699 := by decide +kernel

theorem keyMomentRowsAt1700 : keyMomentRows (1700 : Fin 2886) =
    keyMomentRow1700 := by decide +kernel

theorem keyMomentRowsAt1701 : keyMomentRows (1701 : Fin 2886) =
    keyMomentRow1701 := by decide +kernel

theorem keyMomentRowsAt1702 : keyMomentRows (1702 : Fin 2886) =
    keyMomentRow1702 := by decide +kernel

theorem keyMomentRowsAt1703 : keyMomentRows (1703 : Fin 2886) =
    keyMomentRow1703 := by decide +kernel

theorem keyMomentRowsAt1704 : keyMomentRows (1704 : Fin 2886) =
    keyMomentRow1704 := by decide +kernel

theorem keyMomentRowsAt1705 : keyMomentRows (1705 : Fin 2886) =
    keyMomentRow1705 := by decide +kernel

theorem keyMomentRowsAt1706 : keyMomentRows (1706 : Fin 2886) =
    keyMomentRow1706 := by decide +kernel

theorem keyMomentRowsAt1707 : keyMomentRows (1707 : Fin 2886) =
    keyMomentRow1707 := by decide +kernel

theorem keyMomentRowsAt1708 : keyMomentRows (1708 : Fin 2886) =
    keyMomentRow1708 := by decide +kernel

theorem keyMomentRowsAt1709 : keyMomentRows (1709 : Fin 2886) =
    keyMomentRow1709 := by decide +kernel

theorem keyMomentRowsAt1710 : keyMomentRows (1710 : Fin 2886) =
    keyMomentRow1710 := by decide +kernel

theorem keyMomentRowsAt1711 : keyMomentRows (1711 : Fin 2886) =
    keyMomentRow1711 := by decide +kernel

theorem keyMomentRowsAt1712 : keyMomentRows (1712 : Fin 2886) =
    keyMomentRow1712 := by decide +kernel

theorem keyMomentRowsAt1713 : keyMomentRows (1713 : Fin 2886) =
    keyMomentRow1713 := by decide +kernel

theorem keyMomentRowsAt1714 : keyMomentRows (1714 : Fin 2886) =
    keyMomentRow1714 := by decide +kernel

theorem keyMomentRowsAt1715 : keyMomentRows (1715 : Fin 2886) =
    keyMomentRow1715 := by decide +kernel

theorem keyMomentRowsAt1716 : keyMomentRows (1716 : Fin 2886) =
    keyMomentRow1716 := by decide +kernel

theorem keyMomentRowsAt1717 : keyMomentRows (1717 : Fin 2886) =
    keyMomentRow1717 := by decide +kernel

theorem keyMomentRowsAt1718 : keyMomentRows (1718 : Fin 2886) =
    keyMomentRow1718 := by decide +kernel

theorem keyMomentRowsAt1719 : keyMomentRows (1719 : Fin 2886) =
    keyMomentRow1719 := by decide +kernel

theorem keyMomentRowsAt1720 : keyMomentRows (1720 : Fin 2886) =
    keyMomentRow1720 := by decide +kernel

theorem keyMomentRowsAt1721 : keyMomentRows (1721 : Fin 2886) =
    keyMomentRow1721 := by decide +kernel

theorem keyMomentRowsAt1722 : keyMomentRows (1722 : Fin 2886) =
    keyMomentRow1722 := by decide +kernel

theorem keyMomentRowsAt1723 : keyMomentRows (1723 : Fin 2886) =
    keyMomentRow1723 := by decide +kernel

theorem keyMomentRowsAt1724 : keyMomentRows (1724 : Fin 2886) =
    keyMomentRow1724 := by decide +kernel

theorem keyMomentRowsAt1725 : keyMomentRows (1725 : Fin 2886) =
    keyMomentRow1725 := by decide +kernel

theorem keyMomentRowsAt1726 : keyMomentRows (1726 : Fin 2886) =
    keyMomentRow1726 := by decide +kernel

theorem keyMomentRowsAt1727 : keyMomentRows (1727 : Fin 2886) =
    keyMomentRow1727 := by decide +kernel

theorem keyMomentChunkSound53_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 53) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1696 ∨ k.val = 1697 ∨ k.val = 1698 ∨ k.val = 1699 ∨ k.val = 1700 ∨ k.val = 1701 ∨ k.val = 1702 ∨ k.val = 1703 ∨ k.val = 1704 ∨ k.val = 1705 ∨ k.val = 1706 ∨ k.val = 1707 ∨ k.val = 1708 ∨ k.val = 1709 ∨ k.val = 1710 ∨ k.val = 1711 ∨ k.val = 1712 ∨ k.val = 1713 ∨ k.val = 1714 ∨ k.val = 1715 ∨ k.val = 1716 ∨ k.val = 1717 ∨ k.val = 1718 ∨ k.val = 1719 ∨ k.val = 1720 ∨ k.val = 1721 ∨ k.val = 1722 ∨ k.val = 1723 ∨ k.val = 1724 ∨ k.val = 1725 ∨ k.val = 1726 ∨ k.val = 1727 := by omega
  rcases heq with h1696 | h1697 | h1698 | h1699 | h1700 | h1701 | h1702 | h1703 | h1704 | h1705 | h1706 | h1707 | h1708 | h1709 | h1710 | h1711 | h1712 | h1713 | h1714 | h1715 | h1716 | h1717 | h1718 | h1719 | h1720 | h1721 | h1722 | h1723 | h1724 | h1725 | h1726 | h1727
  · have he : k = (1696 : Fin 2886) := Fin.ext h1696
    subst k
    rw [keyMomentRowsAt1696]
    exact keyMoment1696 B hB
  · have he : k = (1697 : Fin 2886) := Fin.ext h1697
    subst k
    rw [keyMomentRowsAt1697]
    exact keyMoment1697 B hB
  · have he : k = (1698 : Fin 2886) := Fin.ext h1698
    subst k
    rw [keyMomentRowsAt1698]
    exact keyMoment1698 B hB
  · have he : k = (1699 : Fin 2886) := Fin.ext h1699
    subst k
    rw [keyMomentRowsAt1699]
    exact keyMoment1699 B hB
  · have he : k = (1700 : Fin 2886) := Fin.ext h1700
    subst k
    rw [keyMomentRowsAt1700]
    exact keyMoment1700 B hB
  · have he : k = (1701 : Fin 2886) := Fin.ext h1701
    subst k
    rw [keyMomentRowsAt1701]
    exact keyMoment1701 B hB
  · have he : k = (1702 : Fin 2886) := Fin.ext h1702
    subst k
    rw [keyMomentRowsAt1702]
    exact keyMoment1702 B hB
  · have he : k = (1703 : Fin 2886) := Fin.ext h1703
    subst k
    rw [keyMomentRowsAt1703]
    exact keyMoment1703 B hB
  · have he : k = (1704 : Fin 2886) := Fin.ext h1704
    subst k
    rw [keyMomentRowsAt1704]
    exact keyMoment1704 B hB
  · have he : k = (1705 : Fin 2886) := Fin.ext h1705
    subst k
    rw [keyMomentRowsAt1705]
    exact keyMoment1705 B hB
  · have he : k = (1706 : Fin 2886) := Fin.ext h1706
    subst k
    rw [keyMomentRowsAt1706]
    exact keyMoment1706 B hB
  · have he : k = (1707 : Fin 2886) := Fin.ext h1707
    subst k
    rw [keyMomentRowsAt1707]
    exact keyMoment1707 B hB
  · have he : k = (1708 : Fin 2886) := Fin.ext h1708
    subst k
    rw [keyMomentRowsAt1708]
    exact keyMoment1708 B hB
  · have he : k = (1709 : Fin 2886) := Fin.ext h1709
    subst k
    rw [keyMomentRowsAt1709]
    exact keyMoment1709 B hB
  · have he : k = (1710 : Fin 2886) := Fin.ext h1710
    subst k
    rw [keyMomentRowsAt1710]
    exact keyMoment1710 B hB
  · have he : k = (1711 : Fin 2886) := Fin.ext h1711
    subst k
    rw [keyMomentRowsAt1711]
    exact keyMoment1711 B hB
  · have he : k = (1712 : Fin 2886) := Fin.ext h1712
    subst k
    rw [keyMomentRowsAt1712]
    exact keyMoment1712 B hB
  · have he : k = (1713 : Fin 2886) := Fin.ext h1713
    subst k
    rw [keyMomentRowsAt1713]
    exact keyMoment1713 B hB
  · have he : k = (1714 : Fin 2886) := Fin.ext h1714
    subst k
    rw [keyMomentRowsAt1714]
    exact keyMoment1714 B hB
  · have he : k = (1715 : Fin 2886) := Fin.ext h1715
    subst k
    rw [keyMomentRowsAt1715]
    exact keyMoment1715 B hB
  · have he : k = (1716 : Fin 2886) := Fin.ext h1716
    subst k
    rw [keyMomentRowsAt1716]
    exact keyMoment1716 B hB
  · have he : k = (1717 : Fin 2886) := Fin.ext h1717
    subst k
    rw [keyMomentRowsAt1717]
    exact keyMoment1717 B hB
  · have he : k = (1718 : Fin 2886) := Fin.ext h1718
    subst k
    rw [keyMomentRowsAt1718]
    exact keyMoment1718 B hB
  · have he : k = (1719 : Fin 2886) := Fin.ext h1719
    subst k
    rw [keyMomentRowsAt1719]
    exact keyMoment1719 B hB
  · have he : k = (1720 : Fin 2886) := Fin.ext h1720
    subst k
    rw [keyMomentRowsAt1720]
    exact keyMoment1720 B hB
  · have he : k = (1721 : Fin 2886) := Fin.ext h1721
    subst k
    rw [keyMomentRowsAt1721]
    exact keyMoment1721 B hB
  · have he : k = (1722 : Fin 2886) := Fin.ext h1722
    subst k
    rw [keyMomentRowsAt1722]
    exact keyMoment1722 B hB
  · have he : k = (1723 : Fin 2886) := Fin.ext h1723
    subst k
    rw [keyMomentRowsAt1723]
    exact keyMoment1723 B hB
  · have he : k = (1724 : Fin 2886) := Fin.ext h1724
    subst k
    rw [keyMomentRowsAt1724]
    exact keyMoment1724 B hB
  · have he : k = (1725 : Fin 2886) := Fin.ext h1725
    subst k
    rw [keyMomentRowsAt1725]
    exact keyMoment1725 B hB
  · have he : k = (1726 : Fin 2886) := Fin.ext h1726
    subst k
    rw [keyMomentRowsAt1726]
    exact keyMoment1726 B hB
  · have he : k = (1727 : Fin 2886) := Fin.ext h1727
    subst k
    rw [keyMomentRowsAt1727]
    exact keyMoment1727 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound53_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound53_e_oai
