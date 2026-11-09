-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound57_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:58:12.443128+00:00
-- url     : https://prove2.me/submissions/f424a703-8ba6-464e-a504-3c62cb8c4753

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical322
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41237 raw41237Labels = mixedMoment B node4049 node4049Labels := by
  calc
    mixedMoment B raw41237 raw41237Labels = mixedMoment B raw41237step0 raw41237step0Labels := by
      have hz : ∀ j, raw41237 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41237step0 = (fun i j => raw41237 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41237step0 raw41237; decide +kernel
      have hl : raw41237step0Labels = raw41237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41237 raw41237Labels permutation434 hz
    mixedMoment B raw41237step0 raw41237step0Labels = mixedMoment B raw41237step1 raw41237step1Labels := by
      have hz : ∀ j, raw41237step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41237step1 = (fun i j => raw41237step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41237step1 raw41237step0; decide +kernel
      have hl : raw41237step1Labels = raw41237step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41237step0 raw41237step0Labels permutation80 hz
    mixedMoment B raw41237step1 raw41237step1Labels = mixedMoment B raw41237step2 raw41237step2Labels := by
      have ha : raw41237step2 = (fun i j => raw41237step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41237step2 raw41237step1; decide +kernel
      have hl : raw41237step2Labels = raw41237step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41237step1 raw41237step1Labels permutation8 permutation3
    _ = mixedMoment B node4049 node4049Labels := by rfl

theorem canonical41238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41238 raw41238Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw41238 raw41238Labels = mixedMoment B raw41238step0 raw41238step0Labels := by
      have hz : ∀ j, raw41238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41238step0 = (fun i j => raw41238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41238step0 raw41238; decide +kernel
      have hl : raw41238step0Labels = raw41238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41238 raw41238Labels permutation346 hz
    mixedMoment B raw41238step0 raw41238step0Labels = mixedMoment B raw41238step1 raw41238step1Labels := by
      have ha : raw41238step1 = (fun i j => raw41238step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41238step1 raw41238step0; decide +kernel
      have hl : raw41238step1Labels = raw41238step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41238step0 raw41238step0Labels permutation145 permutation3
    mixedMoment B raw41238step1 raw41238step1Labels = mixedMoment B raw41238step2 raw41238step2Labels := by
      have ha : raw41238step2 = -raw41238step1 := by apply Matrix.ext; change ∀ i j, raw41238step2 i j = -(raw41238step1 i j); unfold raw41238step2 raw41238step1; decide +kernel
      have hl : raw41238step2Labels = raw41238step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4010 node4010Labels := by rfl

theorem canonical41239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41239 raw41239Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw41239 raw41239Labels = mixedMoment B raw41239step0 raw41239step0Labels := by
      have hz : ∀ j, raw41239 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41239step0 = (fun i j => raw41239 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41239step0 raw41239; decide +kernel
      have hl : raw41239step0Labels = raw41239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41239 raw41239Labels permutation346 hz
    mixedMoment B raw41239step0 raw41239step0Labels = mixedMoment B raw41239step1 raw41239step1Labels := by
      have ha : raw41239step1 = (fun i j => raw41239step0 (permutation118 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41239step1 raw41239step0; decide +kernel
      have hl : raw41239step1Labels = raw41239step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41239step0 raw41239step0Labels permutation118 permutation6
    mixedMoment B raw41239step1 raw41239step1Labels = mixedMoment B raw41239step2 raw41239step2Labels := by
      have ha : raw41239step2 = -raw41239step1 := by apply Matrix.ext; change ∀ i j, raw41239step2 i j = -(raw41239step1 i j); unfold raw41239step2 raw41239step1; decide +kernel
      have hl : raw41239step2Labels = raw41239step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical41240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41240 raw41240Labels = mixedMoment B node4047 node4047Labels := by
  calc
    mixedMoment B raw41240 raw41240Labels = mixedMoment B raw41240step0 raw41240step0Labels := by
      have hz : ∀ j, raw41240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41240step0 = (fun i j => raw41240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41240step0 raw41240; decide +kernel
      have hl : raw41240step0Labels = raw41240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41240 raw41240Labels permutation346 hz
    mixedMoment B raw41240step0 raw41240step0Labels = mixedMoment B raw41240step1 raw41240step1Labels := by
      have ha : raw41240step1 = (fun i j => raw41240step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41240step1 raw41240step0; decide +kernel
      have hl : raw41240step1Labels = raw41240step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41240step0 raw41240step0Labels permutation32 permutation3
    _ = mixedMoment B node4047 node4047Labels := by rfl

theorem canonical41241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41241 raw41241Labels = mixedMoment B node4048 node4048Labels := by
  calc
    mixedMoment B raw41241 raw41241Labels = mixedMoment B raw41241step0 raw41241step0Labels := by
      have hz : ∀ j, raw41241 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41241step0 = (fun i j => raw41241 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41241step0 raw41241; decide +kernel
      have hl : raw41241step0Labels = raw41241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41241 raw41241Labels permutation346 hz
    mixedMoment B raw41241step0 raw41241step0Labels = mixedMoment B raw41241step1 raw41241step1Labels := by
      have ha : raw41241step1 = (fun i j => raw41241step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41241step1 raw41241step0; decide +kernel
      have hl : raw41241step1Labels = raw41241step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41241step0 raw41241step0Labels permutation32 permutation3
    _ = mixedMoment B node4048 node4048Labels := by rfl

theorem canonical41242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41242 raw41242Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw41242 raw41242Labels = mixedMoment B raw41242step0 raw41242step0Labels := by
      have hz : ∀ j, raw41242 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41242step0 = (fun i j => raw41242 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41242step0 raw41242; decide +kernel
      have hl : raw41242step0Labels = raw41242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41242 raw41242Labels permutation346 hz
    mixedMoment B raw41242step0 raw41242step0Labels = mixedMoment B raw41242step1 raw41242step1Labels := by
      have ha : raw41242step1 = (fun i j => raw41242step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41242step1 raw41242step0; decide +kernel
      have hl : raw41242step1Labels = raw41242step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41242step0 raw41242step0Labels permutation101 permutation6
    mixedMoment B raw41242step1 raw41242step1Labels = mixedMoment B raw41242step2 raw41242step2Labels := by
      have ha : raw41242step2 = -raw41242step1 := by apply Matrix.ext; change ∀ i j, raw41242step2 i j = -(raw41242step1 i j); unfold raw41242step2 raw41242step1; decide +kernel
      have hl : raw41242step2Labels = raw41242step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3903 node3903Labels := by rfl

theorem canonical41243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41243 raw41243Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw41243 raw41243Labels = mixedMoment B raw41243step0 raw41243step0Labels := by
      have ha : raw41243step0 = (fun i j => raw41243 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41243step0 raw41243; decide +kernel
      have hl : raw41243step0Labels = raw41243Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41243 raw41243Labels permutation590 permutation6
    _ = mixedMoment B node4025 node4025Labels := by rfl

theorem canonical41244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41244 raw41244Labels = mixedMoment B node4046 node4046Labels := by
  calc
    mixedMoment B raw41244 raw41244Labels = mixedMoment B raw41244step0 raw41244step0Labels := by
      have ha : raw41244step0 = (fun i j => raw41244 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41244step0 raw41244; decide +kernel
      have hl : raw41244step0Labels = raw41244Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41244 raw41244Labels permutation152 permutation3
    _ = mixedMoment B node4046 node4046Labels := by rfl

theorem canonical41245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41245 raw41245Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw41245 raw41245Labels = mixedMoment B raw41245step0 raw41245step0Labels := by
      have hz : ∀ j, raw41245 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41245step0 = (fun i j => raw41245 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41245step0 raw41245; decide +kernel
      have hl : raw41245step0Labels = raw41245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41245 raw41245Labels permutation520 hz
    mixedMoment B raw41245step0 raw41245step0Labels = mixedMoment B raw41245step1 raw41245step1Labels := by
      have ha : raw41245step1 = (fun i j => raw41245step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41245step1 raw41245step0; decide +kernel
      have hl : raw41245step1Labels = raw41245step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41245step0 raw41245step0Labels permutation149 permutation3
    mixedMoment B raw41245step1 raw41245step1Labels = mixedMoment B raw41245step2 raw41245step2Labels := by
      have ha : raw41245step2 = -raw41245step1 := by apply Matrix.ext; change ∀ i j, raw41245step2 i j = -(raw41245step1 i j); unfold raw41245step2 raw41245step1; decide +kernel
      have hl : raw41245step2Labels = raw41245step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2262 node2262Labels := by rfl

theorem canonical41246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41246 raw41246Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw41246 raw41246Labels = mixedMoment B raw41246step0 raw41246step0Labels := by
      have ha : raw41246step0 = (fun i j => raw41246 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41246step0 raw41246; decide +kernel
      have hl : raw41246step0Labels = raw41246Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41246 raw41246Labels permutation686 permutation3
    mixedMoment B raw41246step0 raw41246step0Labels = mixedMoment B raw41246step1 raw41246step1Labels := by
      have ha : raw41246step1 = -raw41246step0 := by apply Matrix.ext; change ∀ i j, raw41246step1 i j = -(raw41246step0 i j); unfold raw41246step1 raw41246step0; decide +kernel
      have hl : raw41246step1Labels = raw41246step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2720 node2720Labels := by rfl

theorem canonical41247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41247 raw41247Labels = mixedMoment B node3036 node3036Labels := by
  calc
    mixedMoment B raw41247 raw41247Labels = mixedMoment B raw41247step0 raw41247step0Labels := by
      have ha : raw41247step0 = (fun i j => raw41247 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41247step0 raw41247; decide +kernel
      have hl : raw41247step0Labels = raw41247Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41247 raw41247Labels permutation686 permutation3
    mixedMoment B raw41247step0 raw41247step0Labels = mixedMoment B raw41247step1 raw41247step1Labels := by
      have ha : raw41247step1 = -raw41247step0 := by apply Matrix.ext; change ∀ i j, raw41247step1 i j = -(raw41247step0 i j); unfold raw41247step1 raw41247step0; decide +kernel
      have hl : raw41247step1Labels = raw41247step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3036 node3036Labels := by rfl

theorem canonical41248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41248 raw41248Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw41248 raw41248Labels = mixedMoment B raw41248step0 raw41248step0Labels := by
      have ha : raw41248step0 = (fun i j => raw41248 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41248step0 raw41248; decide +kernel
      have hl : raw41248step0Labels = raw41248Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41248 raw41248Labels permutation686 permutation3
    mixedMoment B raw41248step0 raw41248step0Labels = mixedMoment B raw41248step1 raw41248step1Labels := by
      have ha : raw41248step1 = -raw41248step0 := by apply Matrix.ext; change ∀ i j, raw41248step1 i j = -(raw41248step0 i j); unfold raw41248step1 raw41248step0; decide +kernel
      have hl : raw41248step1Labels = raw41248step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3805 node3805Labels := by rfl

theorem canonical41249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41249 raw41249Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw41249 raw41249Labels = mixedMoment B raw41249step0 raw41249step0Labels := by
      have ha : raw41249step0 = (fun i j => raw41249 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41249step0 raw41249; decide +kernel
      have hl : raw41249step0Labels = raw41249Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41249 raw41249Labels permutation686 permutation3
    mixedMoment B raw41249step0 raw41249step0Labels = mixedMoment B raw41249step1 raw41249step1Labels := by
      have ha : raw41249step1 = -raw41249step0 := by apply Matrix.ext; change ∀ i j, raw41249step1 i j = -(raw41249step0 i j); unfold raw41249step1 raw41249step0; decide +kernel
      have hl : raw41249step1Labels = raw41249step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3956 node3956Labels := by rfl

theorem canonical41250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41250 raw41250Labels = mixedMoment B node3497 node3497Labels := by
  calc
    mixedMoment B raw41250 raw41250Labels = mixedMoment B raw41250step0 raw41250step0Labels := by
      have ha : raw41250step0 = (fun i j => raw41250 (permutation532 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41250step0 raw41250; decide +kernel
      have hl : raw41250step0Labels = raw41250Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41250 raw41250Labels permutation532 permutation6
    mixedMoment B raw41250step0 raw41250step0Labels = mixedMoment B raw41250step1 raw41250step1Labels := by
      have ha : raw41250step1 = -raw41250step0 := by apply Matrix.ext; change ∀ i j, raw41250step1 i j = -(raw41250step0 i j); unfold raw41250step1 raw41250step0; decide +kernel
      have hl : raw41250step1Labels = raw41250step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3497 node3497Labels := by rfl

theorem canonical41251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41251 raw41251Labels = mixedMoment B node2879 node2879Labels := by
  calc
    mixedMoment B raw41251 raw41251Labels = mixedMoment B raw41251step0 raw41251step0Labels := by
      have hz : ∀ j, raw41251 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41251step0 = (fun i j => raw41251 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41251step0 raw41251; decide +kernel
      have hl : raw41251step0Labels = raw41251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41251 raw41251Labels permutation434 hz
    mixedMoment B raw41251step0 raw41251step0Labels = mixedMoment B raw41251step1 raw41251step1Labels := by
      have ha : raw41251step1 = (fun i j => raw41251step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41251step1 raw41251step0; decide +kernel
      have hl : raw41251step1Labels = raw41251step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41251step0 raw41251step0Labels permutation128 permutation6
    _ = mixedMoment B node2879 node2879Labels := by rfl

theorem canonical41252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41252 raw41252Labels = mixedMoment B node2878 node2878Labels := by
  calc
    mixedMoment B raw41252 raw41252Labels = mixedMoment B raw41252step0 raw41252step0Labels := by
      have ha : raw41252step0 = (fun i j => raw41252 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41252step0 raw41252; decide +kernel
      have hl : raw41252step0Labels = raw41252Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41252 raw41252Labels permutation590 permutation6
    _ = mixedMoment B node2878 node2878Labels := by rfl

theorem canonical41253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41253 raw41253Labels = mixedMoment B node2861 node2861Labels := by
  calc
    mixedMoment B raw41253 raw41253Labels = mixedMoment B raw41253step0 raw41253step0Labels := by
      have ha : raw41253step0 = (fun i j => raw41253 (permutation599 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41253step0 raw41253; decide +kernel
      have hl : raw41253step0Labels = raw41253Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41253 raw41253Labels permutation599 permutation6
    _ = mixedMoment B node2861 node2861Labels := by rfl

theorem canonical41254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41254 raw41254Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw41254 raw41254Labels = mixedMoment B raw41254step0 raw41254step0Labels := by
      have hz : ∀ j, raw41254 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41254step0 = (fun i j => raw41254 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41254step0 raw41254; decide +kernel
      have hl : raw41254step0Labels = raw41254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41254 raw41254Labels permutation520 hz
    mixedMoment B raw41254step0 raw41254step0Labels = mixedMoment B raw41254step1 raw41254step1Labels := by
      have ha : raw41254step1 = (fun i j => raw41254step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41254step1 raw41254step0; decide +kernel
      have hl : raw41254step1Labels = raw41254step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41254step0 raw41254step0Labels permutation151 permutation3
    mixedMoment B raw41254step1 raw41254step1Labels = mixedMoment B raw41254step2 raw41254step2Labels := by
      have ha : raw41254step2 = -raw41254step1 := by apply Matrix.ext; change ∀ i j, raw41254step2 i j = -(raw41254step1 i j); unfold raw41254step2 raw41254step1; decide +kernel
      have hl : raw41254step2Labels = raw41254step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2763 node2763Labels := by rfl

theorem canonical41255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41255 raw41255Labels = mixedMoment B node3084 node3084Labels := by
  calc
    mixedMoment B raw41255 raw41255Labels = mixedMoment B raw41255step0 raw41255step0Labels := by
      have ha : raw41255step0 = (fun i j => raw41255 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41255step0 raw41255; decide +kernel
      have hl : raw41255step0Labels = raw41255Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41255 raw41255Labels permutation688 permutation3
    mixedMoment B raw41255step0 raw41255step0Labels = mixedMoment B raw41255step1 raw41255step1Labels := by
      have ha : raw41255step1 = -raw41255step0 := by apply Matrix.ext; change ∀ i j, raw41255step1 i j = -(raw41255step0 i j); unfold raw41255step1 raw41255step0; decide +kernel
      have hl : raw41255step1Labels = raw41255step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3084 node3084Labels := by rfl

theorem canonical41256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41256 raw41256Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw41256 raw41256Labels = mixedMoment B raw41256step0 raw41256step0Labels := by
      have ha : raw41256step0 = (fun i j => raw41256 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41256step0 raw41256; decide +kernel
      have hl : raw41256step0Labels = raw41256Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41256 raw41256Labels permutation688 permutation3
    mixedMoment B raw41256step0 raw41256step0Labels = mixedMoment B raw41256step1 raw41256step1Labels := by
      have ha : raw41256step1 = -raw41256step0 := by apply Matrix.ext; change ∀ i j, raw41256step1 i j = -(raw41256step0 i j); unfold raw41256step1 raw41256step0; decide +kernel
      have hl : raw41256step1Labels = raw41256step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3978 node3978Labels := by rfl

theorem canonical41257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41257 raw41257Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw41257 raw41257Labels = mixedMoment B raw41257step0 raw41257step0Labels := by
      have ha : raw41257step0 = (fun i j => raw41257 (permutation404 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41257step0 raw41257; decide +kernel
      have hl : raw41257step0Labels = raw41257Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41257 raw41257Labels permutation404 permutation6
    mixedMoment B raw41257step0 raw41257step0Labels = mixedMoment B raw41257step1 raw41257step1Labels := by
      have ha : raw41257step1 = -raw41257step0 := by apply Matrix.ext; change ∀ i j, raw41257step1 i j = -(raw41257step0 i j); unfold raw41257step1 raw41257step0; decide +kernel
      have hl : raw41257step1Labels = raw41257step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3946 node3946Labels := by rfl

theorem canonical41258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41258 raw41258Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw41258 raw41258Labels = mixedMoment B raw41258step0 raw41258step0Labels := by
      have hz : ∀ j, raw41258 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41258step0 = (fun i j => raw41258 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41258step0 raw41258; decide +kernel
      have hl : raw41258step0Labels = raw41258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41258 raw41258Labels permutation434 hz
    mixedMoment B raw41258step0 raw41258step0Labels = mixedMoment B raw41258step1 raw41258step1Labels := by
      have ha : raw41258step1 = (fun i j => raw41258step0 (permutation129 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41258step1 raw41258step0; decide +kernel
      have hl : raw41258step1Labels = raw41258step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41258step0 raw41258step0Labels permutation129 permutation6
    _ = mixedMoment B node2882 node2882Labels := by rfl

theorem canonical41259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41259 raw41259Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw41259 raw41259Labels = mixedMoment B raw41259step0 raw41259step0Labels := by
      have ha : raw41259step0 = (fun i j => raw41259 (permutation600 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41259step0 raw41259; decide +kernel
      have hl : raw41259step0Labels = raw41259Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41259 raw41259Labels permutation600 permutation6
    _ = mixedMoment B node2862 node2862Labels := by rfl

theorem canonical41260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41260 raw41260Labels = mixedMoment B node2600 node2600Labels := by
  calc
    mixedMoment B raw41260 raw41260Labels = mixedMoment B raw41260step0 raw41260step0Labels := by
      have hz : ∀ j, raw41260 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41260step0 = (fun i j => raw41260 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41260step0 raw41260; decide +kernel
      have hl : raw41260step0Labels = raw41260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41260 raw41260Labels permutation520 hz
    mixedMoment B raw41260step0 raw41260step0Labels = mixedMoment B raw41260step1 raw41260step1Labels := by
      have ha : raw41260step1 = (fun i j => raw41260step0 (permutation88 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41260step1 raw41260step0; decide +kernel
      have hl : raw41260step1Labels = raw41260step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41260step0 raw41260step0Labels permutation88 permutation6
    mixedMoment B raw41260step1 raw41260step1Labels = mixedMoment B raw41260step2 raw41260step2Labels := by
      have ha : raw41260step2 = -raw41260step1 := by apply Matrix.ext; change ∀ i j, raw41260step2 i j = -(raw41260step1 i j); unfold raw41260step2 raw41260step1; decide +kernel
      have hl : raw41260step2Labels = raw41260step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2600 node2600Labels := by rfl

theorem canonical41261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41261 raw41261Labels = mixedMoment B node2557 node2557Labels := by
  calc
    mixedMoment B raw41261 raw41261Labels = mixedMoment B raw41261step0 raw41261step0Labels := by
      have ha : raw41261step0 = (fun i j => raw41261 (permutation377 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41261step0 raw41261; decide +kernel
      have hl : raw41261step0Labels = raw41261Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41261 raw41261Labels permutation377 permutation6
    mixedMoment B raw41261step0 raw41261step0Labels = mixedMoment B raw41261step1 raw41261step1Labels := by
      have ha : raw41261step1 = -raw41261step0 := by apply Matrix.ext; change ∀ i j, raw41261step1 i j = -(raw41261step0 i j); unfold raw41261step1 raw41261step0; decide +kernel
      have hl : raw41261step1Labels = raw41261step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2557 node2557Labels := by rfl

theorem canonical41262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41262 raw41262Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw41262 raw41262Labels = mixedMoment B raw41262step0 raw41262step0Labels := by
      have hz : ∀ j, raw41262 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41262step0 = (fun i j => raw41262 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41262step0 raw41262; decide +kernel
      have hl : raw41262step0Labels = raw41262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41262 raw41262Labels permutation434 hz
    mixedMoment B raw41262step0 raw41262step0Labels = mixedMoment B raw41262step1 raw41262step1Labels := by
      have ha : raw41262step1 = (fun i j => raw41262step0 (permutation88 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41262step1 raw41262step0; decide +kernel
      have hl : raw41262step1Labels = raw41262step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41262step0 raw41262step0Labels permutation88 permutation6
    mixedMoment B raw41262step1 raw41262step1Labels = mixedMoment B raw41262step2 raw41262step2Labels := by
      have ha : raw41262step2 = -raw41262step1 := by apply Matrix.ext; change ∀ i j, raw41262step2 i j = -(raw41262step1 i j); unfold raw41262step2 raw41262step1; decide +kernel
      have hl : raw41262step2Labels = raw41262step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2558 node2558Labels := by rfl

theorem canonical41263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41263 raw41263Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw41263 raw41263Labels = mixedMoment B raw41263step0 raw41263step0Labels := by
      have hz : ∀ j, raw41263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41263step0 = (fun i j => raw41263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41263step0 raw41263; decide +kernel
      have hl : raw41263step0Labels = raw41263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41263 raw41263Labels permutation434 hz
    mixedMoment B raw41263step0 raw41263step0Labels = mixedMoment B raw41263step1 raw41263step1Labels := by
      have ha : raw41263step1 = (fun i j => raw41263step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41263step1 raw41263step0; decide +kernel
      have hl : raw41263step1Labels = raw41263step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41263step0 raw41263step0Labels permutation151 permutation3
    mixedMoment B raw41263step1 raw41263step1Labels = mixedMoment B raw41263step2 raw41263step2Labels := by
      have ha : raw41263step2 = -raw41263step1 := by apply Matrix.ext; change ∀ i j, raw41263step2 i j = -(raw41263step1 i j); unfold raw41263step2 raw41263step1; decide +kernel
      have hl : raw41263step2Labels = raw41263step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3903 node3903Labels := by rfl

theorem canonical41264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41264 raw41264Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw41264 raw41264Labels = mixedMoment B raw41264step0 raw41264step0Labels := by
      have hz : ∀ j, raw41264 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41264step0 = (fun i j => raw41264 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41264step0 raw41264; decide +kernel
      have hl : raw41264step0Labels = raw41264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41264 raw41264Labels permutation434 hz
    mixedMoment B raw41264step0 raw41264step0Labels = mixedMoment B raw41264step1 raw41264step1Labels := by
      have ha : raw41264step1 = (fun i j => raw41264step0 (permutation115 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41264step1 raw41264step0; decide +kernel
      have hl : raw41264step1Labels = raw41264step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41264step0 raw41264step0Labels permutation115 permutation6
    mixedMoment B raw41264step1 raw41264step1Labels = mixedMoment B raw41264step2 raw41264step2Labels := by
      have ha : raw41264step2 = -raw41264step1 := by apply Matrix.ext; change ∀ i j, raw41264step2 i j = -(raw41264step1 i j); unfold raw41264step2 raw41264step1; decide +kernel
      have hl : raw41264step2Labels = raw41264step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical41265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41265 raw41265Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw41265 raw41265Labels = mixedMoment B raw41265step0 raw41265step0Labels := by
      have hz : ∀ j, raw41265 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41265step0 = (fun i j => raw41265 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41265step0 raw41265; decide +kernel
      have hl : raw41265step0Labels = raw41265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41265 raw41265Labels permutation434 hz
    mixedMoment B raw41265step0 raw41265step0Labels = mixedMoment B raw41265step1 raw41265step1Labels := by
      have ha : raw41265step1 = (fun i j => raw41265step0 (permutation112 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41265step1 raw41265step0; decide +kernel
      have hl : raw41265step1Labels = raw41265step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41265step0 raw41265step0Labels permutation112 permutation6
    mixedMoment B raw41265step1 raw41265step1Labels = mixedMoment B raw41265step2 raw41265step2Labels := by
      have ha : raw41265step2 = -raw41265step1 := by apply Matrix.ext; change ∀ i j, raw41265step2 i j = -(raw41265step1 i j); unfold raw41265step2 raw41265step1; decide +kernel
      have hl : raw41265step2Labels = raw41265step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical41266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41266 raw41266Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw41266 raw41266Labels = mixedMoment B raw41266step0 raw41266step0Labels := by
      have hz : ∀ j, raw41266 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41266step0 = (fun i j => raw41266 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41266step0 raw41266; decide +kernel
      have hl : raw41266step0Labels = raw41266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41266 raw41266Labels permutation434 hz
    mixedMoment B raw41266step0 raw41266step0Labels = mixedMoment B raw41266step1 raw41266step1Labels := by
      have ha : raw41266step1 = (fun i j => raw41266step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41266step1 raw41266step0; decide +kernel
      have hl : raw41266step1Labels = raw41266step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41266step0 raw41266step0Labels permutation139 permutation6
    mixedMoment B raw41266step1 raw41266step1Labels = mixedMoment B raw41266step2 raw41266step2Labels := by
      have ha : raw41266step2 = -raw41266step1 := by apply Matrix.ext; change ∀ i j, raw41266step2 i j = -(raw41266step1 i j); unfold raw41266step2 raw41266step1; decide +kernel
      have hl : raw41266step2Labels = raw41266step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical41267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41267 raw41267Labels = mixedMoment B node4047 node4047Labels := by
  calc
    mixedMoment B raw41267 raw41267Labels = mixedMoment B raw41267step0 raw41267step0Labels := by
      have hz : ∀ j, raw41267 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41267step0 = (fun i j => raw41267 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41267step0 raw41267; decide +kernel
      have hl : raw41267step0Labels = raw41267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41267 raw41267Labels permutation434 hz
    mixedMoment B raw41267step0 raw41267step0Labels = mixedMoment B raw41267step1 raw41267step1Labels := by
      have ha : raw41267step1 = (fun i j => raw41267step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41267step1 raw41267step0; decide +kernel
      have hl : raw41267step1Labels = raw41267step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41267step0 raw41267step0Labels permutation151 permutation3
    mixedMoment B raw41267step1 raw41267step1Labels = mixedMoment B raw41267step2 raw41267step2Labels := by
      have ha : raw41267step2 = -raw41267step1 := by apply Matrix.ext; change ∀ i j, raw41267step2 i j = -(raw41267step1 i j); unfold raw41267step2 raw41267step1; decide +kernel
      have hl : raw41267step2Labels = raw41267step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4047 node4047Labels := by rfl

theorem canonical41268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41268 raw41268Labels = mixedMoment B node4008 node4008Labels := by
  calc
    mixedMoment B raw41268 raw41268Labels = mixedMoment B raw41268step0 raw41268step0Labels := by
      have ha : raw41268step0 = (fun i j => raw41268 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41268step0 raw41268; decide +kernel
      have hl : raw41268step0Labels = raw41268Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41268 raw41268Labels permutation664 permutation3
    mixedMoment B raw41268step0 raw41268step0Labels = mixedMoment B raw41268step1 raw41268step1Labels := by
      have ha : raw41268step1 = -raw41268step0 := by apply Matrix.ext; change ∀ i j, raw41268step1 i j = -(raw41268step0 i j); unfold raw41268step1 raw41268step0; decide +kernel
      have hl : raw41268step1Labels = raw41268step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4008 node4008Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1824 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1824) =
      Integer.Sparse.eval keyMomentRow1824 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1824).leftCharge (GramAssembly.key 1824).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4049) := by
    have ha : gramCharges (GramAssembly.key 1824).leftCharge (GramAssembly.key 1824).rightCharge = raw41237 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41237Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41237 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1824).leftCharge (GramAssembly.key 1824).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1824, Integer.Sparse.eval]

theorem keyMoment1825 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1825) =
      Integer.Sparse.eval keyMomentRow1825 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1825).leftCharge (GramAssembly.key 1825).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4010) := by
    have ha : gramCharges (GramAssembly.key 1825).leftCharge (GramAssembly.key 1825).rightCharge = raw41238 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41238Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41238 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1825).leftCharge (GramAssembly.key 1825).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1825, Integer.Sparse.eval]

theorem keyMoment1826 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1826) =
      Integer.Sparse.eval keyMomentRow1826 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1826).leftCharge (GramAssembly.key 1826).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3809) := by
    have ha : gramCharges (GramAssembly.key 1826).leftCharge (GramAssembly.key 1826).rightCharge = raw41239 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41239Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41239 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1826).leftCharge (GramAssembly.key 1826).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1826, Integer.Sparse.eval]

theorem keyMoment1827 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1827) =
      Integer.Sparse.eval keyMomentRow1827 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1827).leftCharge (GramAssembly.key 1827).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4047) := by
    have ha : gramCharges (GramAssembly.key 1827).leftCharge (GramAssembly.key 1827).rightCharge = raw41240 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41240Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41240 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1827).leftCharge (GramAssembly.key 1827).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1827, Integer.Sparse.eval]

theorem keyMoment1828 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1828) =
      Integer.Sparse.eval keyMomentRow1828 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1828).leftCharge (GramAssembly.key 1828).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4048) := by
    have ha : gramCharges (GramAssembly.key 1828).leftCharge (GramAssembly.key 1828).rightCharge = raw41241 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41241Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41241 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1828).leftCharge (GramAssembly.key 1828).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1828, Integer.Sparse.eval]

theorem keyMoment1829 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1829) =
      Integer.Sparse.eval keyMomentRow1829 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1829).leftCharge (GramAssembly.key 1829).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3903) := by
    have ha : gramCharges (GramAssembly.key 1829).leftCharge (GramAssembly.key 1829).rightCharge = raw41242 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41242Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41242 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1829).leftCharge (GramAssembly.key 1829).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1829, Integer.Sparse.eval]

theorem keyMoment1830 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1830) =
      Integer.Sparse.eval keyMomentRow1830 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1830).leftCharge (GramAssembly.key 1830).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4025) := by
    have ha : gramCharges (GramAssembly.key 1830).leftCharge (GramAssembly.key 1830).rightCharge = raw41243 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41243Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41243 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1830).leftCharge (GramAssembly.key 1830).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1830, Integer.Sparse.eval]

theorem keyMoment1831 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1831) =
      Integer.Sparse.eval keyMomentRow1831 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1831).leftCharge (GramAssembly.key 1831).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4046) := by
    have ha : gramCharges (GramAssembly.key 1831).leftCharge (GramAssembly.key 1831).rightCharge = raw41244 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41244Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41244 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1831).leftCharge (GramAssembly.key 1831).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1831, Integer.Sparse.eval]

theorem keyMoment1832 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1832) =
      Integer.Sparse.eval keyMomentRow1832 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1832).leftCharge (GramAssembly.key 1832).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2262) := by
    have ha : gramCharges (GramAssembly.key 1832).leftCharge (GramAssembly.key 1832).rightCharge = raw41245 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41245Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41245 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1832).leftCharge (GramAssembly.key 1832).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1832, Integer.Sparse.eval]

theorem keyMoment1833 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1833) =
      Integer.Sparse.eval keyMomentRow1833 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1833).leftCharge (GramAssembly.key 1833).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2720) := by
    have ha : gramCharges (GramAssembly.key 1833).leftCharge (GramAssembly.key 1833).rightCharge = raw41246 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41246Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41246 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1833).leftCharge (GramAssembly.key 1833).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1833, Integer.Sparse.eval]

theorem keyMoment1834 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1834) =
      Integer.Sparse.eval keyMomentRow1834 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1834).leftCharge (GramAssembly.key 1834).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3036) := by
    have ha : gramCharges (GramAssembly.key 1834).leftCharge (GramAssembly.key 1834).rightCharge = raw41247 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41247Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41247 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1834).leftCharge (GramAssembly.key 1834).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1834, Integer.Sparse.eval]

theorem keyMoment1835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1835) =
      Integer.Sparse.eval keyMomentRow1835 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1835).leftCharge (GramAssembly.key 1835).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3805) := by
    have ha : gramCharges (GramAssembly.key 1835).leftCharge (GramAssembly.key 1835).rightCharge = raw41248 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41248Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41248 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1835).leftCharge (GramAssembly.key 1835).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1835, Integer.Sparse.eval]

theorem keyMoment1836 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1836) =
      Integer.Sparse.eval keyMomentRow1836 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1836).leftCharge (GramAssembly.key 1836).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3956) := by
    have ha : gramCharges (GramAssembly.key 1836).leftCharge (GramAssembly.key 1836).rightCharge = raw41249 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41249Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41249 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1836).leftCharge (GramAssembly.key 1836).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1836, Integer.Sparse.eval]

theorem keyMoment1837 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1837) =
      Integer.Sparse.eval keyMomentRow1837 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1837).leftCharge (GramAssembly.key 1837).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3497) := by
    have ha : gramCharges (GramAssembly.key 1837).leftCharge (GramAssembly.key 1837).rightCharge = raw41250 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41250Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41250 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1837).leftCharge (GramAssembly.key 1837).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1837, Integer.Sparse.eval]

theorem keyMoment1838 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1838) =
      Integer.Sparse.eval keyMomentRow1838 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1838).leftCharge (GramAssembly.key 1838).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2879) := by
    have ha : gramCharges (GramAssembly.key 1838).leftCharge (GramAssembly.key 1838).rightCharge = raw41251 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41251Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41251 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1838).leftCharge (GramAssembly.key 1838).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1838, Integer.Sparse.eval]

theorem keyMoment1839 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1839) =
      Integer.Sparse.eval keyMomentRow1839 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1839).leftCharge (GramAssembly.key 1839).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2878) := by
    have ha : gramCharges (GramAssembly.key 1839).leftCharge (GramAssembly.key 1839).rightCharge = raw41252 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41252Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41252 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1839).leftCharge (GramAssembly.key 1839).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1839, Integer.Sparse.eval]

theorem keyMoment1840 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1840) =
      Integer.Sparse.eval keyMomentRow1840 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1840).leftCharge (GramAssembly.key 1840).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2861) := by
    have ha : gramCharges (GramAssembly.key 1840).leftCharge (GramAssembly.key 1840).rightCharge = raw41253 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41253Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41253 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1840).leftCharge (GramAssembly.key 1840).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1840, Integer.Sparse.eval]

theorem keyMoment1841 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1841) =
      Integer.Sparse.eval keyMomentRow1841 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1841).leftCharge (GramAssembly.key 1841).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2763) := by
    have ha : gramCharges (GramAssembly.key 1841).leftCharge (GramAssembly.key 1841).rightCharge = raw41254 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41254Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41254 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1841).leftCharge (GramAssembly.key 1841).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1841, Integer.Sparse.eval]

theorem keyMoment1842 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1842) =
      Integer.Sparse.eval keyMomentRow1842 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1842).leftCharge (GramAssembly.key 1842).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3084) := by
    have ha : gramCharges (GramAssembly.key 1842).leftCharge (GramAssembly.key 1842).rightCharge = raw41255 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41255Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41255 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1842).leftCharge (GramAssembly.key 1842).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1842, Integer.Sparse.eval]

theorem keyMoment1843 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1843) =
      Integer.Sparse.eval keyMomentRow1843 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1843).leftCharge (GramAssembly.key 1843).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3978) := by
    have ha : gramCharges (GramAssembly.key 1843).leftCharge (GramAssembly.key 1843).rightCharge = raw41256 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41256Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41256 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1843).leftCharge (GramAssembly.key 1843).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1843, Integer.Sparse.eval]

theorem keyMoment1844 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1844) =
      Integer.Sparse.eval keyMomentRow1844 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1844).leftCharge (GramAssembly.key 1844).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3946) := by
    have ha : gramCharges (GramAssembly.key 1844).leftCharge (GramAssembly.key 1844).rightCharge = raw41257 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41257Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41257 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1844).leftCharge (GramAssembly.key 1844).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1844, Integer.Sparse.eval]

theorem keyMoment1845 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1845) =
      Integer.Sparse.eval keyMomentRow1845 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1845).leftCharge (GramAssembly.key 1845).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2882) := by
    have ha : gramCharges (GramAssembly.key 1845).leftCharge (GramAssembly.key 1845).rightCharge = raw41258 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41258Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41258 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1845).leftCharge (GramAssembly.key 1845).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1845, Integer.Sparse.eval]

theorem keyMoment1846 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1846) =
      Integer.Sparse.eval keyMomentRow1846 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1846).leftCharge (GramAssembly.key 1846).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2862) := by
    have ha : gramCharges (GramAssembly.key 1846).leftCharge (GramAssembly.key 1846).rightCharge = raw41259 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41259Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41259 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1846).leftCharge (GramAssembly.key 1846).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1846, Integer.Sparse.eval]

theorem keyMoment1847 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1847) =
      Integer.Sparse.eval keyMomentRow1847 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1847).leftCharge (GramAssembly.key 1847).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2600) := by
    have ha : gramCharges (GramAssembly.key 1847).leftCharge (GramAssembly.key 1847).rightCharge = raw41260 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41260Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41260 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1847).leftCharge (GramAssembly.key 1847).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1847, Integer.Sparse.eval]

theorem keyMoment1848 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1848) =
      Integer.Sparse.eval keyMomentRow1848 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1848).leftCharge (GramAssembly.key 1848).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2557) := by
    have ha : gramCharges (GramAssembly.key 1848).leftCharge (GramAssembly.key 1848).rightCharge = raw41261 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41261Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41261 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1848).leftCharge (GramAssembly.key 1848).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1848, Integer.Sparse.eval]

theorem keyMoment1849 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1849) =
      Integer.Sparse.eval keyMomentRow1849 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1849).leftCharge (GramAssembly.key 1849).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2558) := by
    have ha : gramCharges (GramAssembly.key 1849).leftCharge (GramAssembly.key 1849).rightCharge = raw41262 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41262Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41262 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1849).leftCharge (GramAssembly.key 1849).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1849, Integer.Sparse.eval]

theorem keyMoment1850 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1850) =
      Integer.Sparse.eval keyMomentRow1850 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1850).leftCharge (GramAssembly.key 1850).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3903) := by
    have ha : gramCharges (GramAssembly.key 1850).leftCharge (GramAssembly.key 1850).rightCharge = raw41263 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41263Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41263 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1850).leftCharge (GramAssembly.key 1850).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1850, Integer.Sparse.eval]

theorem keyMoment1851 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1851) =
      Integer.Sparse.eval keyMomentRow1851 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1851).leftCharge (GramAssembly.key 1851).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3857) := by
    have ha : gramCharges (GramAssembly.key 1851).leftCharge (GramAssembly.key 1851).rightCharge = raw41264 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41264Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41264 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1851).leftCharge (GramAssembly.key 1851).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1851, Integer.Sparse.eval]

theorem keyMoment1852 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1852) =
      Integer.Sparse.eval keyMomentRow1852 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1852).leftCharge (GramAssembly.key 1852).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2058) := by
    have ha : gramCharges (GramAssembly.key 1852).leftCharge (GramAssembly.key 1852).rightCharge = raw41265 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41265Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41265 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1852).leftCharge (GramAssembly.key 1852).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1852, Integer.Sparse.eval]

theorem keyMoment1853 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1853) =
      Integer.Sparse.eval keyMomentRow1853 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1853).leftCharge (GramAssembly.key 1853).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3544) := by
    have ha : gramCharges (GramAssembly.key 1853).leftCharge (GramAssembly.key 1853).rightCharge = raw41266 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41266Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41266 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1853).leftCharge (GramAssembly.key 1853).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1853, Integer.Sparse.eval]

theorem keyMoment1854 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1854) =
      Integer.Sparse.eval keyMomentRow1854 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1854).leftCharge (GramAssembly.key 1854).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4047) := by
    have ha : gramCharges (GramAssembly.key 1854).leftCharge (GramAssembly.key 1854).rightCharge = raw41267 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41267Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41267 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1854).leftCharge (GramAssembly.key 1854).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1854, Integer.Sparse.eval]

theorem keyMoment1855 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1855) =
      Integer.Sparse.eval keyMomentRow1855 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1855).leftCharge (GramAssembly.key 1855).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4008) := by
    have ha : gramCharges (GramAssembly.key 1855).leftCharge (GramAssembly.key 1855).rightCharge = raw41268 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41268Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41268 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1855).leftCharge (GramAssembly.key 1855).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1855, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1824 : keyMomentRows (1824 : Fin 2886) =
    keyMomentRow1824 := by decide +kernel

theorem keyMomentRowsAt1825 : keyMomentRows (1825 : Fin 2886) =
    keyMomentRow1825 := by decide +kernel

theorem keyMomentRowsAt1826 : keyMomentRows (1826 : Fin 2886) =
    keyMomentRow1826 := by decide +kernel

theorem keyMomentRowsAt1827 : keyMomentRows (1827 : Fin 2886) =
    keyMomentRow1827 := by decide +kernel

theorem keyMomentRowsAt1828 : keyMomentRows (1828 : Fin 2886) =
    keyMomentRow1828 := by decide +kernel

theorem keyMomentRowsAt1829 : keyMomentRows (1829 : Fin 2886) =
    keyMomentRow1829 := by decide +kernel

theorem keyMomentRowsAt1830 : keyMomentRows (1830 : Fin 2886) =
    keyMomentRow1830 := by decide +kernel

theorem keyMomentRowsAt1831 : keyMomentRows (1831 : Fin 2886) =
    keyMomentRow1831 := by decide +kernel

theorem keyMomentRowsAt1832 : keyMomentRows (1832 : Fin 2886) =
    keyMomentRow1832 := by decide +kernel

theorem keyMomentRowsAt1833 : keyMomentRows (1833 : Fin 2886) =
    keyMomentRow1833 := by decide +kernel

theorem keyMomentRowsAt1834 : keyMomentRows (1834 : Fin 2886) =
    keyMomentRow1834 := by decide +kernel

theorem keyMomentRowsAt1835 : keyMomentRows (1835 : Fin 2886) =
    keyMomentRow1835 := by decide +kernel

theorem keyMomentRowsAt1836 : keyMomentRows (1836 : Fin 2886) =
    keyMomentRow1836 := by decide +kernel

theorem keyMomentRowsAt1837 : keyMomentRows (1837 : Fin 2886) =
    keyMomentRow1837 := by decide +kernel

theorem keyMomentRowsAt1838 : keyMomentRows (1838 : Fin 2886) =
    keyMomentRow1838 := by decide +kernel

theorem keyMomentRowsAt1839 : keyMomentRows (1839 : Fin 2886) =
    keyMomentRow1839 := by decide +kernel

theorem keyMomentRowsAt1840 : keyMomentRows (1840 : Fin 2886) =
    keyMomentRow1840 := by decide +kernel

theorem keyMomentRowsAt1841 : keyMomentRows (1841 : Fin 2886) =
    keyMomentRow1841 := by decide +kernel

theorem keyMomentRowsAt1842 : keyMomentRows (1842 : Fin 2886) =
    keyMomentRow1842 := by decide +kernel

theorem keyMomentRowsAt1843 : keyMomentRows (1843 : Fin 2886) =
    keyMomentRow1843 := by decide +kernel

theorem keyMomentRowsAt1844 : keyMomentRows (1844 : Fin 2886) =
    keyMomentRow1844 := by decide +kernel

theorem keyMomentRowsAt1845 : keyMomentRows (1845 : Fin 2886) =
    keyMomentRow1845 := by decide +kernel

theorem keyMomentRowsAt1846 : keyMomentRows (1846 : Fin 2886) =
    keyMomentRow1846 := by decide +kernel

theorem keyMomentRowsAt1847 : keyMomentRows (1847 : Fin 2886) =
    keyMomentRow1847 := by decide +kernel

theorem keyMomentRowsAt1848 : keyMomentRows (1848 : Fin 2886) =
    keyMomentRow1848 := by decide +kernel

theorem keyMomentRowsAt1849 : keyMomentRows (1849 : Fin 2886) =
    keyMomentRow1849 := by decide +kernel

theorem keyMomentRowsAt1850 : keyMomentRows (1850 : Fin 2886) =
    keyMomentRow1850 := by decide +kernel

theorem keyMomentRowsAt1851 : keyMomentRows (1851 : Fin 2886) =
    keyMomentRow1851 := by decide +kernel

theorem keyMomentRowsAt1852 : keyMomentRows (1852 : Fin 2886) =
    keyMomentRow1852 := by decide +kernel

theorem keyMomentRowsAt1853 : keyMomentRows (1853 : Fin 2886) =
    keyMomentRow1853 := by decide +kernel

theorem keyMomentRowsAt1854 : keyMomentRows (1854 : Fin 2886) =
    keyMomentRow1854 := by decide +kernel

theorem keyMomentRowsAt1855 : keyMomentRows (1855 : Fin 2886) =
    keyMomentRow1855 := by decide +kernel

theorem keyMomentChunkSound57_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 57) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1824 ∨ k.val = 1825 ∨ k.val = 1826 ∨ k.val = 1827 ∨ k.val = 1828 ∨ k.val = 1829 ∨ k.val = 1830 ∨ k.val = 1831 ∨ k.val = 1832 ∨ k.val = 1833 ∨ k.val = 1834 ∨ k.val = 1835 ∨ k.val = 1836 ∨ k.val = 1837 ∨ k.val = 1838 ∨ k.val = 1839 ∨ k.val = 1840 ∨ k.val = 1841 ∨ k.val = 1842 ∨ k.val = 1843 ∨ k.val = 1844 ∨ k.val = 1845 ∨ k.val = 1846 ∨ k.val = 1847 ∨ k.val = 1848 ∨ k.val = 1849 ∨ k.val = 1850 ∨ k.val = 1851 ∨ k.val = 1852 ∨ k.val = 1853 ∨ k.val = 1854 ∨ k.val = 1855 := by omega
  rcases heq with h1824 | h1825 | h1826 | h1827 | h1828 | h1829 | h1830 | h1831 | h1832 | h1833 | h1834 | h1835 | h1836 | h1837 | h1838 | h1839 | h1840 | h1841 | h1842 | h1843 | h1844 | h1845 | h1846 | h1847 | h1848 | h1849 | h1850 | h1851 | h1852 | h1853 | h1854 | h1855
  · have he : k = (1824 : Fin 2886) := Fin.ext h1824
    subst k
    rw [keyMomentRowsAt1824]
    exact keyMoment1824 B hB
  · have he : k = (1825 : Fin 2886) := Fin.ext h1825
    subst k
    rw [keyMomentRowsAt1825]
    exact keyMoment1825 B hB
  · have he : k = (1826 : Fin 2886) := Fin.ext h1826
    subst k
    rw [keyMomentRowsAt1826]
    exact keyMoment1826 B hB
  · have he : k = (1827 : Fin 2886) := Fin.ext h1827
    subst k
    rw [keyMomentRowsAt1827]
    exact keyMoment1827 B hB
  · have he : k = (1828 : Fin 2886) := Fin.ext h1828
    subst k
    rw [keyMomentRowsAt1828]
    exact keyMoment1828 B hB
  · have he : k = (1829 : Fin 2886) := Fin.ext h1829
    subst k
    rw [keyMomentRowsAt1829]
    exact keyMoment1829 B hB
  · have he : k = (1830 : Fin 2886) := Fin.ext h1830
    subst k
    rw [keyMomentRowsAt1830]
    exact keyMoment1830 B hB
  · have he : k = (1831 : Fin 2886) := Fin.ext h1831
    subst k
    rw [keyMomentRowsAt1831]
    exact keyMoment1831 B hB
  · have he : k = (1832 : Fin 2886) := Fin.ext h1832
    subst k
    rw [keyMomentRowsAt1832]
    exact keyMoment1832 B hB
  · have he : k = (1833 : Fin 2886) := Fin.ext h1833
    subst k
    rw [keyMomentRowsAt1833]
    exact keyMoment1833 B hB
  · have he : k = (1834 : Fin 2886) := Fin.ext h1834
    subst k
    rw [keyMomentRowsAt1834]
    exact keyMoment1834 B hB
  · have he : k = (1835 : Fin 2886) := Fin.ext h1835
    subst k
    rw [keyMomentRowsAt1835]
    exact keyMoment1835 B hB
  · have he : k = (1836 : Fin 2886) := Fin.ext h1836
    subst k
    rw [keyMomentRowsAt1836]
    exact keyMoment1836 B hB
  · have he : k = (1837 : Fin 2886) := Fin.ext h1837
    subst k
    rw [keyMomentRowsAt1837]
    exact keyMoment1837 B hB
  · have he : k = (1838 : Fin 2886) := Fin.ext h1838
    subst k
    rw [keyMomentRowsAt1838]
    exact keyMoment1838 B hB
  · have he : k = (1839 : Fin 2886) := Fin.ext h1839
    subst k
    rw [keyMomentRowsAt1839]
    exact keyMoment1839 B hB
  · have he : k = (1840 : Fin 2886) := Fin.ext h1840
    subst k
    rw [keyMomentRowsAt1840]
    exact keyMoment1840 B hB
  · have he : k = (1841 : Fin 2886) := Fin.ext h1841
    subst k
    rw [keyMomentRowsAt1841]
    exact keyMoment1841 B hB
  · have he : k = (1842 : Fin 2886) := Fin.ext h1842
    subst k
    rw [keyMomentRowsAt1842]
    exact keyMoment1842 B hB
  · have he : k = (1843 : Fin 2886) := Fin.ext h1843
    subst k
    rw [keyMomentRowsAt1843]
    exact keyMoment1843 B hB
  · have he : k = (1844 : Fin 2886) := Fin.ext h1844
    subst k
    rw [keyMomentRowsAt1844]
    exact keyMoment1844 B hB
  · have he : k = (1845 : Fin 2886) := Fin.ext h1845
    subst k
    rw [keyMomentRowsAt1845]
    exact keyMoment1845 B hB
  · have he : k = (1846 : Fin 2886) := Fin.ext h1846
    subst k
    rw [keyMomentRowsAt1846]
    exact keyMoment1846 B hB
  · have he : k = (1847 : Fin 2886) := Fin.ext h1847
    subst k
    rw [keyMomentRowsAt1847]
    exact keyMoment1847 B hB
  · have he : k = (1848 : Fin 2886) := Fin.ext h1848
    subst k
    rw [keyMomentRowsAt1848]
    exact keyMoment1848 B hB
  · have he : k = (1849 : Fin 2886) := Fin.ext h1849
    subst k
    rw [keyMomentRowsAt1849]
    exact keyMoment1849 B hB
  · have he : k = (1850 : Fin 2886) := Fin.ext h1850
    subst k
    rw [keyMomentRowsAt1850]
    exact keyMoment1850 B hB
  · have he : k = (1851 : Fin 2886) := Fin.ext h1851
    subst k
    rw [keyMomentRowsAt1851]
    exact keyMoment1851 B hB
  · have he : k = (1852 : Fin 2886) := Fin.ext h1852
    subst k
    rw [keyMomentRowsAt1852]
    exact keyMoment1852 B hB
  · have he : k = (1853 : Fin 2886) := Fin.ext h1853
    subst k
    rw [keyMomentRowsAt1853]
    exact keyMoment1853 B hB
  · have he : k = (1854 : Fin 2886) := Fin.ext h1854
    subst k
    rw [keyMomentRowsAt1854]
    exact keyMoment1854 B hB
  · have he : k = (1855 : Fin 2886) := Fin.ext h1855
    subst k
    rw [keyMomentRowsAt1855]
    exact keyMoment1855 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound57_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound57_e_oai
