-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound26_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:50:02.52972+00:00
-- url     : https://prove2.me/submissions/4b01459a-0538-4e21-b9c1-153a82b3a58f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E111
import Definitions.Def_OAIQ106E116
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2929 raw2929Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2929 raw2929Labels = mixedMoment B raw2929step0 raw2929step0Labels := by
      have hz : ∀ j, raw2929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2929step0 = (fun i j => raw2929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2929step0 raw2929; decide +kernel
      have hl : raw2929step0Labels = raw2929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929 raw2929Labels permutation434 hz
    mixedMoment B raw2929step0 raw2929step0Labels = mixedMoment B raw2929step1 raw2929step1Labels := by
      have hz : ∀ j, raw2929step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2929step1 = (fun i j => raw2929step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2929step1 raw2929step0; decide +kernel
      have hl : raw2929step1Labels = raw2929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929step0 raw2929step0Labels permutation80 hz
    mixedMoment B raw2929step1 raw2929step1Labels = mixedMoment B raw2929step2 raw2929step2Labels := by
      have hz : ∀ j, raw2929step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2929step2 = (fun i j => raw2929step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2929step2 raw2929step1; decide +kernel
      have hl : raw2929step2Labels = raw2929step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929step1 raw2929step1Labels permutation14 hz
    mixedMoment B raw2929step2 raw2929step2Labels = mixedMoment B raw2929step3 raw2929step3Labels := by
      have hz : ∀ i, raw2929step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2929step3 = (fun i j => raw2929step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2929step3 raw2929step2; decide +kernel
      have hl : raw2929step3Labels = (fun j => raw2929step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2929step2 raw2929step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2934 raw2934Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw2934 raw2934Labels = mixedMoment B raw2934step0 raw2934step0Labels := by
      have hz : ∀ j, raw2934 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2934step0 = (fun i j => raw2934 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2934step0 raw2934; decide +kernel
      have hl : raw2934step0Labels = raw2934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934 raw2934Labels permutation520 hz
    mixedMoment B raw2934step0 raw2934step0Labels = mixedMoment B raw2934step1 raw2934step1Labels := by
      have hz : ∀ j, raw2934step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2934step1 = (fun i j => raw2934step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2934step1 raw2934step0; decide +kernel
      have hl : raw2934step1Labels = raw2934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step0 raw2934step0Labels permutation104 hz
    mixedMoment B raw2934step1 raw2934step1Labels = mixedMoment B raw2934step2 raw2934step2Labels := by
      have hz : ∀ j, raw2934step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2934step2 = (fun i j => raw2934step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2934step2 raw2934step1; decide +kernel
      have hl : raw2934step2Labels = raw2934step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step1 raw2934step1Labels permutation20 hz
    mixedMoment B raw2934step2 raw2934step2Labels = mixedMoment B raw2934step3 raw2934step3Labels := by
      have hz : ∀ j, raw2934step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw2934step3 = (fun i j => raw2934step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw2934step3 raw2934step2; decide +kernel
      have hl : raw2934step3Labels = raw2934step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step2 raw2934step2Labels permutation4 hz
    mixedMoment B raw2934step3 raw2934step3Labels = mixedMoment B raw2934step4 raw2934step4Labels := by
      have hz : ∀ i, raw2934step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2934step4 = (fun i j => raw2934step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2934step4 raw2934step3; decide +kernel
      have hl : raw2934step4Labels = (fun j => raw2934step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2934step3 raw2934step3Labels permutation6 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3331 raw3331Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3331 raw3331Labels = mixedMoment B raw3331step0 raw3331step0Labels := by
      have hz : ∀ j, raw3331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3331step0 = (fun i j => raw3331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3331step0 raw3331; decide +kernel
      have hl : raw3331step0Labels = raw3331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3331 raw3331Labels permutation346 hz
    mixedMoment B raw3331step0 raw3331step0Labels = mixedMoment B raw3331step1 raw3331step1Labels := by
      have hz : ∀ j, raw3331step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3331step1 = (fun i j => raw3331step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3331step1 raw3331step0; decide +kernel
      have hl : raw3331step1Labels = raw3331step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3331step0 raw3331step0Labels permutation56 hz
    mixedMoment B raw3331step1 raw3331step1Labels = mixedMoment B raw3331step2 raw3331step2Labels := by
      have hz : ∀ i, raw3331step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3331step2 = (fun i j => raw3331step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3331step2 raw3331step1; decide +kernel
      have hl : raw3331step2Labels = (fun j => raw3331step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3331step1 raw3331step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical314
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40279 raw40279Labels = mixedMoment B node34 node34Labels := by
  calc
    mixedMoment B raw40279 raw40279Labels = mixedMoment B raw40279step0 raw40279step0Labels := by
      have hz : ∀ j, raw40279 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40279step0 = (fun i j => raw40279 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40279step0 raw40279; decide +kernel
      have hl : raw40279step0Labels = raw40279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40279 raw40279Labels permutation434 hz
    mixedMoment B raw40279step0 raw40279step0Labels = mixedMoment B raw40279step1 raw40279step1Labels := by
      have hz : ∀ j, raw40279step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40279step1 = (fun i j => raw40279step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40279step1 raw40279step0; decide +kernel
      have hl : raw40279step1Labels = raw40279step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40279step0 raw40279step0Labels permutation80 hz
    mixedMoment B raw40279step1 raw40279step1Labels = mixedMoment B raw40279step2 raw40279step2Labels := by
      have ha : raw40279step2 = (fun i j => raw40279step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40279step2 raw40279step1; decide +kernel
      have hl : raw40279step2Labels = raw40279step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40279step1 raw40279step1Labels permutation30 permutation6
    _ = mixedMoment B node34 node34Labels := by rfl

theorem canonical40280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40280 raw40280Labels = mixedMoment B node99 node99Labels := by
  calc
    mixedMoment B raw40280 raw40280Labels = mixedMoment B raw40280step0 raw40280step0Labels := by
      have hz : ∀ j, raw40280 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40280step0 = (fun i j => raw40280 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40280step0 raw40280; decide +kernel
      have hl : raw40280step0Labels = raw40280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40280 raw40280Labels permutation434 hz
    mixedMoment B raw40280step0 raw40280step0Labels = mixedMoment B raw40280step1 raw40280step1Labels := by
      have hz : ∀ j, raw40280step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40280step1 = (fun i j => raw40280step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40280step1 raw40280step0; decide +kernel
      have hl : raw40280step1Labels = raw40280step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40280step0 raw40280step0Labels permutation80 hz
    mixedMoment B raw40280step1 raw40280step1Labels = mixedMoment B raw40280step2 raw40280step2Labels := by
      have ha : raw40280step2 = (fun i j => raw40280step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40280step2 raw40280step1; decide +kernel
      have hl : raw40280step2Labels = raw40280step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40280step1 raw40280step1Labels permutation24 permutation6
    _ = mixedMoment B node99 node99Labels := by rfl

theorem canonical40281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40281 raw40281Labels = mixedMoment B node510 node510Labels := by
  calc
    mixedMoment B raw40281 raw40281Labels = mixedMoment B raw40281step0 raw40281step0Labels := by
      have hz : ∀ j, raw40281 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40281step0 = (fun i j => raw40281 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40281step0 raw40281; decide +kernel
      have hl : raw40281step0Labels = raw40281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40281 raw40281Labels permutation434 hz
    mixedMoment B raw40281step0 raw40281step0Labels = mixedMoment B raw40281step1 raw40281step1Labels := by
      have hz : ∀ j, raw40281step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40281step1 = (fun i j => raw40281step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40281step1 raw40281step0; decide +kernel
      have hl : raw40281step1Labels = raw40281step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40281step0 raw40281step0Labels permutation80 hz
    mixedMoment B raw40281step1 raw40281step1Labels = mixedMoment B raw40281step2 raw40281step2Labels := by
      have ha : raw40281step2 = (fun i j => raw40281step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40281step2 raw40281step1; decide +kernel
      have hl : raw40281step2Labels = raw40281step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40281step1 raw40281step1Labels permutation24 permutation6
    _ = mixedMoment B node510 node510Labels := by rfl

theorem canonical40282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40282 raw40282Labels = mixedMoment B node69 node69Labels := by
  calc
    mixedMoment B raw40282 raw40282Labels = mixedMoment B raw40282step0 raw40282step0Labels := by
      have hz : ∀ j, raw40282 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40282step0 = (fun i j => raw40282 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40282step0 raw40282; decide +kernel
      have hl : raw40282step0Labels = raw40282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40282 raw40282Labels permutation346 hz
    mixedMoment B raw40282step0 raw40282step0Labels = mixedMoment B raw40282step1 raw40282step1Labels := by
      have ha : raw40282step1 = (fun i j => raw40282step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40282step1 raw40282step0; decide +kernel
      have hl : raw40282step1Labels = raw40282step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40282step0 raw40282step0Labels permutation126 permutation6
    _ = mixedMoment B node69 node69Labels := by rfl

theorem canonical40283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40283 raw40283Labels = mixedMoment B node186 node186Labels := by
  calc
    mixedMoment B raw40283 raw40283Labels = mixedMoment B raw40283step0 raw40283step0Labels := by
      have hz : ∀ j, raw40283 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40283step0 = (fun i j => raw40283 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40283step0 raw40283; decide +kernel
      have hl : raw40283step0Labels = raw40283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40283 raw40283Labels permutation520 hz
    mixedMoment B raw40283step0 raw40283step0Labels = mixedMoment B raw40283step1 raw40283step1Labels := by
      have hz : ∀ j, raw40283step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40283step1 = (fun i j => raw40283step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40283step1 raw40283step0; decide +kernel
      have hl : raw40283step1Labels = raw40283step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40283step0 raw40283step0Labels permutation104 hz
    mixedMoment B raw40283step1 raw40283step1Labels = mixedMoment B raw40283step2 raw40283step2Labels := by
      have ha : raw40283step2 = (fun i j => raw40283step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40283step2 raw40283step1; decide +kernel
      have hl : raw40283step2Labels = raw40283step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40283step1 raw40283step1Labels permutation24 permutation6
    _ = mixedMoment B node186 node186Labels := by rfl

theorem canonical40284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40284 raw40284Labels = mixedMoment B node275 node275Labels := by
  calc
    mixedMoment B raw40284 raw40284Labels = mixedMoment B raw40284step0 raw40284step0Labels := by
      have hz : ∀ j, raw40284 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40284step0 = (fun i j => raw40284 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40284step0 raw40284; decide +kernel
      have hl : raw40284step0Labels = raw40284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40284 raw40284Labels permutation520 hz
    mixedMoment B raw40284step0 raw40284step0Labels = mixedMoment B raw40284step1 raw40284step1Labels := by
      have ha : raw40284step1 = (fun i j => raw40284step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40284step1 raw40284step0; decide +kernel
      have hl : raw40284step1Labels = raw40284step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40284step0 raw40284step0Labels permutation59 permutation6
    mixedMoment B raw40284step1 raw40284step1Labels = mixedMoment B raw40284step2 raw40284step2Labels := by
      have ha : raw40284step2 = -raw40284step1 := by apply Matrix.ext; change ∀ i j, raw40284step2 i j = -(raw40284step1 i j); unfold raw40284step2 raw40284step1; decide +kernel
      have hl : raw40284step2Labels = raw40284step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node275 node275Labels := by rfl

theorem canonical40285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40285 raw40285Labels = mixedMoment B node277 node277Labels := by
  calc
    mixedMoment B raw40285 raw40285Labels = mixedMoment B raw40285step0 raw40285step0Labels := by
      have hz : ∀ j, raw40285 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40285step0 = (fun i j => raw40285 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40285step0 raw40285; decide +kernel
      have hl : raw40285step0Labels = raw40285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40285 raw40285Labels permutation520 hz
    mixedMoment B raw40285step0 raw40285step0Labels = mixedMoment B raw40285step1 raw40285step1Labels := by
      have hz : ∀ j, raw40285step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40285step1 = (fun i j => raw40285step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40285step1 raw40285step0; decide +kernel
      have hl : raw40285step1Labels = raw40285step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40285step0 raw40285step0Labels permutation104 hz
    mixedMoment B raw40285step1 raw40285step1Labels = mixedMoment B raw40285step2 raw40285step2Labels := by
      have ha : raw40285step2 = (fun i j => raw40285step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40285step2 raw40285step1; decide +kernel
      have hl : raw40285step2Labels = raw40285step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40285step1 raw40285step1Labels permutation14 permutation6
    mixedMoment B raw40285step2 raw40285step2Labels = mixedMoment B raw40285step3 raw40285step3Labels := by
      have ha : raw40285step3 = -raw40285step2 := by apply Matrix.ext; change ∀ i j, raw40285step3 i j = -(raw40285step2 i j); unfold raw40285step3 raw40285step2; decide +kernel
      have hl : raw40285step3Labels = raw40285step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node277 node277Labels := by rfl

theorem canonical40286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40286 raw40286Labels = mixedMoment B node39 node39Labels := by
  calc
    mixedMoment B raw40286 raw40286Labels = mixedMoment B raw40286step0 raw40286step0Labels := by
      have hz : ∀ j, raw40286 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40286step0 = (fun i j => raw40286 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40286step0 raw40286; decide +kernel
      have hl : raw40286step0Labels = raw40286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40286 raw40286Labels permutation520 hz
    mixedMoment B raw40286step0 raw40286step0Labels = mixedMoment B raw40286step1 raw40286step1Labels := by
      have hz : ∀ j, raw40286step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40286step1 = (fun i j => raw40286step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40286step1 raw40286step0; decide +kernel
      have hl : raw40286step1Labels = raw40286step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40286step0 raw40286step0Labels permutation104 hz
    mixedMoment B raw40286step1 raw40286step1Labels = mixedMoment B raw40286step2 raw40286step2Labels := by
      have hz : ∀ j, raw40286step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40286step2 = (fun i j => raw40286step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40286step2 raw40286step1; decide +kernel
      have hl : raw40286step2Labels = raw40286step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40286step1 raw40286step1Labels permutation20 hz
    mixedMoment B raw40286step2 raw40286step2Labels = mixedMoment B raw40286step3 raw40286step3Labels := by
      have ha : raw40286step3 = (fun i j => raw40286step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40286step3 raw40286step2; decide +kernel
      have hl : raw40286step3Labels = raw40286step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40286step2 raw40286step2Labels permutation6 permutation6
    _ = mixedMoment B node39 node39Labels := by rfl

theorem canonical40287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40287 raw40287Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw40287 raw40287Labels = mixedMoment B raw40287step0 raw40287step0Labels := by
      have hz : ∀ j, raw40287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40287step0 = (fun i j => raw40287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40287step0 raw40287; decide +kernel
      have hl : raw40287step0Labels = raw40287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40287 raw40287Labels permutation434 hz
    mixedMoment B raw40287step0 raw40287step0Labels = mixedMoment B raw40287step1 raw40287step1Labels := by
      have hz : ∀ j, raw40287step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40287step1 = (fun i j => raw40287step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40287step1 raw40287step0; decide +kernel
      have hl : raw40287step1Labels = raw40287step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40287step0 raw40287step0Labels permutation80 hz
    mixedMoment B raw40287step1 raw40287step1Labels = mixedMoment B raw40287step2 raw40287step2Labels := by
      have hz : ∀ j, raw40287step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40287step2 = (fun i j => raw40287step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40287step2 raw40287step1; decide +kernel
      have hl : raw40287step2Labels = raw40287step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40287step1 raw40287step1Labels permutation14 hz
    mixedMoment B raw40287step2 raw40287step2Labels = mixedMoment B raw40287step3 raw40287step3Labels := by
      have ha : raw40287step3 = (fun i j => raw40287step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40287step3 raw40287step2; decide +kernel
      have hl : raw40287step3Labels = raw40287step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40287step2 raw40287step2Labels permutation2 permutation3
    _ = mixedMoment B node2268 node2268Labels := by rfl

theorem canonical40288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40288 raw40288Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw40288 raw40288Labels = mixedMoment B raw40288step0 raw40288step0Labels := by
      have hz : ∀ j, raw40288 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40288step0 = (fun i j => raw40288 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40288step0 raw40288; decide +kernel
      have hl : raw40288step0Labels = raw40288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40288 raw40288Labels permutation434 hz
    mixedMoment B raw40288step0 raw40288step0Labels = mixedMoment B raw40288step1 raw40288step1Labels := by
      have hz : ∀ j, raw40288step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40288step1 = (fun i j => raw40288step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40288step1 raw40288step0; decide +kernel
      have hl : raw40288step1Labels = raw40288step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40288step0 raw40288step0Labels permutation80 hz
    mixedMoment B raw40288step1 raw40288step1Labels = mixedMoment B raw40288step2 raw40288step2Labels := by
      have hz : ∀ j, raw40288step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40288step2 = (fun i j => raw40288step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40288step2 raw40288step1; decide +kernel
      have hl : raw40288step2Labels = raw40288step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40288step1 raw40288step1Labels permutation14 hz
    mixedMoment B raw40288step2 raw40288step2Labels = mixedMoment B raw40288step3 raw40288step3Labels := by
      have ha : raw40288step3 = (fun i j => raw40288step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40288step3 raw40288step2; decide +kernel
      have hl : raw40288step3Labels = raw40288step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40288step2 raw40288step2Labels permutation2 permutation3
    _ = mixedMoment B node2281 node2281Labels := by rfl

theorem canonical40289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40289 raw40289Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw40289 raw40289Labels = mixedMoment B raw40289step0 raw40289step0Labels := by
      have hz : ∀ j, raw40289 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40289step0 = (fun i j => raw40289 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40289step0 raw40289; decide +kernel
      have hl : raw40289step0Labels = raw40289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40289 raw40289Labels permutation434 hz
    mixedMoment B raw40289step0 raw40289step0Labels = mixedMoment B raw40289step1 raw40289step1Labels := by
      have hz : ∀ j, raw40289step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40289step1 = (fun i j => raw40289step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40289step1 raw40289step0; decide +kernel
      have hl : raw40289step1Labels = raw40289step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40289step0 raw40289step0Labels permutation80 hz
    mixedMoment B raw40289step1 raw40289step1Labels = mixedMoment B raw40289step2 raw40289step2Labels := by
      have hz : ∀ j, raw40289step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40289step2 = (fun i j => raw40289step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40289step2 raw40289step1; decide +kernel
      have hl : raw40289step2Labels = raw40289step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40289step1 raw40289step1Labels permutation14 hz
    mixedMoment B raw40289step2 raw40289step2Labels = mixedMoment B raw40289step3 raw40289step3Labels := by
      have ha : raw40289step3 = (fun i j => raw40289step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40289step3 raw40289step2; decide +kernel
      have hl : raw40289step3Labels = raw40289step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40289step2 raw40289step2Labels permutation2 permutation3
    _ = mixedMoment B node2293 node2293Labels := by rfl

theorem canonical40290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40290 raw40290Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw40290 raw40290Labels = mixedMoment B raw40290step0 raw40290step0Labels := by
      have hz : ∀ j, raw40290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40290step0 = (fun i j => raw40290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40290step0 raw40290; decide +kernel
      have hl : raw40290step0Labels = raw40290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40290 raw40290Labels permutation434 hz
    mixedMoment B raw40290step0 raw40290step0Labels = mixedMoment B raw40290step1 raw40290step1Labels := by
      have hz : ∀ j, raw40290step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40290step1 = (fun i j => raw40290step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40290step1 raw40290step0; decide +kernel
      have hl : raw40290step1Labels = raw40290step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40290step0 raw40290step0Labels permutation80 hz
    mixedMoment B raw40290step1 raw40290step1Labels = mixedMoment B raw40290step2 raw40290step2Labels := by
      have hz : ∀ j, raw40290step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40290step2 = (fun i j => raw40290step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40290step2 raw40290step1; decide +kernel
      have hl : raw40290step2Labels = raw40290step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40290step1 raw40290step1Labels permutation14 hz
    mixedMoment B raw40290step2 raw40290step2Labels = mixedMoment B raw40290step3 raw40290step3Labels := by
      have ha : raw40290step3 = (fun i j => raw40290step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40290step3 raw40290step2; decide +kernel
      have hl : raw40290step3Labels = raw40290step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40290step2 raw40290step2Labels permutation2 permutation3
    _ = mixedMoment B node2294 node2294Labels := by rfl

theorem canonical40291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40291 raw40291Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw40291 raw40291Labels = mixedMoment B raw40291step0 raw40291step0Labels := by
      have hz : ∀ j, raw40291 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40291step0 = (fun i j => raw40291 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40291step0 raw40291; decide +kernel
      have hl : raw40291step0Labels = raw40291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40291 raw40291Labels permutation346 hz
    mixedMoment B raw40291step0 raw40291step0Labels = mixedMoment B raw40291step1 raw40291step1Labels := by
      have hz : ∀ j, raw40291step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40291step1 = (fun i j => raw40291step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40291step1 raw40291step0; decide +kernel
      have hl : raw40291step1Labels = raw40291step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40291step0 raw40291step0Labels permutation56 hz
    mixedMoment B raw40291step1 raw40291step1Labels = mixedMoment B raw40291step2 raw40291step2Labels := by
      have ha : raw40291step2 = (fun i j => raw40291step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40291step2 raw40291step1; decide +kernel
      have hl : raw40291step2Labels = raw40291step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40291step1 raw40291step1Labels permutation8 permutation3
    _ = mixedMoment B node2247 node2247Labels := by rfl

theorem canonical40292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40292 raw40292Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw40292 raw40292Labels = mixedMoment B raw40292step0 raw40292step0Labels := by
      have hz : ∀ j, raw40292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40292step0 = (fun i j => raw40292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40292step0 raw40292; decide +kernel
      have hl : raw40292step0Labels = raw40292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40292 raw40292Labels permutation346 hz
    mixedMoment B raw40292step0 raw40292step0Labels = mixedMoment B raw40292step1 raw40292step1Labels := by
      have hz : ∀ j, raw40292step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40292step1 = (fun i j => raw40292step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40292step1 raw40292step0; decide +kernel
      have hl : raw40292step1Labels = raw40292step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40292step0 raw40292step0Labels permutation56 hz
    mixedMoment B raw40292step1 raw40292step1Labels = mixedMoment B raw40292step2 raw40292step2Labels := by
      have ha : raw40292step2 = (fun i j => raw40292step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40292step2 raw40292step1; decide +kernel
      have hl : raw40292step2Labels = raw40292step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40292step1 raw40292step1Labels permutation8 permutation3
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical40293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40293 raw40293Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw40293 raw40293Labels = mixedMoment B raw40293step0 raw40293step0Labels := by
      have hz : ∀ j, raw40293 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40293step0 = (fun i j => raw40293 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40293step0 raw40293; decide +kernel
      have hl : raw40293step0Labels = raw40293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40293 raw40293Labels permutation346 hz
    mixedMoment B raw40293step0 raw40293step0Labels = mixedMoment B raw40293step1 raw40293step1Labels := by
      have hz : ∀ j, raw40293step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40293step1 = (fun i j => raw40293step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40293step1 raw40293step0; decide +kernel
      have hl : raw40293step1Labels = raw40293step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40293step0 raw40293step0Labels permutation56 hz
    mixedMoment B raw40293step1 raw40293step1Labels = mixedMoment B raw40293step2 raw40293step2Labels := by
      have ha : raw40293step2 = (fun i j => raw40293step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40293step2 raw40293step1; decide +kernel
      have hl : raw40293step2Labels = raw40293step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40293step1 raw40293step1Labels permutation8 permutation3
    _ = mixedMoment B node2265 node2265Labels := by rfl

theorem canonical40294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40294 raw40294Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw40294 raw40294Labels = mixedMoment B raw40294step0 raw40294step0Labels := by
      have hz : ∀ j, raw40294 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40294step0 = (fun i j => raw40294 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40294step0 raw40294; decide +kernel
      have hl : raw40294step0Labels = raw40294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40294 raw40294Labels permutation346 hz
    mixedMoment B raw40294step0 raw40294step0Labels = mixedMoment B raw40294step1 raw40294step1Labels := by
      have hz : ∀ j, raw40294step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40294step1 = (fun i j => raw40294step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40294step1 raw40294step0; decide +kernel
      have hl : raw40294step1Labels = raw40294step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40294step0 raw40294step0Labels permutation56 hz
    mixedMoment B raw40294step1 raw40294step1Labels = mixedMoment B raw40294step2 raw40294step2Labels := by
      have ha : raw40294step2 = (fun i j => raw40294step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40294step2 raw40294step1; decide +kernel
      have hl : raw40294step2Labels = raw40294step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40294step1 raw40294step1Labels permutation8 permutation3
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical40295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40295 raw40295Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw40295 raw40295Labels = mixedMoment B raw40295step0 raw40295step0Labels := by
      have hz : ∀ j, raw40295 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40295step0 = (fun i j => raw40295 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40295step0 raw40295; decide +kernel
      have hl : raw40295step0Labels = raw40295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40295 raw40295Labels permutation346 hz
    mixedMoment B raw40295step0 raw40295step0Labels = mixedMoment B raw40295step1 raw40295step1Labels := by
      have hz : ∀ j, raw40295step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40295step1 = (fun i j => raw40295step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40295step1 raw40295step0; decide +kernel
      have hl : raw40295step1Labels = raw40295step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40295step0 raw40295step0Labels permutation56 hz
    mixedMoment B raw40295step1 raw40295step1Labels = mixedMoment B raw40295step2 raw40295step2Labels := by
      have ha : raw40295step2 = (fun i j => raw40295step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40295step2 raw40295step1; decide +kernel
      have hl : raw40295step2Labels = raw40295step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40295step1 raw40295step1Labels permutation8 permutation3
    _ = mixedMoment B node2278 node2278Labels := by rfl

theorem canonical40296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40296 raw40296Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw40296 raw40296Labels = mixedMoment B raw40296step0 raw40296step0Labels := by
      have hz : ∀ j, raw40296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40296step0 = (fun i j => raw40296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40296step0 raw40296; decide +kernel
      have hl : raw40296step0Labels = raw40296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40296 raw40296Labels permutation346 hz
    mixedMoment B raw40296step0 raw40296step0Labels = mixedMoment B raw40296step1 raw40296step1Labels := by
      have hz : ∀ j, raw40296step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40296step1 = (fun i j => raw40296step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40296step1 raw40296step0; decide +kernel
      have hl : raw40296step1Labels = raw40296step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40296step0 raw40296step0Labels permutation56 hz
    mixedMoment B raw40296step1 raw40296step1Labels = mixedMoment B raw40296step2 raw40296step2Labels := by
      have ha : raw40296step2 = (fun i j => raw40296step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40296step2 raw40296step1; decide +kernel
      have hl : raw40296step2Labels = raw40296step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40296step1 raw40296step1Labels permutation8 permutation3
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical40297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40297 raw40297Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw40297 raw40297Labels = mixedMoment B raw40297step0 raw40297step0Labels := by
      have hz : ∀ j, raw40297 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40297step0 = (fun i j => raw40297 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40297step0 raw40297; decide +kernel
      have hl : raw40297step0Labels = raw40297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40297 raw40297Labels permutation346 hz
    mixedMoment B raw40297step0 raw40297step0Labels = mixedMoment B raw40297step1 raw40297step1Labels := by
      have hz : ∀ j, raw40297step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40297step1 = (fun i j => raw40297step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40297step1 raw40297step0; decide +kernel
      have hl : raw40297step1Labels = raw40297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40297step0 raw40297step0Labels permutation56 hz
    mixedMoment B raw40297step1 raw40297step1Labels = mixedMoment B raw40297step2 raw40297step2Labels := by
      have ha : raw40297step2 = (fun i j => raw40297step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40297step2 raw40297step1; decide +kernel
      have hl : raw40297step2Labels = raw40297step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40297step1 raw40297step1Labels permutation8 permutation3
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical40298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40298 raw40298Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw40298 raw40298Labels = mixedMoment B raw40298step0 raw40298step0Labels := by
      have hz : ∀ j, raw40298 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40298step0 = (fun i j => raw40298 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40298step0 raw40298; decide +kernel
      have hl : raw40298step0Labels = raw40298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40298 raw40298Labels permutation265 hz
    mixedMoment B raw40298step0 raw40298step0Labels = mixedMoment B raw40298step1 raw40298step1Labels := by
      have ha : raw40298step1 = (fun i j => raw40298step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40298step1 raw40298step0; decide +kernel
      have hl : raw40298step1Labels = raw40298step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40298step0 raw40298step0Labels permutation32 permutation3
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical40299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40299 raw40299Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw40299 raw40299Labels = mixedMoment B raw40299step0 raw40299step0Labels := by
      have hz : ∀ j, raw40299 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40299step0 = (fun i j => raw40299 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40299step0 raw40299; decide +kernel
      have hl : raw40299step0Labels = raw40299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40299 raw40299Labels permutation265 hz
    mixedMoment B raw40299step0 raw40299step0Labels = mixedMoment B raw40299step1 raw40299step1Labels := by
      have ha : raw40299step1 = (fun i j => raw40299step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40299step1 raw40299step0; decide +kernel
      have hl : raw40299step1Labels = raw40299step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40299step0 raw40299step0Labels permutation32 permutation3
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical40300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40300 raw40300Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw40300 raw40300Labels = mixedMoment B raw40300step0 raw40300step0Labels := by
      have hz : ∀ j, raw40300 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40300step0 = (fun i j => raw40300 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40300step0 raw40300; decide +kernel
      have hl : raw40300step0Labels = raw40300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40300 raw40300Labels permutation265 hz
    mixedMoment B raw40300step0 raw40300step0Labels = mixedMoment B raw40300step1 raw40300step1Labels := by
      have ha : raw40300step1 = (fun i j => raw40300step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40300step1 raw40300step0; decide +kernel
      have hl : raw40300step1Labels = raw40300step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40300step0 raw40300step0Labels permutation32 permutation3
    _ = mixedMoment B node2262 node2262Labels := by rfl

theorem canonical40301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40301 raw40301Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw40301 raw40301Labels = mixedMoment B raw40301step0 raw40301step0Labels := by
      have hz : ∀ j, raw40301 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40301step0 = (fun i j => raw40301 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40301step0 raw40301; decide +kernel
      have hl : raw40301step0Labels = raw40301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40301 raw40301Labels permutation265 hz
    mixedMoment B raw40301step0 raw40301step0Labels = mixedMoment B raw40301step1 raw40301step1Labels := by
      have ha : raw40301step1 = (fun i j => raw40301step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40301step1 raw40301step0; decide +kernel
      have hl : raw40301step1Labels = raw40301step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40301step0 raw40301step0Labels permutation32 permutation3
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical40302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40302 raw40302Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw40302 raw40302Labels = mixedMoment B raw40302step0 raw40302step0Labels := by
      have hz : ∀ j, raw40302 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40302step0 = (fun i j => raw40302 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40302step0 raw40302; decide +kernel
      have hl : raw40302step0Labels = raw40302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40302 raw40302Labels permutation265 hz
    mixedMoment B raw40302step0 raw40302step0Labels = mixedMoment B raw40302step1 raw40302step1Labels := by
      have ha : raw40302step1 = (fun i j => raw40302step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40302step1 raw40302step0; decide +kernel
      have hl : raw40302step1Labels = raw40302step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40302step0 raw40302step0Labels permutation32 permutation3
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical40303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40303 raw40303Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw40303 raw40303Labels = mixedMoment B raw40303step0 raw40303step0Labels := by
      have ha : raw40303step0 = (fun i j => raw40303 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40303step0 raw40303; decide +kernel
      have hl : raw40303step0Labels = raw40303Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40303 raw40303Labels permutation152 permutation3
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical40304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40304 raw40304Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw40304 raw40304Labels = mixedMoment B raw40304step0 raw40304step0Labels := by
      have hz : ∀ j, raw40304 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40304step0 = (fun i j => raw40304 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40304step0 raw40304; decide +kernel
      have hl : raw40304step0Labels = raw40304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40304 raw40304Labels permutation520 hz
    mixedMoment B raw40304step0 raw40304step0Labels = mixedMoment B raw40304step1 raw40304step1Labels := by
      have hz : ∀ j, raw40304step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40304step1 = (fun i j => raw40304step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40304step1 raw40304step0; decide +kernel
      have hl : raw40304step1Labels = raw40304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40304step0 raw40304step0Labels permutation104 hz
    mixedMoment B raw40304step1 raw40304step1Labels = mixedMoment B raw40304step2 raw40304step2Labels := by
      have hz : ∀ j, raw40304step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40304step2 = (fun i j => raw40304step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40304step2 raw40304step1; decide +kernel
      have hl : raw40304step2Labels = raw40304step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40304step1 raw40304step1Labels permutation20 hz
    mixedMoment B raw40304step2 raw40304step2Labels = mixedMoment B raw40304step3 raw40304step3Labels := by
      have ha : raw40304step3 = (fun i j => raw40304step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40304step3 raw40304step2; decide +kernel
      have hl : raw40304step3Labels = raw40304step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40304step2 raw40304step2Labels permutation7 permutation3
    mixedMoment B raw40304step3 raw40304step3Labels = mixedMoment B raw40304step4 raw40304step4Labels := by
      have ha : raw40304step4 = -raw40304step3 := by apply Matrix.ext; change ∀ i j, raw40304step4 i j = -(raw40304step3 i j); unfold raw40304step4 raw40304step3; decide +kernel
      have hl : raw40304step4Labels = raw40304step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2268 node2268Labels := by rfl

theorem canonical40305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40305 raw40305Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw40305 raw40305Labels = mixedMoment B raw40305step0 raw40305step0Labels := by
      have hz : ∀ j, raw40305 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40305step0 = (fun i j => raw40305 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40305step0 raw40305; decide +kernel
      have hl : raw40305step0Labels = raw40305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40305 raw40305Labels permutation434 hz
    mixedMoment B raw40305step0 raw40305step0Labels = mixedMoment B raw40305step1 raw40305step1Labels := by
      have hz : ∀ j, raw40305step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40305step1 = (fun i j => raw40305step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40305step1 raw40305step0; decide +kernel
      have hl : raw40305step1Labels = raw40305step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40305step0 raw40305step0Labels permutation80 hz
    mixedMoment B raw40305step1 raw40305step1Labels = mixedMoment B raw40305step2 raw40305step2Labels := by
      have ha : raw40305step2 = (fun i j => raw40305step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40305step2 raw40305step1; decide +kernel
      have hl : raw40305step2Labels = raw40305step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40305step1 raw40305step1Labels permutation8 permutation3
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical40306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40306 raw40306Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw40306 raw40306Labels = mixedMoment B raw40306step0 raw40306step0Labels := by
      have hz : ∀ j, raw40306 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40306step0 = (fun i j => raw40306 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40306step0 raw40306; decide +kernel
      have hl : raw40306step0Labels = raw40306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40306 raw40306Labels permutation434 hz
    mixedMoment B raw40306step0 raw40306step0Labels = mixedMoment B raw40306step1 raw40306step1Labels := by
      have hz : ∀ j, raw40306step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40306step1 = (fun i j => raw40306step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40306step1 raw40306step0; decide +kernel
      have hl : raw40306step1Labels = raw40306step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40306step0 raw40306step0Labels permutation80 hz
    mixedMoment B raw40306step1 raw40306step1Labels = mixedMoment B raw40306step2 raw40306step2Labels := by
      have ha : raw40306step2 = (fun i j => raw40306step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40306step2 raw40306step1; decide +kernel
      have hl : raw40306step2Labels = raw40306step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40306step1 raw40306step1Labels permutation8 permutation3
    _ = mixedMoment B node2742 node2742Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5951 raw5951Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw5951 raw5951Labels = mixedMoment B raw5951step0 raw5951step0Labels := by
      have hz : ∀ j, raw5951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5951step0 = (fun i j => raw5951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5951step0 raw5951; decide +kernel
      have hl : raw5951step0Labels = raw5951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5951 raw5951Labels permutation434 hz
    mixedMoment B raw5951step0 raw5951step0Labels = mixedMoment B raw5951step1 raw5951step1Labels := by
      have hz : ∀ j, raw5951step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5951step1 = (fun i j => raw5951step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5951step1 raw5951step0; decide +kernel
      have hl : raw5951step1Labels = raw5951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5951step0 raw5951step0Labels permutation80 hz
    mixedMoment B raw5951step1 raw5951step1Labels = mixedMoment B raw5951step2 raw5951step2Labels := by
      have ha : raw5951step2 = (fun i j => raw5951step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5951step2 raw5951step1; decide +kernel
      have hl : raw5951step2Labels = raw5951step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5951step1 raw5951step1Labels permutation8 permutation3
    _ = mixedMoment B node2734 node2734Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment832 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 832) =
      Integer.Sparse.eval keyMomentRow832 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 832).leftCharge (GramAssembly.key 832).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 34) := by
    have ha : gramCharges (GramAssembly.key 832).leftCharge (GramAssembly.key 832).rightCharge = raw40279 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40279Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40279 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 832).leftCharge (GramAssembly.key 832).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow832, Integer.Sparse.eval]

theorem keyMoment833 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 833) =
      Integer.Sparse.eval keyMomentRow833 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 833).leftCharge (GramAssembly.key 833).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 99) := by
    have ha : gramCharges (GramAssembly.key 833).leftCharge (GramAssembly.key 833).rightCharge = raw40280 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40280Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40280 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 833).leftCharge (GramAssembly.key 833).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow833, Integer.Sparse.eval]

theorem keyMoment834 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 834) =
      Integer.Sparse.eval keyMomentRow834 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 834).leftCharge (GramAssembly.key 834).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 510) := by
    have ha : gramCharges (GramAssembly.key 834).leftCharge (GramAssembly.key 834).rightCharge = raw40281 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40281Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40281 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 834).leftCharge (GramAssembly.key 834).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow834, Integer.Sparse.eval]

theorem keyMoment835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 835) =
      Integer.Sparse.eval keyMomentRow835 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 835).leftCharge (GramAssembly.key 835).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 69) := by
    have ha : gramCharges (GramAssembly.key 835).leftCharge (GramAssembly.key 835).rightCharge = raw40282 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40282Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40282 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 835).leftCharge (GramAssembly.key 835).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow835, Integer.Sparse.eval]

theorem keyMoment836 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 836) =
      Integer.Sparse.eval keyMomentRow836 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 836).leftCharge (GramAssembly.key 836).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 186) := by
    have ha : gramCharges (GramAssembly.key 836).leftCharge (GramAssembly.key 836).rightCharge = raw40283 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40283Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40283 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 836).leftCharge (GramAssembly.key 836).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow836, Integer.Sparse.eval]

theorem keyMoment837 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 837) =
      Integer.Sparse.eval keyMomentRow837 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 837).leftCharge (GramAssembly.key 837).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 275) := by
    have ha : gramCharges (GramAssembly.key 837).leftCharge (GramAssembly.key 837).rightCharge = raw40284 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40284Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40284 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 837).leftCharge (GramAssembly.key 837).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow837, Integer.Sparse.eval]

theorem keyMoment838 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 838) =
      Integer.Sparse.eval keyMomentRow838 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 838).leftCharge (GramAssembly.key 838).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 277) := by
    have ha : gramCharges (GramAssembly.key 838).leftCharge (GramAssembly.key 838).rightCharge = raw40285 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40285Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40285 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 838).leftCharge (GramAssembly.key 838).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow838, Integer.Sparse.eval]

theorem keyMoment839 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 839) =
      Integer.Sparse.eval keyMomentRow839 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 839).leftCharge (GramAssembly.key 839).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 39) := by
    have ha : gramCharges (GramAssembly.key 839).leftCharge (GramAssembly.key 839).rightCharge = raw40286 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40286Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40286 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 839).leftCharge (GramAssembly.key 839).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow839, Integer.Sparse.eval]

theorem keyMoment840 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 840) =
      Integer.Sparse.eval keyMomentRow840 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 840).leftCharge (GramAssembly.key 840).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4085) := by
    have ha : gramCharges (GramAssembly.key 840).leftCharge (GramAssembly.key 840).rightCharge = raw2934 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw2934Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical2934 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 840).leftCharge (GramAssembly.key 840).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow840, Integer.Sparse.eval]

theorem keyMoment841 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 841) =
      Integer.Sparse.eval keyMomentRow841 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 841).leftCharge (GramAssembly.key 841).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2268) := by
    have ha : gramCharges (GramAssembly.key 841).leftCharge (GramAssembly.key 841).rightCharge = raw40287 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40287Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40287 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 841).leftCharge (GramAssembly.key 841).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow841, Integer.Sparse.eval]

theorem keyMoment842 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 842) =
      Integer.Sparse.eval keyMomentRow842 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 842).leftCharge (GramAssembly.key 842).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2281) := by
    have ha : gramCharges (GramAssembly.key 842).leftCharge (GramAssembly.key 842).rightCharge = raw40288 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40288Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40288 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 842).leftCharge (GramAssembly.key 842).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow842, Integer.Sparse.eval]

theorem keyMoment843 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 843) =
      Integer.Sparse.eval keyMomentRow843 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 843).leftCharge (GramAssembly.key 843).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4084) := by
    have ha : gramCharges (GramAssembly.key 843).leftCharge (GramAssembly.key 843).rightCharge = raw2929 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw2929Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical2929 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 843).leftCharge (GramAssembly.key 843).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow843, Integer.Sparse.eval]

theorem keyMoment844 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 844) =
      Integer.Sparse.eval keyMomentRow844 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 844).leftCharge (GramAssembly.key 844).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2293) := by
    have ha : gramCharges (GramAssembly.key 844).leftCharge (GramAssembly.key 844).rightCharge = raw40289 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40289Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40289 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 844).leftCharge (GramAssembly.key 844).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow844, Integer.Sparse.eval]

theorem keyMoment845 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 845) =
      Integer.Sparse.eval keyMomentRow845 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 845).leftCharge (GramAssembly.key 845).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2294) := by
    have ha : gramCharges (GramAssembly.key 845).leftCharge (GramAssembly.key 845).rightCharge = raw40290 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40290Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40290 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 845).leftCharge (GramAssembly.key 845).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow845, Integer.Sparse.eval]

theorem keyMoment846 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 846) =
      Integer.Sparse.eval keyMomentRow846 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 846).leftCharge (GramAssembly.key 846).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2247) := by
    have ha : gramCharges (GramAssembly.key 846).leftCharge (GramAssembly.key 846).rightCharge = raw40291 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40291Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40291 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 846).leftCharge (GramAssembly.key 846).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow846, Integer.Sparse.eval]

theorem keyMoment847 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 847) =
      Integer.Sparse.eval keyMomentRow847 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 847).leftCharge (GramAssembly.key 847).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2264) := by
    have ha : gramCharges (GramAssembly.key 847).leftCharge (GramAssembly.key 847).rightCharge = raw40292 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40292Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40292 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 847).leftCharge (GramAssembly.key 847).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow847, Integer.Sparse.eval]

theorem keyMoment848 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 848) =
      Integer.Sparse.eval keyMomentRow848 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 848).leftCharge (GramAssembly.key 848).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2265) := by
    have ha : gramCharges (GramAssembly.key 848).leftCharge (GramAssembly.key 848).rightCharge = raw40293 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40293Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40293 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 848).leftCharge (GramAssembly.key 848).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow848, Integer.Sparse.eval]

theorem keyMoment849 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 849) =
      Integer.Sparse.eval keyMomentRow849 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 849).leftCharge (GramAssembly.key 849).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2266) := by
    have ha : gramCharges (GramAssembly.key 849).leftCharge (GramAssembly.key 849).rightCharge = raw40294 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40294Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40294 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 849).leftCharge (GramAssembly.key 849).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow849, Integer.Sparse.eval]

theorem keyMoment850 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 850) =
      Integer.Sparse.eval keyMomentRow850 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 850).leftCharge (GramAssembly.key 850).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2278) := by
    have ha : gramCharges (GramAssembly.key 850).leftCharge (GramAssembly.key 850).rightCharge = raw40295 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40295Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40295 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 850).leftCharge (GramAssembly.key 850).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow850, Integer.Sparse.eval]

theorem keyMoment851 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 851) =
      Integer.Sparse.eval keyMomentRow851 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 851).leftCharge (GramAssembly.key 851).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2279) := by
    have ha : gramCharges (GramAssembly.key 851).leftCharge (GramAssembly.key 851).rightCharge = raw40296 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40296Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40296 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 851).leftCharge (GramAssembly.key 851).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow851, Integer.Sparse.eval]

theorem keyMoment852 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 852) =
      Integer.Sparse.eval keyMomentRow852 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 852).leftCharge (GramAssembly.key 852).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2291) := by
    have ha : gramCharges (GramAssembly.key 852).leftCharge (GramAssembly.key 852).rightCharge = raw40297 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40297Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40297 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 852).leftCharge (GramAssembly.key 852).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow852, Integer.Sparse.eval]

theorem keyMoment853 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 853) =
      Integer.Sparse.eval keyMomentRow853 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 853).leftCharge (GramAssembly.key 853).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4083) := by
    have ha : gramCharges (GramAssembly.key 853).leftCharge (GramAssembly.key 853).rightCharge = raw3331 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw3331Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical3331 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 853).leftCharge (GramAssembly.key 853).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow853, Integer.Sparse.eval]

theorem keyMoment854 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 854) =
      Integer.Sparse.eval keyMomentRow854 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 854).leftCharge (GramAssembly.key 854).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2244) := by
    have ha : gramCharges (GramAssembly.key 854).leftCharge (GramAssembly.key 854).rightCharge = raw40298 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40298Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40298 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 854).leftCharge (GramAssembly.key 854).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow854, Integer.Sparse.eval]

theorem keyMoment855 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 855) =
      Integer.Sparse.eval keyMomentRow855 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 855).leftCharge (GramAssembly.key 855).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2245) := by
    have ha : gramCharges (GramAssembly.key 855).leftCharge (GramAssembly.key 855).rightCharge = raw40299 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40299Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40299 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 855).leftCharge (GramAssembly.key 855).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow855, Integer.Sparse.eval]

theorem keyMoment856 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 856) =
      Integer.Sparse.eval keyMomentRow856 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 856).leftCharge (GramAssembly.key 856).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2262) := by
    have ha : gramCharges (GramAssembly.key 856).leftCharge (GramAssembly.key 856).rightCharge = raw40300 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40300Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40300 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 856).leftCharge (GramAssembly.key 856).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow856, Integer.Sparse.eval]

theorem keyMoment857 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 857) =
      Integer.Sparse.eval keyMomentRow857 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 857).leftCharge (GramAssembly.key 857).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2263) := by
    have ha : gramCharges (GramAssembly.key 857).leftCharge (GramAssembly.key 857).rightCharge = raw40301 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40301Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40301 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 857).leftCharge (GramAssembly.key 857).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow857, Integer.Sparse.eval]

theorem keyMoment858 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 858) =
      Integer.Sparse.eval keyMomentRow858 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 858).leftCharge (GramAssembly.key 858).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2277) := by
    have ha : gramCharges (GramAssembly.key 858).leftCharge (GramAssembly.key 858).rightCharge = raw40302 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40302Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40302 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 858).leftCharge (GramAssembly.key 858).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow858, Integer.Sparse.eval]

theorem keyMoment859 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 859) =
      Integer.Sparse.eval keyMomentRow859 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 859).leftCharge (GramAssembly.key 859).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2243) := by
    have ha : gramCharges (GramAssembly.key 859).leftCharge (GramAssembly.key 859).rightCharge = raw40303 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40303Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40303 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 859).leftCharge (GramAssembly.key 859).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow859, Integer.Sparse.eval]

theorem keyMoment860 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 860) =
      Integer.Sparse.eval keyMomentRow860 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 860).leftCharge (GramAssembly.key 860).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2268) := by
    have ha : gramCharges (GramAssembly.key 860).leftCharge (GramAssembly.key 860).rightCharge = raw40304 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40304Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40304 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 860).leftCharge (GramAssembly.key 860).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow860, Integer.Sparse.eval]

theorem keyMoment861 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 861) =
      Integer.Sparse.eval keyMomentRow861 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 861).leftCharge (GramAssembly.key 861).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2734) := by
    have ha : gramCharges (GramAssembly.key 861).leftCharge (GramAssembly.key 861).rightCharge = raw5951 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw5951Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical5951 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 861).leftCharge (GramAssembly.key 861).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow861, Integer.Sparse.eval]

theorem keyMoment862 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 862) =
      Integer.Sparse.eval keyMomentRow862 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 862).leftCharge (GramAssembly.key 862).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2740) := by
    have ha : gramCharges (GramAssembly.key 862).leftCharge (GramAssembly.key 862).rightCharge = raw40305 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40305Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40305 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 862).leftCharge (GramAssembly.key 862).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow862, Integer.Sparse.eval]

theorem keyMoment863 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 863) =
      Integer.Sparse.eval keyMomentRow863 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 863).leftCharge (GramAssembly.key 863).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2742) := by
    have ha : gramCharges (GramAssembly.key 863).leftCharge (GramAssembly.key 863).rightCharge = raw40306 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40306Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40306 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 863).leftCharge (GramAssembly.key 863).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow863, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt832 : keyMomentRows (832 : Fin 2886) =
    keyMomentRow832 := by decide +kernel

theorem keyMomentRowsAt833 : keyMomentRows (833 : Fin 2886) =
    keyMomentRow833 := by decide +kernel

theorem keyMomentRowsAt834 : keyMomentRows (834 : Fin 2886) =
    keyMomentRow834 := by decide +kernel

theorem keyMomentRowsAt835 : keyMomentRows (835 : Fin 2886) =
    keyMomentRow835 := by decide +kernel

theorem keyMomentRowsAt836 : keyMomentRows (836 : Fin 2886) =
    keyMomentRow836 := by decide +kernel

theorem keyMomentRowsAt837 : keyMomentRows (837 : Fin 2886) =
    keyMomentRow837 := by decide +kernel

theorem keyMomentRowsAt838 : keyMomentRows (838 : Fin 2886) =
    keyMomentRow838 := by decide +kernel

theorem keyMomentRowsAt839 : keyMomentRows (839 : Fin 2886) =
    keyMomentRow839 := by decide +kernel

theorem keyMomentRowsAt840 : keyMomentRows (840 : Fin 2886) =
    keyMomentRow840 := by decide +kernel

theorem keyMomentRowsAt841 : keyMomentRows (841 : Fin 2886) =
    keyMomentRow841 := by decide +kernel

theorem keyMomentRowsAt842 : keyMomentRows (842 : Fin 2886) =
    keyMomentRow842 := by decide +kernel

theorem keyMomentRowsAt843 : keyMomentRows (843 : Fin 2886) =
    keyMomentRow843 := by decide +kernel

theorem keyMomentRowsAt844 : keyMomentRows (844 : Fin 2886) =
    keyMomentRow844 := by decide +kernel

theorem keyMomentRowsAt845 : keyMomentRows (845 : Fin 2886) =
    keyMomentRow845 := by decide +kernel

theorem keyMomentRowsAt846 : keyMomentRows (846 : Fin 2886) =
    keyMomentRow846 := by decide +kernel

theorem keyMomentRowsAt847 : keyMomentRows (847 : Fin 2886) =
    keyMomentRow847 := by decide +kernel

theorem keyMomentRowsAt848 : keyMomentRows (848 : Fin 2886) =
    keyMomentRow848 := by decide +kernel

theorem keyMomentRowsAt849 : keyMomentRows (849 : Fin 2886) =
    keyMomentRow849 := by decide +kernel

theorem keyMomentRowsAt850 : keyMomentRows (850 : Fin 2886) =
    keyMomentRow850 := by decide +kernel

theorem keyMomentRowsAt851 : keyMomentRows (851 : Fin 2886) =
    keyMomentRow851 := by decide +kernel

theorem keyMomentRowsAt852 : keyMomentRows (852 : Fin 2886) =
    keyMomentRow852 := by decide +kernel

theorem keyMomentRowsAt853 : keyMomentRows (853 : Fin 2886) =
    keyMomentRow853 := by decide +kernel

theorem keyMomentRowsAt854 : keyMomentRows (854 : Fin 2886) =
    keyMomentRow854 := by decide +kernel

theorem keyMomentRowsAt855 : keyMomentRows (855 : Fin 2886) =
    keyMomentRow855 := by decide +kernel

theorem keyMomentRowsAt856 : keyMomentRows (856 : Fin 2886) =
    keyMomentRow856 := by decide +kernel

theorem keyMomentRowsAt857 : keyMomentRows (857 : Fin 2886) =
    keyMomentRow857 := by decide +kernel

theorem keyMomentRowsAt858 : keyMomentRows (858 : Fin 2886) =
    keyMomentRow858 := by decide +kernel

theorem keyMomentRowsAt859 : keyMomentRows (859 : Fin 2886) =
    keyMomentRow859 := by decide +kernel

theorem keyMomentRowsAt860 : keyMomentRows (860 : Fin 2886) =
    keyMomentRow860 := by decide +kernel

theorem keyMomentRowsAt861 : keyMomentRows (861 : Fin 2886) =
    keyMomentRow861 := by decide +kernel

theorem keyMomentRowsAt862 : keyMomentRows (862 : Fin 2886) =
    keyMomentRow862 := by decide +kernel

theorem keyMomentRowsAt863 : keyMomentRows (863 : Fin 2886) =
    keyMomentRow863 := by decide +kernel

theorem keyMomentChunkSound26_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 26) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 832 ∨ k.val = 833 ∨ k.val = 834 ∨ k.val = 835 ∨ k.val = 836 ∨ k.val = 837 ∨ k.val = 838 ∨ k.val = 839 ∨ k.val = 840 ∨ k.val = 841 ∨ k.val = 842 ∨ k.val = 843 ∨ k.val = 844 ∨ k.val = 845 ∨ k.val = 846 ∨ k.val = 847 ∨ k.val = 848 ∨ k.val = 849 ∨ k.val = 850 ∨ k.val = 851 ∨ k.val = 852 ∨ k.val = 853 ∨ k.val = 854 ∨ k.val = 855 ∨ k.val = 856 ∨ k.val = 857 ∨ k.val = 858 ∨ k.val = 859 ∨ k.val = 860 ∨ k.val = 861 ∨ k.val = 862 ∨ k.val = 863 := by omega
  rcases heq with h832 | h833 | h834 | h835 | h836 | h837 | h838 | h839 | h840 | h841 | h842 | h843 | h844 | h845 | h846 | h847 | h848 | h849 | h850 | h851 | h852 | h853 | h854 | h855 | h856 | h857 | h858 | h859 | h860 | h861 | h862 | h863
  · have he : k = (832 : Fin 2886) := Fin.ext h832
    subst k
    rw [keyMomentRowsAt832]
    exact keyMoment832 B hB
  · have he : k = (833 : Fin 2886) := Fin.ext h833
    subst k
    rw [keyMomentRowsAt833]
    exact keyMoment833 B hB
  · have he : k = (834 : Fin 2886) := Fin.ext h834
    subst k
    rw [keyMomentRowsAt834]
    exact keyMoment834 B hB
  · have he : k = (835 : Fin 2886) := Fin.ext h835
    subst k
    rw [keyMomentRowsAt835]
    exact keyMoment835 B hB
  · have he : k = (836 : Fin 2886) := Fin.ext h836
    subst k
    rw [keyMomentRowsAt836]
    exact keyMoment836 B hB
  · have he : k = (837 : Fin 2886) := Fin.ext h837
    subst k
    rw [keyMomentRowsAt837]
    exact keyMoment837 B hB
  · have he : k = (838 : Fin 2886) := Fin.ext h838
    subst k
    rw [keyMomentRowsAt838]
    exact keyMoment838 B hB
  · have he : k = (839 : Fin 2886) := Fin.ext h839
    subst k
    rw [keyMomentRowsAt839]
    exact keyMoment839 B hB
  · have he : k = (840 : Fin 2886) := Fin.ext h840
    subst k
    rw [keyMomentRowsAt840]
    exact keyMoment840 B hB
  · have he : k = (841 : Fin 2886) := Fin.ext h841
    subst k
    rw [keyMomentRowsAt841]
    exact keyMoment841 B hB
  · have he : k = (842 : Fin 2886) := Fin.ext h842
    subst k
    rw [keyMomentRowsAt842]
    exact keyMoment842 B hB
  · have he : k = (843 : Fin 2886) := Fin.ext h843
    subst k
    rw [keyMomentRowsAt843]
    exact keyMoment843 B hB
  · have he : k = (844 : Fin 2886) := Fin.ext h844
    subst k
    rw [keyMomentRowsAt844]
    exact keyMoment844 B hB
  · have he : k = (845 : Fin 2886) := Fin.ext h845
    subst k
    rw [keyMomentRowsAt845]
    exact keyMoment845 B hB
  · have he : k = (846 : Fin 2886) := Fin.ext h846
    subst k
    rw [keyMomentRowsAt846]
    exact keyMoment846 B hB
  · have he : k = (847 : Fin 2886) := Fin.ext h847
    subst k
    rw [keyMomentRowsAt847]
    exact keyMoment847 B hB
  · have he : k = (848 : Fin 2886) := Fin.ext h848
    subst k
    rw [keyMomentRowsAt848]
    exact keyMoment848 B hB
  · have he : k = (849 : Fin 2886) := Fin.ext h849
    subst k
    rw [keyMomentRowsAt849]
    exact keyMoment849 B hB
  · have he : k = (850 : Fin 2886) := Fin.ext h850
    subst k
    rw [keyMomentRowsAt850]
    exact keyMoment850 B hB
  · have he : k = (851 : Fin 2886) := Fin.ext h851
    subst k
    rw [keyMomentRowsAt851]
    exact keyMoment851 B hB
  · have he : k = (852 : Fin 2886) := Fin.ext h852
    subst k
    rw [keyMomentRowsAt852]
    exact keyMoment852 B hB
  · have he : k = (853 : Fin 2886) := Fin.ext h853
    subst k
    rw [keyMomentRowsAt853]
    exact keyMoment853 B hB
  · have he : k = (854 : Fin 2886) := Fin.ext h854
    subst k
    rw [keyMomentRowsAt854]
    exact keyMoment854 B hB
  · have he : k = (855 : Fin 2886) := Fin.ext h855
    subst k
    rw [keyMomentRowsAt855]
    exact keyMoment855 B hB
  · have he : k = (856 : Fin 2886) := Fin.ext h856
    subst k
    rw [keyMomentRowsAt856]
    exact keyMoment856 B hB
  · have he : k = (857 : Fin 2886) := Fin.ext h857
    subst k
    rw [keyMomentRowsAt857]
    exact keyMoment857 B hB
  · have he : k = (858 : Fin 2886) := Fin.ext h858
    subst k
    rw [keyMomentRowsAt858]
    exact keyMoment858 B hB
  · have he : k = (859 : Fin 2886) := Fin.ext h859
    subst k
    rw [keyMomentRowsAt859]
    exact keyMoment859 B hB
  · have he : k = (860 : Fin 2886) := Fin.ext h860
    subst k
    rw [keyMomentRowsAt860]
    exact keyMoment860 B hB
  · have he : k = (861 : Fin 2886) := Fin.ext h861
    subst k
    rw [keyMomentRowsAt861]
    exact keyMoment861 B hB
  · have he : k = (862 : Fin 2886) := Fin.ext h862
    subst k
    rw [keyMomentRowsAt862]
    exact keyMoment862 B hB
  · have he : k = (863 : Fin 2886) := Fin.ext h863
    subst k
    rw [keyMomentRowsAt863]
    exact keyMoment863 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound26_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound26_e_oai
