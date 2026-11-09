-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound73_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:02:23.893883+00:00
-- url     : https://prove2.me/submissions/58ece116-88fc-4a23-8f0d-c183809286be

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E113
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

theorem rename_labels {p n l k : ℕ} (hk : k ≤ 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (small : Fin n → Fin l) (e : Fin l ↪ Fin k) (h : label = e ∘ small) :
    mixedMoment B A label = mixedMoment B A small := by
  rw [h]
  exact mixedMoment_label_embedding hk B A e small

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical328
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41984 raw41984Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw41984 raw41984Labels = mixedMoment B raw41984step0 raw41984step0Labels := by
      have hz : ∀ j, raw41984 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41984step0 = (fun i j => raw41984 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41984step0 raw41984; decide +kernel
      have hl : raw41984step0Labels = raw41984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41984 raw41984Labels permutation346 hz
    mixedMoment B raw41984step0 raw41984step0Labels = mixedMoment B raw41984step1 raw41984step1Labels := by
      have ha : raw41984step1 = (fun i j => raw41984step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41984step1 raw41984step0; decide +kernel
      have hl : raw41984step1Labels = raw41984step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41984step0 raw41984step0Labels permutation37 permutation4
    mixedMoment B raw41984step1 raw41984step1Labels = mixedMoment B raw41984step2 raw41984step2Labels := by
      have ha : raw41984step2 = -raw41984step1 := by apply Matrix.ext; change ∀ i j, raw41984step2 i j = -(raw41984step1 i j); unfold raw41984step2 raw41984step1; decide +kernel
      have hl : raw41984step2Labels = raw41984step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41984step2 raw41984step2Labels = mixedMoment B raw41984step3 raw41984step3Labels := by
      have ha : raw41984step3 = raw41984step2 := by apply Matrix.ext; unfold raw41984step3 raw41984step2; decide +kernel
      have hl : raw41984step2Labels = labelEmbedding1 ∘ raw41984step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41984step2 raw41984step2Labels raw41984step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3109 node3109Labels := by rfl

theorem canonical41985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41985 raw41985Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw41985 raw41985Labels = mixedMoment B raw41985step0 raw41985step0Labels := by
      have hz : ∀ j, raw41985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41985step0 = (fun i j => raw41985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41985step0 raw41985; decide +kernel
      have hl : raw41985step0Labels = raw41985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41985 raw41985Labels permutation346 hz
    mixedMoment B raw41985step0 raw41985step0Labels = mixedMoment B raw41985step1 raw41985step1Labels := by
      have ha : raw41985step1 = (fun i j => raw41985step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41985step1 raw41985step0; decide +kernel
      have hl : raw41985step1Labels = raw41985step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41985step0 raw41985step0Labels permutation32 permutation5
    mixedMoment B raw41985step1 raw41985step1Labels = mixedMoment B raw41985step2 raw41985step2Labels := by
      have ha : raw41985step2 = -raw41985step1 := by apply Matrix.ext; change ∀ i j, raw41985step2 i j = -(raw41985step1 i j); unfold raw41985step2 raw41985step1; decide +kernel
      have hl : raw41985step2Labels = raw41985step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41985step2 raw41985step2Labels = mixedMoment B raw41985step3 raw41985step3Labels := by
      have ha : raw41985step3 = raw41985step2 := by apply Matrix.ext; unfold raw41985step3 raw41985step2; decide +kernel
      have hl : raw41985step2Labels = labelEmbedding9 ∘ raw41985step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41985step2 raw41985step2Labels raw41985step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical41986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41986 raw41986Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw41986 raw41986Labels = mixedMoment B raw41986step0 raw41986step0Labels := by
      have hz : ∀ j, raw41986 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41986step0 = (fun i j => raw41986 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41986step0 raw41986; decide +kernel
      have hl : raw41986step0Labels = raw41986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41986 raw41986Labels permutation346 hz
    mixedMoment B raw41986step0 raw41986step0Labels = mixedMoment B raw41986step1 raw41986step1Labels := by
      have ha : raw41986step1 = (fun i j => raw41986step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41986step1 raw41986step0; decide +kernel
      have hl : raw41986step1Labels = raw41986step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41986step0 raw41986step0Labels permutation50 permutation4
    mixedMoment B raw41986step1 raw41986step1Labels = mixedMoment B raw41986step2 raw41986step2Labels := by
      have ha : raw41986step2 = -raw41986step1 := by apply Matrix.ext; change ∀ i j, raw41986step2 i j = -(raw41986step1 i j); unfold raw41986step2 raw41986step1; decide +kernel
      have hl : raw41986step2Labels = raw41986step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41986step2 raw41986step2Labels = mixedMoment B raw41986step3 raw41986step3Labels := by
      have ha : raw41986step3 = raw41986step2 := by apply Matrix.ext; unfold raw41986step3 raw41986step2; decide +kernel
      have hl : raw41986step2Labels = labelEmbedding1 ∘ raw41986step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41986step2 raw41986step2Labels raw41986step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

theorem canonical41987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41987 raw41987Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw41987 raw41987Labels = mixedMoment B raw41987step0 raw41987step0Labels := by
      have hz : ∀ j, raw41987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41987step0 = (fun i j => raw41987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41987step0 raw41987; decide +kernel
      have hl : raw41987step0Labels = raw41987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41987 raw41987Labels permutation346 hz
    mixedMoment B raw41987step0 raw41987step0Labels = mixedMoment B raw41987step1 raw41987step1Labels := by
      have ha : raw41987step1 = (fun i j => raw41987step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41987step1 raw41987step0; decide +kernel
      have hl : raw41987step1Labels = raw41987step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41987step0 raw41987step0Labels permutation36 permutation5
    mixedMoment B raw41987step1 raw41987step1Labels = mixedMoment B raw41987step2 raw41987step2Labels := by
      have ha : raw41987step2 = -raw41987step1 := by apply Matrix.ext; change ∀ i j, raw41987step2 i j = -(raw41987step1 i j); unfold raw41987step2 raw41987step1; decide +kernel
      have hl : raw41987step2Labels = raw41987step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41987step2 raw41987step2Labels = mixedMoment B raw41987step3 raw41987step3Labels := by
      have ha : raw41987step3 = raw41987step2 := by apply Matrix.ext; unfold raw41987step3 raw41987step2; decide +kernel
      have hl : raw41987step2Labels = labelEmbedding9 ∘ raw41987step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41987step2 raw41987step2Labels raw41987step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical41988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41988 raw41988Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw41988 raw41988Labels = mixedMoment B raw41988step0 raw41988step0Labels := by
      have hz : ∀ j, raw41988 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41988step0 = (fun i j => raw41988 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41988step0 raw41988; decide +kernel
      have hl : raw41988step0Labels = raw41988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41988 raw41988Labels permutation346 hz
    mixedMoment B raw41988step0 raw41988step0Labels = mixedMoment B raw41988step1 raw41988step1Labels := by
      have ha : raw41988step1 = (fun i j => raw41988step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41988step1 raw41988step0; decide +kernel
      have hl : raw41988step1Labels = raw41988step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41988step0 raw41988step0Labels permutation51 permutation4
    mixedMoment B raw41988step1 raw41988step1Labels = mixedMoment B raw41988step2 raw41988step2Labels := by
      have ha : raw41988step2 = -raw41988step1 := by apply Matrix.ext; change ∀ i j, raw41988step2 i j = -(raw41988step1 i j); unfold raw41988step2 raw41988step1; decide +kernel
      have hl : raw41988step2Labels = raw41988step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41988step2 raw41988step2Labels = mixedMoment B raw41988step3 raw41988step3Labels := by
      have ha : raw41988step3 = raw41988step2 := by apply Matrix.ext; unfold raw41988step3 raw41988step2; decide +kernel
      have hl : raw41988step2Labels = labelEmbedding1 ∘ raw41988step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41988step2 raw41988step2Labels raw41988step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3038 node3038Labels := by rfl

theorem canonical41989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41989 raw41989Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw41989 raw41989Labels = mixedMoment B raw41989step0 raw41989step0Labels := by
      have hz : ∀ j, raw41989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41989step0 = (fun i j => raw41989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41989step0 raw41989; decide +kernel
      have hl : raw41989step0Labels = raw41989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41989 raw41989Labels permutation346 hz
    mixedMoment B raw41989step0 raw41989step0Labels = mixedMoment B raw41989step1 raw41989step1Labels := by
      have ha : raw41989step1 = (fun i j => raw41989step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41989step1 raw41989step0; decide +kernel
      have hl : raw41989step1Labels = raw41989step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41989step0 raw41989step0Labels permutation37 permutation5
    mixedMoment B raw41989step1 raw41989step1Labels = mixedMoment B raw41989step2 raw41989step2Labels := by
      have ha : raw41989step2 = -raw41989step1 := by apply Matrix.ext; change ∀ i j, raw41989step2 i j = -(raw41989step1 i j); unfold raw41989step2 raw41989step1; decide +kernel
      have hl : raw41989step2Labels = raw41989step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41989step2 raw41989step2Labels = mixedMoment B raw41989step3 raw41989step3Labels := by
      have ha : raw41989step3 = raw41989step2 := by apply Matrix.ext; unfold raw41989step3 raw41989step2; decide +kernel
      have hl : raw41989step2Labels = labelEmbedding9 ∘ raw41989step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41989step2 raw41989step2Labels raw41989step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

theorem canonical41990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41990 raw41990Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw41990 raw41990Labels = mixedMoment B raw41990step0 raw41990step0Labels := by
      have hz : ∀ j, raw41990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41990step0 = (fun i j => raw41990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41990step0 raw41990; decide +kernel
      have hl : raw41990step0Labels = raw41990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41990 raw41990Labels permutation346 hz
    mixedMoment B raw41990step0 raw41990step0Labels = mixedMoment B raw41990step1 raw41990step1Labels := by
      have ha : raw41990step1 = (fun i j => raw41990step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41990step1 raw41990step0; decide +kernel
      have hl : raw41990step1Labels = raw41990step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41990step0 raw41990step0Labels permutation38 permutation4
    mixedMoment B raw41990step1 raw41990step1Labels = mixedMoment B raw41990step2 raw41990step2Labels := by
      have ha : raw41990step2 = -raw41990step1 := by apply Matrix.ext; change ∀ i j, raw41990step2 i j = -(raw41990step1 i j); unfold raw41990step2 raw41990step1; decide +kernel
      have hl : raw41990step2Labels = raw41990step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41990step2 raw41990step2Labels = mixedMoment B raw41990step3 raw41990step3Labels := by
      have ha : raw41990step3 = raw41990step2 := by apply Matrix.ext; unfold raw41990step3 raw41990step2; decide +kernel
      have hl : raw41990step2Labels = labelEmbedding1 ∘ raw41990step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41990step2 raw41990step2Labels raw41990step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3088 node3088Labels := by rfl

theorem canonical41991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41991 raw41991Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw41991 raw41991Labels = mixedMoment B raw41991step0 raw41991step0Labels := by
      have hz : ∀ j, raw41991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41991step0 = (fun i j => raw41991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41991step0 raw41991; decide +kernel
      have hl : raw41991step0Labels = raw41991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41991 raw41991Labels permutation346 hz
    mixedMoment B raw41991step0 raw41991step0Labels = mixedMoment B raw41991step1 raw41991step1Labels := by
      have ha : raw41991step1 = (fun i j => raw41991step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41991step1 raw41991step0; decide +kernel
      have hl : raw41991step1Labels = raw41991step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41991step0 raw41991step0Labels permutation32 permutation5
    mixedMoment B raw41991step1 raw41991step1Labels = mixedMoment B raw41991step2 raw41991step2Labels := by
      have ha : raw41991step2 = -raw41991step1 := by apply Matrix.ext; change ∀ i j, raw41991step2 i j = -(raw41991step1 i j); unfold raw41991step2 raw41991step1; decide +kernel
      have hl : raw41991step2Labels = raw41991step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41991step2 raw41991step2Labels = mixedMoment B raw41991step3 raw41991step3Labels := by
      have ha : raw41991step3 = raw41991step2 := by apply Matrix.ext; unfold raw41991step3 raw41991step2; decide +kernel
      have hl : raw41991step2Labels = labelEmbedding9 ∘ raw41991step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41991step2 raw41991step2Labels raw41991step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical41992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41992 raw41992Labels = mixedMoment B node3111 node3111Labels := by
  calc
    mixedMoment B raw41992 raw41992Labels = mixedMoment B raw41992step0 raw41992step0Labels := by
      have hz : ∀ j, raw41992 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41992step0 = (fun i j => raw41992 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41992step0 raw41992; decide +kernel
      have hl : raw41992step0Labels = raw41992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41992 raw41992Labels permutation346 hz
    mixedMoment B raw41992step0 raw41992step0Labels = mixedMoment B raw41992step1 raw41992step1Labels := by
      have ha : raw41992step1 = (fun i j => raw41992step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41992step1 raw41992step0; decide +kernel
      have hl : raw41992step1Labels = raw41992step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41992step0 raw41992step0Labels permutation32 permutation4
    mixedMoment B raw41992step1 raw41992step1Labels = mixedMoment B raw41992step2 raw41992step2Labels := by
      have ha : raw41992step2 = -raw41992step1 := by apply Matrix.ext; change ∀ i j, raw41992step2 i j = -(raw41992step1 i j); unfold raw41992step2 raw41992step1; decide +kernel
      have hl : raw41992step2Labels = raw41992step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41992step2 raw41992step2Labels = mixedMoment B raw41992step3 raw41992step3Labels := by
      have ha : raw41992step3 = raw41992step2 := by apply Matrix.ext; unfold raw41992step3 raw41992step2; decide +kernel
      have hl : raw41992step2Labels = labelEmbedding1 ∘ raw41992step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41992step2 raw41992step2Labels raw41992step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3111 node3111Labels := by rfl

theorem canonical41993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41993 raw41993Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw41993 raw41993Labels = mixedMoment B raw41993step0 raw41993step0Labels := by
      have hz : ∀ j, raw41993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41993step0 = (fun i j => raw41993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41993step0 raw41993; decide +kernel
      have hl : raw41993step0Labels = raw41993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41993 raw41993Labels permutation346 hz
    mixedMoment B raw41993step0 raw41993step0Labels = mixedMoment B raw41993step1 raw41993step1Labels := by
      have ha : raw41993step1 = (fun i j => raw41993step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41993step1 raw41993step0; decide +kernel
      have hl : raw41993step1Labels = raw41993step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41993step0 raw41993step0Labels permutation32 permutation5
    mixedMoment B raw41993step1 raw41993step1Labels = mixedMoment B raw41993step2 raw41993step2Labels := by
      have ha : raw41993step2 = -raw41993step1 := by apply Matrix.ext; change ∀ i j, raw41993step2 i j = -(raw41993step1 i j); unfold raw41993step2 raw41993step1; decide +kernel
      have hl : raw41993step2Labels = raw41993step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41993step2 raw41993step2Labels = mixedMoment B raw41993step3 raw41993step3Labels := by
      have ha : raw41993step3 = raw41993step2 := by apply Matrix.ext; unfold raw41993step3 raw41993step2; decide +kernel
      have hl : raw41993step2Labels = labelEmbedding9 ∘ raw41993step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41993step2 raw41993step2Labels raw41993step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

theorem canonical41994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41994 raw41994Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw41994 raw41994Labels = mixedMoment B raw41994step0 raw41994step0Labels := by
      have ha : raw41994step0 = (fun i j => raw41994 (permutation250 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41994step0 raw41994; decide +kernel
      have hl : raw41994step0Labels = raw41994Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41994 raw41994Labels permutation250 permutation4
    mixedMoment B raw41994step0 raw41994step0Labels = mixedMoment B raw41994step1 raw41994step1Labels := by
      have ha : raw41994step1 = -raw41994step0 := by apply Matrix.ext; change ∀ i j, raw41994step1 i j = -(raw41994step0 i j); unfold raw41994step1 raw41994step0; decide +kernel
      have hl : raw41994step1Labels = raw41994step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41994step1 raw41994step1Labels = mixedMoment B raw41994step2 raw41994step2Labels := by
      have ha : raw41994step2 = raw41994step1 := by apply Matrix.ext; unfold raw41994step2 raw41994step1; decide +kernel
      have hl : raw41994step1Labels = labelEmbedding1 ∘ raw41994step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41994step1 raw41994step1Labels raw41994step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical41995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41995 raw41995Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw41995 raw41995Labels = mixedMoment B raw41995step0 raw41995step0Labels := by
      have ha : raw41995step0 = (fun i j => raw41995 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41995step0 raw41995; decide +kernel
      have hl : raw41995step0Labels = raw41995Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41995 raw41995Labels permutation170 permutation5
    mixedMoment B raw41995step0 raw41995step0Labels = mixedMoment B raw41995step1 raw41995step1Labels := by
      have ha : raw41995step1 = -raw41995step0 := by apply Matrix.ext; change ∀ i j, raw41995step1 i j = -(raw41995step0 i j); unfold raw41995step1 raw41995step0; decide +kernel
      have hl : raw41995step1Labels = raw41995step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41995step1 raw41995step1Labels = mixedMoment B raw41995step2 raw41995step2Labels := by
      have ha : raw41995step2 = raw41995step1 := by apply Matrix.ext; unfold raw41995step2 raw41995step1; decide +kernel
      have hl : raw41995step1Labels = labelEmbedding9 ∘ raw41995step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41995step1 raw41995step1Labels raw41995step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical41996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41996 raw41996Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw41996 raw41996Labels = mixedMoment B raw41996step0 raw41996step0Labels := by
      have ha : raw41996step0 = (fun i j => raw41996 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41996step0 raw41996; decide +kernel
      have hl : raw41996step0Labels = raw41996Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41996 raw41996Labels permutation212 permutation4
    mixedMoment B raw41996step0 raw41996step0Labels = mixedMoment B raw41996step1 raw41996step1Labels := by
      have ha : raw41996step1 = -raw41996step0 := by apply Matrix.ext; change ∀ i j, raw41996step1 i j = -(raw41996step0 i j); unfold raw41996step1 raw41996step0; decide +kernel
      have hl : raw41996step1Labels = raw41996step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41996step1 raw41996step1Labels = mixedMoment B raw41996step2 raw41996step2Labels := by
      have ha : raw41996step2 = raw41996step1 := by apply Matrix.ext; unfold raw41996step2 raw41996step1; decide +kernel
      have hl : raw41996step1Labels = labelEmbedding1 ∘ raw41996step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41996step1 raw41996step1Labels raw41996step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3065 node3065Labels := by rfl

theorem canonical41997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41997 raw41997Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw41997 raw41997Labels = mixedMoment B raw41997step0 raw41997step0Labels := by
      have ha : raw41997step0 = (fun i j => raw41997 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41997step0 raw41997; decide +kernel
      have hl : raw41997step0Labels = raw41997Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41997 raw41997Labels permutation160 permutation5
    mixedMoment B raw41997step0 raw41997step0Labels = mixedMoment B raw41997step1 raw41997step1Labels := by
      have ha : raw41997step1 = -raw41997step0 := by apply Matrix.ext; change ∀ i j, raw41997step1 i j = -(raw41997step0 i j); unfold raw41997step1 raw41997step0; decide +kernel
      have hl : raw41997step1Labels = raw41997step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41997step1 raw41997step1Labels = mixedMoment B raw41997step2 raw41997step2Labels := by
      have ha : raw41997step2 = raw41997step1 := by apply Matrix.ext; unfold raw41997step2 raw41997step1; decide +kernel
      have hl : raw41997step1Labels = labelEmbedding9 ∘ raw41997step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41997step1 raw41997step1Labels raw41997step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5250 node5250Labels := by rfl

theorem canonical41998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41998 raw41998Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw41998 raw41998Labels = mixedMoment B raw41998step0 raw41998step0Labels := by
      have ha : raw41998step0 = (fun i j => raw41998 (permutation203 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41998step0 raw41998; decide +kernel
      have hl : raw41998step0Labels = raw41998Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41998 raw41998Labels permutation203 permutation4
    mixedMoment B raw41998step0 raw41998step0Labels = mixedMoment B raw41998step1 raw41998step1Labels := by
      have ha : raw41998step1 = -raw41998step0 := by apply Matrix.ext; change ∀ i j, raw41998step1 i j = -(raw41998step0 i j); unfold raw41998step1 raw41998step0; decide +kernel
      have hl : raw41998step1Labels = raw41998step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41998step1 raw41998step1Labels = mixedMoment B raw41998step2 raw41998step2Labels := by
      have ha : raw41998step2 = raw41998step1 := by apply Matrix.ext; unfold raw41998step2 raw41998step1; decide +kernel
      have hl : raw41998step1Labels = labelEmbedding1 ∘ raw41998step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41998step1 raw41998step1Labels raw41998step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3087 node3087Labels := by rfl

theorem canonical41999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41999 raw41999Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw41999 raw41999Labels = mixedMoment B raw41999step0 raw41999step0Labels := by
      have ha : raw41999step0 = (fun i j => raw41999 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41999step0 raw41999; decide +kernel
      have hl : raw41999step0Labels = raw41999Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41999 raw41999Labels permutation158 permutation5
    mixedMoment B raw41999step0 raw41999step0Labels = mixedMoment B raw41999step1 raw41999step1Labels := by
      have ha : raw41999step1 = -raw41999step0 := by apply Matrix.ext; change ∀ i j, raw41999step1 i j = -(raw41999step0 i j); unfold raw41999step1 raw41999step0; decide +kernel
      have hl : raw41999step1Labels = raw41999step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41999step1 raw41999step1Labels = mixedMoment B raw41999step2 raw41999step2Labels := by
      have ha : raw41999step2 = raw41999step1 := by apply Matrix.ext; unfold raw41999step2 raw41999step1; decide +kernel
      have hl : raw41999step1Labels = labelEmbedding9 ∘ raw41999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41999step1 raw41999step1Labels raw41999step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical42000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42000 raw42000Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw42000 raw42000Labels = mixedMoment B raw42000step0 raw42000step0Labels := by
      have ha : raw42000step0 = (fun i j => raw42000 (permutation213 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42000step0 raw42000; decide +kernel
      have hl : raw42000step0Labels = raw42000Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42000 raw42000Labels permutation213 permutation4
    mixedMoment B raw42000step0 raw42000step0Labels = mixedMoment B raw42000step1 raw42000step1Labels := by
      have ha : raw42000step1 = -raw42000step0 := by apply Matrix.ext; change ∀ i j, raw42000step1 i j = -(raw42000step0 i j); unfold raw42000step1 raw42000step0; decide +kernel
      have hl : raw42000step1Labels = raw42000step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42000step1 raw42000step1Labels = mixedMoment B raw42000step2 raw42000step2Labels := by
      have ha : raw42000step2 = raw42000step1 := by apply Matrix.ext; unfold raw42000step2 raw42000step1; decide +kernel
      have hl : raw42000step1Labels = labelEmbedding1 ∘ raw42000step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42000step1 raw42000step1Labels raw42000step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3064 node3064Labels := by rfl

theorem canonical42001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42001 raw42001Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw42001 raw42001Labels = mixedMoment B raw42001step0 raw42001step0Labels := by
      have ha : raw42001step0 = (fun i j => raw42001 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42001step0 raw42001; decide +kernel
      have hl : raw42001step0Labels = raw42001Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42001 raw42001Labels permutation161 permutation5
    mixedMoment B raw42001step0 raw42001step0Labels = mixedMoment B raw42001step1 raw42001step1Labels := by
      have ha : raw42001step1 = -raw42001step0 := by apply Matrix.ext; change ∀ i j, raw42001step1 i j = -(raw42001step0 i j); unfold raw42001step1 raw42001step0; decide +kernel
      have hl : raw42001step1Labels = raw42001step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42001step1 raw42001step1Labels = mixedMoment B raw42001step2 raw42001step2Labels := by
      have ha : raw42001step2 = raw42001step1 := by apply Matrix.ext; unfold raw42001step2 raw42001step1; decide +kernel
      have hl : raw42001step1Labels = labelEmbedding9 ∘ raw42001step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42001step1 raw42001step1Labels raw42001step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical42002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42002 raw42002Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw42002 raw42002Labels = mixedMoment B raw42002step0 raw42002step0Labels := by
      have hz : ∀ j, raw42002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42002step0 = (fun i j => raw42002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42002step0 raw42002; decide +kernel
      have hl : raw42002step0Labels = raw42002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42002 raw42002Labels permutation434 hz
    mixedMoment B raw42002step0 raw42002step0Labels = mixedMoment B raw42002step1 raw42002step1Labels := by
      have hz : ∀ j, raw42002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42002step1 = (fun i j => raw42002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42002step1 raw42002step0; decide +kernel
      have hl : raw42002step1Labels = raw42002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42002step0 raw42002step0Labels permutation80 hz
    mixedMoment B raw42002step1 raw42002step1Labels = mixedMoment B raw42002step2 raw42002step2Labels := by
      have ha : raw42002step2 = (fun i j => raw42002step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42002step2 raw42002step1; decide +kernel
      have hl : raw42002step2Labels = raw42002step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42002step1 raw42002step1Labels permutation10 permutation4
    mixedMoment B raw42002step2 raw42002step2Labels = mixedMoment B raw42002step3 raw42002step3Labels := by
      have ha : raw42002step3 = -raw42002step2 := by apply Matrix.ext; change ∀ i j, raw42002step3 i j = -(raw42002step2 i j); unfold raw42002step3 raw42002step2; decide +kernel
      have hl : raw42002step3Labels = raw42002step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42002step3 raw42002step3Labels = mixedMoment B raw42002step4 raw42002step4Labels := by
      have ha : raw42002step4 = raw42002step3 := by apply Matrix.ext; unfold raw42002step4 raw42002step3; decide +kernel
      have hl : raw42002step3Labels = labelEmbedding1 ∘ raw42002step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42002step3 raw42002step3Labels raw42002step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3103 node3103Labels := by rfl

theorem canonical42003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42003 raw42003Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw42003 raw42003Labels = mixedMoment B raw42003step0 raw42003step0Labels := by
      have hz : ∀ j, raw42003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42003step0 = (fun i j => raw42003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42003step0 raw42003; decide +kernel
      have hl : raw42003step0Labels = raw42003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42003 raw42003Labels permutation434 hz
    mixedMoment B raw42003step0 raw42003step0Labels = mixedMoment B raw42003step1 raw42003step1Labels := by
      have hz : ∀ j, raw42003step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42003step1 = (fun i j => raw42003step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42003step1 raw42003step0; decide +kernel
      have hl : raw42003step1Labels = raw42003step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42003step0 raw42003step0Labels permutation80 hz
    mixedMoment B raw42003step1 raw42003step1Labels = mixedMoment B raw42003step2 raw42003step2Labels := by
      have ha : raw42003step2 = (fun i j => raw42003step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42003step2 raw42003step1; decide +kernel
      have hl : raw42003step2Labels = raw42003step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42003step1 raw42003step1Labels permutation10 permutation5
    mixedMoment B raw42003step2 raw42003step2Labels = mixedMoment B raw42003step3 raw42003step3Labels := by
      have ha : raw42003step3 = -raw42003step2 := by apply Matrix.ext; change ∀ i j, raw42003step3 i j = -(raw42003step2 i j); unfold raw42003step3 raw42003step2; decide +kernel
      have hl : raw42003step3Labels = raw42003step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42003step3 raw42003step3Labels = mixedMoment B raw42003step4 raw42003step4Labels := by
      have ha : raw42003step4 = raw42003step3 := by apply Matrix.ext; unfold raw42003step4 raw42003step3; decide +kernel
      have hl : raw42003step3Labels = labelEmbedding9 ∘ raw42003step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42003step3 raw42003step3Labels raw42003step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical42004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42004 raw42004Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw42004 raw42004Labels = mixedMoment B raw42004step0 raw42004step0Labels := by
      have hz : ∀ j, raw42004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42004step0 = (fun i j => raw42004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42004step0 raw42004; decide +kernel
      have hl : raw42004step0Labels = raw42004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42004 raw42004Labels permutation434 hz
    mixedMoment B raw42004step0 raw42004step0Labels = mixedMoment B raw42004step1 raw42004step1Labels := by
      have hz : ∀ j, raw42004step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42004step1 = (fun i j => raw42004step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42004step1 raw42004step0; decide +kernel
      have hl : raw42004step1Labels = raw42004step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42004step0 raw42004step0Labels permutation80 hz
    mixedMoment B raw42004step1 raw42004step1Labels = mixedMoment B raw42004step2 raw42004step2Labels := by
      have ha : raw42004step2 = (fun i j => raw42004step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42004step2 raw42004step1; decide +kernel
      have hl : raw42004step2Labels = raw42004step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42004step1 raw42004step1Labels permutation13 permutation4
    mixedMoment B raw42004step2 raw42004step2Labels = mixedMoment B raw42004step3 raw42004step3Labels := by
      have ha : raw42004step3 = -raw42004step2 := by apply Matrix.ext; change ∀ i j, raw42004step3 i j = -(raw42004step2 i j); unfold raw42004step3 raw42004step2; decide +kernel
      have hl : raw42004step3Labels = raw42004step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42004step3 raw42004step3Labels = mixedMoment B raw42004step4 raw42004step4Labels := by
      have ha : raw42004step4 = raw42004step3 := by apply Matrix.ext; unfold raw42004step4 raw42004step3; decide +kernel
      have hl : raw42004step3Labels = labelEmbedding1 ∘ raw42004step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42004step3 raw42004step3Labels raw42004step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3119 node3119Labels := by rfl

theorem canonical42005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42005 raw42005Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw42005 raw42005Labels = mixedMoment B raw42005step0 raw42005step0Labels := by
      have hz : ∀ j, raw42005 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42005step0 = (fun i j => raw42005 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42005step0 raw42005; decide +kernel
      have hl : raw42005step0Labels = raw42005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42005 raw42005Labels permutation434 hz
    mixedMoment B raw42005step0 raw42005step0Labels = mixedMoment B raw42005step1 raw42005step1Labels := by
      have hz : ∀ j, raw42005step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42005step1 = (fun i j => raw42005step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42005step1 raw42005step0; decide +kernel
      have hl : raw42005step1Labels = raw42005step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42005step0 raw42005step0Labels permutation80 hz
    mixedMoment B raw42005step1 raw42005step1Labels = mixedMoment B raw42005step2 raw42005step2Labels := by
      have ha : raw42005step2 = (fun i j => raw42005step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42005step2 raw42005step1; decide +kernel
      have hl : raw42005step2Labels = raw42005step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42005step1 raw42005step1Labels permutation8 permutation5
    mixedMoment B raw42005step2 raw42005step2Labels = mixedMoment B raw42005step3 raw42005step3Labels := by
      have ha : raw42005step3 = -raw42005step2 := by apply Matrix.ext; change ∀ i j, raw42005step3 i j = -(raw42005step2 i j); unfold raw42005step3 raw42005step2; decide +kernel
      have hl : raw42005step3Labels = raw42005step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42005step3 raw42005step3Labels = mixedMoment B raw42005step4 raw42005step4Labels := by
      have ha : raw42005step4 = raw42005step3 := by apply Matrix.ext; unfold raw42005step4 raw42005step3; decide +kernel
      have hl : raw42005step3Labels = labelEmbedding9 ∘ raw42005step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42005step3 raw42005step3Labels raw42005step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical42006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42006 raw42006Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw42006 raw42006Labels = mixedMoment B raw42006step0 raw42006step0Labels := by
      have hz : ∀ j, raw42006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42006step0 = (fun i j => raw42006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42006step0 raw42006; decide +kernel
      have hl : raw42006step0Labels = raw42006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42006 raw42006Labels permutation434 hz
    mixedMoment B raw42006step0 raw42006step0Labels = mixedMoment B raw42006step1 raw42006step1Labels := by
      have hz : ∀ j, raw42006step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42006step1 = (fun i j => raw42006step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42006step1 raw42006step0; decide +kernel
      have hl : raw42006step1Labels = raw42006step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42006step0 raw42006step0Labels permutation80 hz
    mixedMoment B raw42006step1 raw42006step1Labels = mixedMoment B raw42006step2 raw42006step2Labels := by
      have ha : raw42006step2 = (fun i j => raw42006step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42006step2 raw42006step1; decide +kernel
      have hl : raw42006step2Labels = raw42006step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42006step1 raw42006step1Labels permutation12 permutation4
    mixedMoment B raw42006step2 raw42006step2Labels = mixedMoment B raw42006step3 raw42006step3Labels := by
      have ha : raw42006step3 = -raw42006step2 := by apply Matrix.ext; change ∀ i j, raw42006step3 i j = -(raw42006step2 i j); unfold raw42006step3 raw42006step2; decide +kernel
      have hl : raw42006step3Labels = raw42006step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42006step3 raw42006step3Labels = mixedMoment B raw42006step4 raw42006step4Labels := by
      have ha : raw42006step4 = raw42006step3 := by apply Matrix.ext; unfold raw42006step4 raw42006step3; decide +kernel
      have hl : raw42006step3Labels = labelEmbedding1 ∘ raw42006step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42006step3 raw42006step3Labels raw42006step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3055 node3055Labels := by rfl

theorem canonical42007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42007 raw42007Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw42007 raw42007Labels = mixedMoment B raw42007step0 raw42007step0Labels := by
      have hz : ∀ j, raw42007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42007step0 = (fun i j => raw42007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42007step0 raw42007; decide +kernel
      have hl : raw42007step0Labels = raw42007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42007 raw42007Labels permutation434 hz
    mixedMoment B raw42007step0 raw42007step0Labels = mixedMoment B raw42007step1 raw42007step1Labels := by
      have hz : ∀ j, raw42007step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42007step1 = (fun i j => raw42007step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42007step1 raw42007step0; decide +kernel
      have hl : raw42007step1Labels = raw42007step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42007step0 raw42007step0Labels permutation80 hz
    mixedMoment B raw42007step1 raw42007step1Labels = mixedMoment B raw42007step2 raw42007step2Labels := by
      have ha : raw42007step2 = (fun i j => raw42007step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42007step2 raw42007step1; decide +kernel
      have hl : raw42007step2Labels = raw42007step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42007step1 raw42007step1Labels permutation12 permutation5
    mixedMoment B raw42007step2 raw42007step2Labels = mixedMoment B raw42007step3 raw42007step3Labels := by
      have ha : raw42007step3 = -raw42007step2 := by apply Matrix.ext; change ∀ i j, raw42007step3 i j = -(raw42007step2 i j); unfold raw42007step3 raw42007step2; decide +kernel
      have hl : raw42007step3Labels = raw42007step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42007step3 raw42007step3Labels = mixedMoment B raw42007step4 raw42007step4Labels := by
      have ha : raw42007step4 = raw42007step3 := by apply Matrix.ext; unfold raw42007step4 raw42007step3; decide +kernel
      have hl : raw42007step3Labels = labelEmbedding9 ∘ raw42007step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42007step3 raw42007step3Labels raw42007step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

theorem canonical42008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42008 raw42008Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw42008 raw42008Labels = mixedMoment B raw42008step0 raw42008step0Labels := by
      have hz : ∀ j, raw42008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42008step0 = (fun i j => raw42008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42008step0 raw42008; decide +kernel
      have hl : raw42008step0Labels = raw42008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42008 raw42008Labels permutation346 hz
    mixedMoment B raw42008step0 raw42008step0Labels = mixedMoment B raw42008step1 raw42008step1Labels := by
      have ha : raw42008step1 = (fun i j => raw42008step0 (permutation55 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42008step1 raw42008step0; decide +kernel
      have hl : raw42008step1Labels = raw42008step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42008step0 raw42008step0Labels permutation55 permutation4
    mixedMoment B raw42008step1 raw42008step1Labels = mixedMoment B raw42008step2 raw42008step2Labels := by
      have ha : raw42008step2 = -raw42008step1 := by apply Matrix.ext; change ∀ i j, raw42008step2 i j = -(raw42008step1 i j); unfold raw42008step2 raw42008step1; decide +kernel
      have hl : raw42008step2Labels = raw42008step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42008step2 raw42008step2Labels = mixedMoment B raw42008step3 raw42008step3Labels := by
      have ha : raw42008step3 = raw42008step2 := by apply Matrix.ext; unfold raw42008step3 raw42008step2; decide +kernel
      have hl : raw42008step2Labels = labelEmbedding1 ∘ raw42008step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42008step2 raw42008step2Labels raw42008step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical42009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42009 raw42009Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw42009 raw42009Labels = mixedMoment B raw42009step0 raw42009step0Labels := by
      have hz : ∀ j, raw42009 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42009step0 = (fun i j => raw42009 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42009step0 raw42009; decide +kernel
      have hl : raw42009step0Labels = raw42009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42009 raw42009Labels permutation346 hz
    mixedMoment B raw42009step0 raw42009step0Labels = mixedMoment B raw42009step1 raw42009step1Labels := by
      have ha : raw42009step1 = (fun i j => raw42009step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42009step1 raw42009step0; decide +kernel
      have hl : raw42009step1Labels = raw42009step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42009step0 raw42009step0Labels permutation50 permutation5
    mixedMoment B raw42009step1 raw42009step1Labels = mixedMoment B raw42009step2 raw42009step2Labels := by
      have ha : raw42009step2 = -raw42009step1 := by apply Matrix.ext; change ∀ i j, raw42009step2 i j = -(raw42009step1 i j); unfold raw42009step2 raw42009step1; decide +kernel
      have hl : raw42009step2Labels = raw42009step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42009step2 raw42009step2Labels = mixedMoment B raw42009step3 raw42009step3Labels := by
      have ha : raw42009step3 = raw42009step2 := by apply Matrix.ext; unfold raw42009step3 raw42009step2; decide +kernel
      have hl : raw42009step2Labels = labelEmbedding9 ∘ raw42009step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42009step2 raw42009step2Labels raw42009step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical42010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42010 raw42010Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw42010 raw42010Labels = mixedMoment B raw42010step0 raw42010step0Labels := by
      have hz : ∀ j, raw42010 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42010step0 = (fun i j => raw42010 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42010step0 raw42010; decide +kernel
      have hl : raw42010step0Labels = raw42010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42010 raw42010Labels permutation346 hz
    mixedMoment B raw42010step0 raw42010step0Labels = mixedMoment B raw42010step1 raw42010step1Labels := by
      have ha : raw42010step1 = (fun i j => raw42010step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42010step1 raw42010step0; decide +kernel
      have hl : raw42010step1Labels = raw42010step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42010step0 raw42010step0Labels permutation40 permutation4
    mixedMoment B raw42010step1 raw42010step1Labels = mixedMoment B raw42010step2 raw42010step2Labels := by
      have ha : raw42010step2 = -raw42010step1 := by apply Matrix.ext; change ∀ i j, raw42010step2 i j = -(raw42010step1 i j); unfold raw42010step2 raw42010step1; decide +kernel
      have hl : raw42010step2Labels = raw42010step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42010step2 raw42010step2Labels = mixedMoment B raw42010step3 raw42010step3Labels := by
      have ha : raw42010step3 = raw42010step2 := by apply Matrix.ext; unfold raw42010step3 raw42010step2; decide +kernel
      have hl : raw42010step2Labels = labelEmbedding1 ∘ raw42010step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42010step2 raw42010step2Labels raw42010step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3078 node3078Labels := by rfl

theorem canonical42011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42011 raw42011Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw42011 raw42011Labels = mixedMoment B raw42011step0 raw42011step0Labels := by
      have hz : ∀ j, raw42011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42011step0 = (fun i j => raw42011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42011step0 raw42011; decide +kernel
      have hl : raw42011step0Labels = raw42011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42011 raw42011Labels permutation346 hz
    mixedMoment B raw42011step0 raw42011step0Labels = mixedMoment B raw42011step1 raw42011step1Labels := by
      have ha : raw42011step1 = (fun i j => raw42011step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42011step1 raw42011step0; decide +kernel
      have hl : raw42011step1Labels = raw42011step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42011step0 raw42011step0Labels permutation40 permutation5
    mixedMoment B raw42011step1 raw42011step1Labels = mixedMoment B raw42011step2 raw42011step2Labels := by
      have ha : raw42011step2 = -raw42011step1 := by apply Matrix.ext; change ∀ i j, raw42011step2 i j = -(raw42011step1 i j); unfold raw42011step2 raw42011step1; decide +kernel
      have hl : raw42011step2Labels = raw42011step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42011step2 raw42011step2Labels = mixedMoment B raw42011step3 raw42011step3Labels := by
      have ha : raw42011step3 = raw42011step2 := by apply Matrix.ext; unfold raw42011step3 raw42011step2; decide +kernel
      have hl : raw42011step2Labels = labelEmbedding9 ∘ raw42011step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42011step2 raw42011step2Labels raw42011step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

theorem canonical42012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42012 raw42012Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw42012 raw42012Labels = mixedMoment B raw42012step0 raw42012step0Labels := by
      have hz : ∀ j, raw42012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42012step0 = (fun i j => raw42012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42012step0 raw42012; decide +kernel
      have hl : raw42012step0Labels = raw42012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42012 raw42012Labels permutation346 hz
    mixedMoment B raw42012step0 raw42012step0Labels = mixedMoment B raw42012step1 raw42012step1Labels := by
      have ha : raw42012step1 = (fun i j => raw42012step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42012step1 raw42012step0; decide +kernel
      have hl : raw42012step1Labels = raw42012step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42012step0 raw42012step0Labels permutation41 permutation4
    mixedMoment B raw42012step1 raw42012step1Labels = mixedMoment B raw42012step2 raw42012step2Labels := by
      have ha : raw42012step2 = -raw42012step1 := by apply Matrix.ext; change ∀ i j, raw42012step2 i j = -(raw42012step1 i j); unfold raw42012step2 raw42012step1; decide +kernel
      have hl : raw42012step2Labels = raw42012step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42012step2 raw42012step2Labels = mixedMoment B raw42012step3 raw42012step3Labels := by
      have ha : raw42012step3 = raw42012step2 := by apply Matrix.ext; unfold raw42012step3 raw42012step2; decide +kernel
      have hl : raw42012step2Labels = labelEmbedding1 ∘ raw42012step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42012step2 raw42012step2Labels raw42012step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3099 node3099Labels := by rfl

theorem canonical42013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42013 raw42013Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw42013 raw42013Labels = mixedMoment B raw42013step0 raw42013step0Labels := by
      have hz : ∀ j, raw42013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42013step0 = (fun i j => raw42013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42013step0 raw42013; decide +kernel
      have hl : raw42013step0Labels = raw42013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42013 raw42013Labels permutation346 hz
    mixedMoment B raw42013step0 raw42013step0Labels = mixedMoment B raw42013step1 raw42013step1Labels := by
      have ha : raw42013step1 = (fun i j => raw42013step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42013step1 raw42013step0; decide +kernel
      have hl : raw42013step1Labels = raw42013step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42013step0 raw42013step0Labels permutation38 permutation5
    mixedMoment B raw42013step1 raw42013step1Labels = mixedMoment B raw42013step2 raw42013step2Labels := by
      have ha : raw42013step2 = -raw42013step1 := by apply Matrix.ext; change ∀ i j, raw42013step2 i j = -(raw42013step1 i j); unfold raw42013step2 raw42013step1; decide +kernel
      have hl : raw42013step2Labels = raw42013step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42013step2 raw42013step2Labels = mixedMoment B raw42013step3 raw42013step3Labels := by
      have ha : raw42013step3 = raw42013step2 := by apply Matrix.ext; unfold raw42013step3 raw42013step2; decide +kernel
      have hl : raw42013step2Labels = labelEmbedding9 ∘ raw42013step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42013step2 raw42013step2Labels raw42013step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical42014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42014 raw42014Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw42014 raw42014Labels = mixedMoment B raw42014step0 raw42014step0Labels := by
      have ha : raw42014step0 = (fun i j => raw42014 (permutation217 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42014step0 raw42014; decide +kernel
      have hl : raw42014step0Labels = raw42014Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42014 raw42014Labels permutation217 permutation4
    mixedMoment B raw42014step0 raw42014step0Labels = mixedMoment B raw42014step1 raw42014step1Labels := by
      have ha : raw42014step1 = -raw42014step0 := by apply Matrix.ext; change ∀ i j, raw42014step1 i j = -(raw42014step0 i j); unfold raw42014step1 raw42014step0; decide +kernel
      have hl : raw42014step1Labels = raw42014step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42014step1 raw42014step1Labels = mixedMoment B raw42014step2 raw42014step2Labels := by
      have ha : raw42014step2 = raw42014step1 := by apply Matrix.ext; unfold raw42014step2 raw42014step1; decide +kernel
      have hl : raw42014step1Labels = labelEmbedding1 ∘ raw42014step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42014step1 raw42014step1Labels raw42014step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

theorem canonical42015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42015 raw42015Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw42015 raw42015Labels = mixedMoment B raw42015step0 raw42015step0Labels := by
      have ha : raw42015step0 = (fun i j => raw42015 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42015step0 raw42015; decide +kernel
      have hl : raw42015step0Labels = raw42015Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42015 raw42015Labels permutation212 permutation5
    mixedMoment B raw42015step0 raw42015step0Labels = mixedMoment B raw42015step1 raw42015step1Labels := by
      have ha : raw42015step1 = -raw42015step0 := by apply Matrix.ext; change ∀ i j, raw42015step1 i j = -(raw42015step0 i j); unfold raw42015step1 raw42015step0; decide +kernel
      have hl : raw42015step1Labels = raw42015step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42015step1 raw42015step1Labels = mixedMoment B raw42015step2 raw42015step2Labels := by
      have ha : raw42015step2 = raw42015step1 := by apply Matrix.ext; unfold raw42015step2 raw42015step1; decide +kernel
      have hl : raw42015step1Labels = labelEmbedding9 ∘ raw42015step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42015step1 raw42015step1Labels raw42015step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical42016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42016 raw42016Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw42016 raw42016Labels = mixedMoment B raw42016step0 raw42016step0Labels := by
      have hz : ∀ j, raw42016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42016step0 = (fun i j => raw42016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42016step0 raw42016; decide +kernel
      have hl : raw42016step0Labels = raw42016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42016 raw42016Labels permutation434 hz
    mixedMoment B raw42016step0 raw42016step0Labels = mixedMoment B raw42016step1 raw42016step1Labels := by
      have hz : ∀ j, raw42016step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42016step1 = (fun i j => raw42016step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42016step1 raw42016step0; decide +kernel
      have hl : raw42016step1Labels = raw42016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42016step0 raw42016step0Labels permutation80 hz
    mixedMoment B raw42016step1 raw42016step1Labels = mixedMoment B raw42016step2 raw42016step2Labels := by
      have ha : raw42016step2 = (fun i j => raw42016step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42016step2 raw42016step1; decide +kernel
      have hl : raw42016step2Labels = raw42016step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42016step1 raw42016step1Labels permutation13 permutation4
    mixedMoment B raw42016step2 raw42016step2Labels = mixedMoment B raw42016step3 raw42016step3Labels := by
      have ha : raw42016step3 = -raw42016step2 := by apply Matrix.ext; change ∀ i j, raw42016step3 i j = -(raw42016step2 i j); unfold raw42016step3 raw42016step2; decide +kernel
      have hl : raw42016step3Labels = raw42016step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42016step3 raw42016step3Labels = mixedMoment B raw42016step4 raw42016step4Labels := by
      have ha : raw42016step4 = raw42016step3 := by apply Matrix.ext; unfold raw42016step4 raw42016step3; decide +kernel
      have hl : raw42016step3Labels = labelEmbedding1 ∘ raw42016step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42016step3 raw42016step3Labels raw42016step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3052 node3052Labels := by rfl

theorem canonical42017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42017 raw42017Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw42017 raw42017Labels = mixedMoment B raw42017step0 raw42017step0Labels := by
      have hz : ∀ j, raw42017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42017step0 = (fun i j => raw42017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42017step0 raw42017; decide +kernel
      have hl : raw42017step0Labels = raw42017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42017 raw42017Labels permutation434 hz
    mixedMoment B raw42017step0 raw42017step0Labels = mixedMoment B raw42017step1 raw42017step1Labels := by
      have hz : ∀ j, raw42017step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42017step1 = (fun i j => raw42017step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42017step1 raw42017step0; decide +kernel
      have hl : raw42017step1Labels = raw42017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42017step0 raw42017step0Labels permutation80 hz
    mixedMoment B raw42017step1 raw42017step1Labels = mixedMoment B raw42017step2 raw42017step2Labels := by
      have ha : raw42017step2 = (fun i j => raw42017step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42017step2 raw42017step1; decide +kernel
      have hl : raw42017step2Labels = raw42017step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42017step1 raw42017step1Labels permutation16 permutation6
    mixedMoment B raw42017step2 raw42017step2Labels = mixedMoment B raw42017step3 raw42017step3Labels := by
      have ha : raw42017step3 = -raw42017step2 := by apply Matrix.ext; change ∀ i j, raw42017step3 i j = -(raw42017step2 i j); unfold raw42017step3 raw42017step2; decide +kernel
      have hl : raw42017step3Labels = raw42017step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5276 node5276Labels := by rfl

theorem canonical42018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42018 raw42018Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw42018 raw42018Labels = mixedMoment B raw42018step0 raw42018step0Labels := by
      have hz : ∀ j, raw42018 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42018step0 = (fun i j => raw42018 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42018step0 raw42018; decide +kernel
      have hl : raw42018step0Labels = raw42018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42018 raw42018Labels permutation346 hz
    mixedMoment B raw42018step0 raw42018step0Labels = mixedMoment B raw42018step1 raw42018step1Labels := by
      have ha : raw42018step1 = (fun i j => raw42018step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42018step1 raw42018step0; decide +kernel
      have hl : raw42018step1Labels = raw42018step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42018step0 raw42018step0Labels permutation41 permutation4
    mixedMoment B raw42018step1 raw42018step1Labels = mixedMoment B raw42018step2 raw42018step2Labels := by
      have ha : raw42018step2 = -raw42018step1 := by apply Matrix.ext; change ∀ i j, raw42018step2 i j = -(raw42018step1 i j); unfold raw42018step2 raw42018step1; decide +kernel
      have hl : raw42018step2Labels = raw42018step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42018step2 raw42018step2Labels = mixedMoment B raw42018step3 raw42018step3Labels := by
      have ha : raw42018step3 = raw42018step2 := by apply Matrix.ext; unfold raw42018step3 raw42018step2; decide +kernel
      have hl : raw42018step2Labels = labelEmbedding1 ∘ raw42018step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42018step2 raw42018step2Labels raw42018step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

theorem canonical42019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42019 raw42019Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw42019 raw42019Labels = mixedMoment B raw42019step0 raw42019step0Labels := by
      have hz : ∀ j, raw42019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42019step0 = (fun i j => raw42019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42019step0 raw42019; decide +kernel
      have hl : raw42019step0Labels = raw42019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42019 raw42019Labels permutation346 hz
    mixedMoment B raw42019step0 raw42019step0Labels = mixedMoment B raw42019step1 raw42019step1Labels := by
      have ha : raw42019step1 = (fun i j => raw42019step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42019step1 raw42019step0; decide +kernel
      have hl : raw42019step1Labels = raw42019step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42019step0 raw42019step0Labels permutation77 permutation6
    mixedMoment B raw42019step1 raw42019step1Labels = mixedMoment B raw42019step2 raw42019step2Labels := by
      have ha : raw42019step2 = -raw42019step1 := by apply Matrix.ext; change ∀ i j, raw42019step2 i j = -(raw42019step1 i j); unfold raw42019step2 raw42019step1; decide +kernel
      have hl : raw42019step2Labels = raw42019step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5270 node5270Labels := by rfl

theorem canonical42020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42020 raw42020Labels = mixedMoment B node1 node1Labels := by
  calc
    mixedMoment B raw42020 raw42020Labels = mixedMoment B raw42020step0 raw42020step0Labels := by
      have hz : ∀ j, raw42020 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42020step0 = (fun i j => raw42020 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42020step0 raw42020; decide +kernel
      have hl : raw42020step0Labels = raw42020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42020 raw42020Labels permutation520 hz
    mixedMoment B raw42020step0 raw42020step0Labels = mixedMoment B raw42020step1 raw42020step1Labels := by
      have hz : ∀ j, raw42020step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42020step1 = (fun i j => raw42020step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42020step1 raw42020step0; decide +kernel
      have hl : raw42020step1Labels = raw42020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42020step0 raw42020step0Labels permutation104 hz
    mixedMoment B raw42020step1 raw42020step1Labels = mixedMoment B raw42020step2 raw42020step2Labels := by
      have hz : ∀ j, raw42020step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw42020step2 = (fun i j => raw42020step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw42020step2 raw42020step1; decide +kernel
      have hl : raw42020step2Labels = raw42020step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42020step1 raw42020step1Labels permutation20 hz
    mixedMoment B raw42020step2 raw42020step2Labels = mixedMoment B raw42020step3 raw42020step3Labels := by
      have hz : ∀ i, raw42020step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42020step3 = (fun i j => raw42020step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42020step3 raw42020step2; decide +kernel
      have hl : raw42020step3Labels = (fun j => raw42020step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42020step2 raw42020step2Labels permutation6 hz
    mixedMoment B raw42020step3 raw42020step3Labels = mixedMoment B raw42020step4 raw42020step4Labels := by
      have ha : raw42020step4 = (fun i j => raw42020step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw42020step4 raw42020step3; decide +kernel
      have hl : raw42020step4Labels = raw42020step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42020step3 raw42020step3Labels permutation7 permutation0
    mixedMoment B raw42020step4 raw42020step4Labels = mixedMoment B raw42020step5 raw42020step5Labels := by
      have ha : raw42020step5 = -raw42020step4 := by apply Matrix.ext; change ∀ i j, raw42020step5 i j = -(raw42020step4 i j); unfold raw42020step5 raw42020step4; decide +kernel
      have hl : raw42020step5Labels = raw42020step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42020step5 raw42020step5Labels = mixedMoment B raw42020step6 raw42020step6Labels := by
      have ha : raw42020step6 = raw42020step5 := by apply Matrix.ext; unfold raw42020step6 raw42020step5; decide +kernel
      have hl : raw42020step5Labels = labelEmbedding0 ∘ raw42020step6Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42020step5 raw42020step5Labels raw42020step6Labels labelEmbedding0 hl
    _ = mixedMoment B node1 node1Labels := by rfl

theorem canonical42021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42021 raw42021Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw42021 raw42021Labels = mixedMoment B raw42021step0 raw42021step0Labels := by
      have hz : ∀ j, raw42021 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42021step0 = (fun i j => raw42021 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42021step0 raw42021; decide +kernel
      have hl : raw42021step0Labels = raw42021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42021 raw42021Labels permutation520 hz
    mixedMoment B raw42021step0 raw42021step0Labels = mixedMoment B raw42021step1 raw42021step1Labels := by
      have hz : ∀ j, raw42021step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42021step1 = (fun i j => raw42021step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42021step1 raw42021step0; decide +kernel
      have hl : raw42021step1Labels = raw42021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42021step0 raw42021step0Labels permutation104 hz
    mixedMoment B raw42021step1 raw42021step1Labels = mixedMoment B raw42021step2 raw42021step2Labels := by
      have hz : ∀ j, raw42021step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw42021step2 = (fun i j => raw42021step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw42021step2 raw42021step1; decide +kernel
      have hl : raw42021step2Labels = raw42021step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42021step1 raw42021step1Labels permutation20 hz
    mixedMoment B raw42021step2 raw42021step2Labels = mixedMoment B raw42021step3 raw42021step3Labels := by
      have hz : ∀ i, raw42021step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42021step3 = (fun i j => raw42021step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42021step3 raw42021step2; decide +kernel
      have hl : raw42021step3Labels = (fun j => raw42021step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42021step2 raw42021step2Labels permutation6 hz
    mixedMoment B raw42021step3 raw42021step3Labels = mixedMoment B raw42021step4 raw42021step4Labels := by
      have ha : raw42021step4 = (fun i j => raw42021step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw42021step4 raw42021step3; decide +kernel
      have hl : raw42021step4Labels = raw42021step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42021step3 raw42021step3Labels permutation7 permutation0
    mixedMoment B raw42021step4 raw42021step4Labels = mixedMoment B raw42021step5 raw42021step5Labels := by
      have ha : raw42021step5 = -raw42021step4 := by apply Matrix.ext; change ∀ i j, raw42021step5 i j = -(raw42021step4 i j); unfold raw42021step5 raw42021step4; decide +kernel
      have hl : raw42021step5Labels = raw42021step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42021step5 raw42021step5Labels = mixedMoment B raw42021step6 raw42021step6Labels := by
      have ha : raw42021step6 = raw42021step5 := by apply Matrix.ext; unfold raw42021step6 raw42021step5; decide +kernel
      have hl : raw42021step5Labels = labelEmbedding3 ∘ raw42021step6Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42021step5 raw42021step5Labels raw42021step6Labels labelEmbedding3 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical42022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42022 raw42022Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw42022 raw42022Labels = mixedMoment B raw42022step0 raw42022step0Labels := by
      have hz : ∀ j, raw42022 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42022step0 = (fun i j => raw42022 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42022step0 raw42022; decide +kernel
      have hl : raw42022step0Labels = raw42022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42022 raw42022Labels permutation434 hz
    mixedMoment B raw42022step0 raw42022step0Labels = mixedMoment B raw42022step1 raw42022step1Labels := by
      have hz : ∀ j, raw42022step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42022step1 = (fun i j => raw42022step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42022step1 raw42022step0; decide +kernel
      have hl : raw42022step1Labels = raw42022step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42022step0 raw42022step0Labels permutation80 hz
    mixedMoment B raw42022step1 raw42022step1Labels = mixedMoment B raw42022step2 raw42022step2Labels := by
      have ha : raw42022step2 = (fun i j => raw42022step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42022step2 raw42022step1; decide +kernel
      have hl : raw42022step2Labels = raw42022step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42022step1 raw42022step1Labels permutation31 permutation4
    mixedMoment B raw42022step2 raw42022step2Labels = mixedMoment B raw42022step3 raw42022step3Labels := by
      have ha : raw42022step3 = raw42022step2 := by apply Matrix.ext; unfold raw42022step3 raw42022step2; decide +kernel
      have hl : raw42022step2Labels = labelEmbedding1 ∘ raw42022step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42022step2 raw42022step2Labels raw42022step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3112 node3112Labels := by rfl

theorem canonical42023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42023 raw42023Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw42023 raw42023Labels = mixedMoment B raw42023step0 raw42023step0Labels := by
      have hz : ∀ j, raw42023 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42023step0 = (fun i j => raw42023 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42023step0 raw42023; decide +kernel
      have hl : raw42023step0Labels = raw42023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42023 raw42023Labels permutation434 hz
    mixedMoment B raw42023step0 raw42023step0Labels = mixedMoment B raw42023step1 raw42023step1Labels := by
      have hz : ∀ j, raw42023step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42023step1 = (fun i j => raw42023step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42023step1 raw42023step0; decide +kernel
      have hl : raw42023step1Labels = raw42023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42023step0 raw42023step0Labels permutation80 hz
    mixedMoment B raw42023step1 raw42023step1Labels = mixedMoment B raw42023step2 raw42023step2Labels := by
      have ha : raw42023step2 = (fun i j => raw42023step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42023step2 raw42023step1; decide +kernel
      have hl : raw42023step2Labels = raw42023step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42023step1 raw42023step1Labels permutation31 permutation5
    mixedMoment B raw42023step2 raw42023step2Labels = mixedMoment B raw42023step3 raw42023step3Labels := by
      have ha : raw42023step3 = raw42023step2 := by apply Matrix.ext; unfold raw42023step3 raw42023step2; decide +kernel
      have hl : raw42023step2Labels = labelEmbedding9 ∘ raw42023step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42023step2 raw42023step2Labels raw42023step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

theorem canonical42024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42024 raw42024Labels = mixedMoment B node4 node4Labels := by
  calc
    mixedMoment B raw42024 raw42024Labels = mixedMoment B raw42024step0 raw42024step0Labels := by
      have hz : ∀ j, raw42024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42024step0 = (fun i j => raw42024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42024step0 raw42024; decide +kernel
      have hl : raw42024step0Labels = raw42024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42024 raw42024Labels permutation434 hz
    mixedMoment B raw42024step0 raw42024step0Labels = mixedMoment B raw42024step1 raw42024step1Labels := by
      have hz : ∀ j, raw42024step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42024step1 = (fun i j => raw42024step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42024step1 raw42024step0; decide +kernel
      have hl : raw42024step1Labels = raw42024step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42024step0 raw42024step0Labels permutation80 hz
    mixedMoment B raw42024step1 raw42024step1Labels = mixedMoment B raw42024step2 raw42024step2Labels := by
      have hz : ∀ i, raw42024step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42024step2 = (fun i j => raw42024step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42024step2 raw42024step1; decide +kernel
      have hl : raw42024step2Labels = (fun j => raw42024step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42024step1 raw42024step1Labels permutation6 hz
    mixedMoment B raw42024step2 raw42024step2Labels = mixedMoment B raw42024step3 raw42024step3Labels := by
      have ha : raw42024step3 = raw42024step2 := by apply Matrix.ext; unfold raw42024step3 raw42024step2; decide +kernel
      have hl : raw42024step2Labels = labelEmbedding0 ∘ raw42024step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42024step2 raw42024step2Labels raw42024step3Labels labelEmbedding0 hl
    _ = mixedMoment B node4 node4Labels := by rfl

theorem canonical42025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42025 raw42025Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw42025 raw42025Labels = mixedMoment B raw42025step0 raw42025step0Labels := by
      have hz : ∀ j, raw42025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42025step0 = (fun i j => raw42025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42025step0 raw42025; decide +kernel
      have hl : raw42025step0Labels = raw42025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42025 raw42025Labels permutation434 hz
    mixedMoment B raw42025step0 raw42025step0Labels = mixedMoment B raw42025step1 raw42025step1Labels := by
      have hz : ∀ j, raw42025step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42025step1 = (fun i j => raw42025step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42025step1 raw42025step0; decide +kernel
      have hl : raw42025step1Labels = raw42025step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42025step0 raw42025step0Labels permutation80 hz
    mixedMoment B raw42025step1 raw42025step1Labels = mixedMoment B raw42025step2 raw42025step2Labels := by
      have hz : ∀ i, raw42025step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42025step2 = (fun i j => raw42025step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42025step2 raw42025step1; decide +kernel
      have hl : raw42025step2Labels = (fun j => raw42025step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42025step1 raw42025step1Labels permutation6 hz
    mixedMoment B raw42025step2 raw42025step2Labels = mixedMoment B raw42025step3 raw42025step3Labels := by
      have ha : raw42025step3 = raw42025step2 := by apply Matrix.ext; unfold raw42025step3 raw42025step2; decide +kernel
      have hl : raw42025step2Labels = labelEmbedding3 ∘ raw42025step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42025step2 raw42025step2Labels raw42025step3Labels labelEmbedding3 hl
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical42026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42026 raw42026Labels = mixedMoment B node4006 node4006Labels := by
  calc
    mixedMoment B raw42026 raw42026Labels = mixedMoment B raw42026step0 raw42026step0Labels := by
      have hz : ∀ j, raw42026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42026step0 = (fun i j => raw42026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42026step0 raw42026; decide +kernel
      have hl : raw42026step0Labels = raw42026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42026 raw42026Labels permutation434 hz
    mixedMoment B raw42026step0 raw42026step0Labels = mixedMoment B raw42026step1 raw42026step1Labels := by
      have hz : ∀ j, raw42026step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42026step1 = (fun i j => raw42026step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42026step1 raw42026step0; decide +kernel
      have hl : raw42026step1Labels = raw42026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42026step0 raw42026step0Labels permutation80 hz
    mixedMoment B raw42026step1 raw42026step1Labels = mixedMoment B raw42026step2 raw42026step2Labels := by
      have ha : raw42026step2 = (fun i j => raw42026step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42026step2 raw42026step1; decide +kernel
      have hl : raw42026step2Labels = raw42026step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42026step1 raw42026step1Labels permutation31 permutation2
    mixedMoment B raw42026step2 raw42026step2Labels = mixedMoment B raw42026step3 raw42026step3Labels := by
      have ha : raw42026step3 = -raw42026step2 := by apply Matrix.ext; change ∀ i j, raw42026step3 i j = -(raw42026step2 i j); unfold raw42026step3 raw42026step2; decide +kernel
      have hl : raw42026step3Labels = raw42026step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42026step3 raw42026step3Labels = mixedMoment B raw42026step4 raw42026step4Labels := by
      have ha : raw42026step4 = raw42026step3 := by apply Matrix.ext; unfold raw42026step4 raw42026step3; decide +kernel
      have hl : raw42026step3Labels = labelEmbedding1 ∘ raw42026step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42026step3 raw42026step3Labels raw42026step4Labels labelEmbedding1 hl
    _ = mixedMoment B node4006 node4006Labels := by rfl

theorem canonical42027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42027 raw42027Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw42027 raw42027Labels = mixedMoment B raw42027step0 raw42027step0Labels := by
      have hz : ∀ j, raw42027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42027step0 = (fun i j => raw42027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42027step0 raw42027; decide +kernel
      have hl : raw42027step0Labels = raw42027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42027 raw42027Labels permutation434 hz
    mixedMoment B raw42027step0 raw42027step0Labels = mixedMoment B raw42027step1 raw42027step1Labels := by
      have hz : ∀ j, raw42027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42027step1 = (fun i j => raw42027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42027step1 raw42027step0; decide +kernel
      have hl : raw42027step1Labels = raw42027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42027step0 raw42027step0Labels permutation80 hz
    mixedMoment B raw42027step1 raw42027step1Labels = mixedMoment B raw42027step2 raw42027step2Labels := by
      have ha : raw42027step2 = (fun i j => raw42027step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42027step2 raw42027step1; decide +kernel
      have hl : raw42027step2Labels = raw42027step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42027step1 raw42027step1Labels permutation8 permutation3
    mixedMoment B raw42027step2 raw42027step2Labels = mixedMoment B raw42027step3 raw42027step3Labels := by
      have ha : raw42027step3 = raw42027step2 := by apply Matrix.ext; unfold raw42027step3 raw42027step2; decide +kernel
      have hl : raw42027step2Labels = labelEmbedding7 ∘ raw42027step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42027step2 raw42027step2Labels raw42027step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5413 node5413Labels := by rfl

theorem canonical42028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42028 raw42028Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw42028 raw42028Labels = mixedMoment B raw42028step0 raw42028step0Labels := by
      have hz : ∀ j, raw42028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42028step0 = (fun i j => raw42028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42028step0 raw42028; decide +kernel
      have hl : raw42028step0Labels = raw42028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42028 raw42028Labels permutation434 hz
    mixedMoment B raw42028step0 raw42028step0Labels = mixedMoment B raw42028step1 raw42028step1Labels := by
      have hz : ∀ j, raw42028step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42028step1 = (fun i j => raw42028step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42028step1 raw42028step0; decide +kernel
      have hl : raw42028step1Labels = raw42028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42028step0 raw42028step0Labels permutation80 hz
    mixedMoment B raw42028step1 raw42028step1Labels = mixedMoment B raw42028step2 raw42028step2Labels := by
      have ha : raw42028step2 = (fun i j => raw42028step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42028step2 raw42028step1; decide +kernel
      have hl : raw42028step2Labels = raw42028step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42028step1 raw42028step1Labels permutation25 permutation4
    mixedMoment B raw42028step2 raw42028step2Labels = mixedMoment B raw42028step3 raw42028step3Labels := by
      have ha : raw42028step3 = raw42028step2 := by apply Matrix.ext; unfold raw42028step3 raw42028step2; decide +kernel
      have hl : raw42028step2Labels = labelEmbedding1 ∘ raw42028step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42028step2 raw42028step2Labels raw42028step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

theorem canonical42029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42029 raw42029Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw42029 raw42029Labels = mixedMoment B raw42029step0 raw42029step0Labels := by
      have hz : ∀ j, raw42029 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42029step0 = (fun i j => raw42029 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42029step0 raw42029; decide +kernel
      have hl : raw42029step0Labels = raw42029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42029 raw42029Labels permutation434 hz
    mixedMoment B raw42029step0 raw42029step0Labels = mixedMoment B raw42029step1 raw42029step1Labels := by
      have hz : ∀ j, raw42029step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42029step1 = (fun i j => raw42029step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42029step1 raw42029step0; decide +kernel
      have hl : raw42029step1Labels = raw42029step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42029step0 raw42029step0Labels permutation80 hz
    mixedMoment B raw42029step1 raw42029step1Labels = mixedMoment B raw42029step2 raw42029step2Labels := by
      have ha : raw42029step2 = (fun i j => raw42029step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42029step2 raw42029step1; decide +kernel
      have hl : raw42029step2Labels = raw42029step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42029step1 raw42029step1Labels permutation25 permutation4
    mixedMoment B raw42029step2 raw42029step2Labels = mixedMoment B raw42029step3 raw42029step3Labels := by
      have ha : raw42029step3 = raw42029step2 := by apply Matrix.ext; unfold raw42029step3 raw42029step2; decide +kernel
      have hl : raw42029step2Labels = labelEmbedding10 ∘ raw42029step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42029step2 raw42029step2Labels raw42029step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical42030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42030 raw42030Labels = mixedMoment B node4035 node4035Labels := by
  calc
    mixedMoment B raw42030 raw42030Labels = mixedMoment B raw42030step0 raw42030step0Labels := by
      have hz : ∀ j, raw42030 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42030step0 = (fun i j => raw42030 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42030step0 raw42030; decide +kernel
      have hl : raw42030step0Labels = raw42030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42030 raw42030Labels permutation346 hz
    mixedMoment B raw42030step0 raw42030step0Labels = mixedMoment B raw42030step1 raw42030step1Labels := by
      have ha : raw42030step1 = (fun i j => raw42030step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42030step1 raw42030step0; decide +kernel
      have hl : raw42030step1Labels = raw42030step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42030step0 raw42030step0Labels permutation151 permutation2
    mixedMoment B raw42030step1 raw42030step1Labels = mixedMoment B raw42030step2 raw42030step2Labels := by
      have ha : raw42030step2 = -raw42030step1 := by apply Matrix.ext; change ∀ i j, raw42030step2 i j = -(raw42030step1 i j); unfold raw42030step2 raw42030step1; decide +kernel
      have hl : raw42030step2Labels = raw42030step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42030step2 raw42030step2Labels = mixedMoment B raw42030step3 raw42030step3Labels := by
      have ha : raw42030step3 = raw42030step2 := by apply Matrix.ext; unfold raw42030step3 raw42030step2; decide +kernel
      have hl : raw42030step2Labels = labelEmbedding1 ∘ raw42030step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42030step2 raw42030step2Labels raw42030step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4035 node4035Labels := by rfl

theorem canonical42031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42031 raw42031Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw42031 raw42031Labels = mixedMoment B raw42031step0 raw42031step0Labels := by
      have hz : ∀ j, raw42031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42031step0 = (fun i j => raw42031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42031step0 raw42031; decide +kernel
      have hl : raw42031step0Labels = raw42031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42031 raw42031Labels permutation346 hz
    mixedMoment B raw42031step0 raw42031step0Labels = mixedMoment B raw42031step1 raw42031step1Labels := by
      have ha : raw42031step1 = (fun i j => raw42031step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42031step1 raw42031step0; decide +kernel
      have hl : raw42031step1Labels = raw42031step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42031step0 raw42031step0Labels permutation32 permutation3
    mixedMoment B raw42031step1 raw42031step1Labels = mixedMoment B raw42031step2 raw42031step2Labels := by
      have ha : raw42031step2 = raw42031step1 := by apply Matrix.ext; unfold raw42031step2 raw42031step1; decide +kernel
      have hl : raw42031step1Labels = labelEmbedding7 ∘ raw42031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42031step1 raw42031step1Labels raw42031step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5409 node5409Labels := by rfl

theorem canonical42032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42032 raw42032Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw42032 raw42032Labels = mixedMoment B raw42032step0 raw42032step0Labels := by
      have hz : ∀ j, raw42032 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42032step0 = (fun i j => raw42032 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42032step0 raw42032; decide +kernel
      have hl : raw42032step0Labels = raw42032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42032 raw42032Labels permutation346 hz
    mixedMoment B raw42032step0 raw42032step0Labels = mixedMoment B raw42032step1 raw42032step1Labels := by
      have ha : raw42032step1 = (fun i j => raw42032step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42032step1 raw42032step0; decide +kernel
      have hl : raw42032step1Labels = raw42032step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42032step0 raw42032step0Labels permutation151 permutation2
    mixedMoment B raw42032step1 raw42032step1Labels = mixedMoment B raw42032step2 raw42032step2Labels := by
      have ha : raw42032step2 = -raw42032step1 := by apply Matrix.ext; change ∀ i j, raw42032step2 i j = -(raw42032step1 i j); unfold raw42032step2 raw42032step1; decide +kernel
      have hl : raw42032step2Labels = raw42032step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42032step2 raw42032step2Labels = mixedMoment B raw42032step3 raw42032step3Labels := by
      have ha : raw42032step3 = raw42032step2 := by apply Matrix.ext; unfold raw42032step3 raw42032step2; decide +kernel
      have hl : raw42032step2Labels = labelEmbedding1 ∘ raw42032step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42032step2 raw42032step2Labels raw42032step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3996 node3996Labels := by rfl

theorem canonical42033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42033 raw42033Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw42033 raw42033Labels = mixedMoment B raw42033step0 raw42033step0Labels := by
      have hz : ∀ j, raw42033 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42033step0 = (fun i j => raw42033 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42033step0 raw42033; decide +kernel
      have hl : raw42033step0Labels = raw42033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42033 raw42033Labels permutation346 hz
    mixedMoment B raw42033step0 raw42033step0Labels = mixedMoment B raw42033step1 raw42033step1Labels := by
      have ha : raw42033step1 = (fun i j => raw42033step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42033step1 raw42033step0; decide +kernel
      have hl : raw42033step1Labels = raw42033step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42033step0 raw42033step0Labels permutation32 permutation3
    mixedMoment B raw42033step1 raw42033step1Labels = mixedMoment B raw42033step2 raw42033step2Labels := by
      have ha : raw42033step2 = raw42033step1 := by apply Matrix.ext; unfold raw42033step2 raw42033step1; decide +kernel
      have hl : raw42033step1Labels = labelEmbedding7 ∘ raw42033step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42033step1 raw42033step1Labels raw42033step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical42034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42034 raw42034Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw42034 raw42034Labels = mixedMoment B raw42034step0 raw42034step0Labels := by
      have hz : ∀ j, raw42034 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42034step0 = (fun i j => raw42034 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42034step0 raw42034; decide +kernel
      have hl : raw42034step0Labels = raw42034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42034 raw42034Labels permutation346 hz
    mixedMoment B raw42034step0 raw42034step0Labels = mixedMoment B raw42034step1 raw42034step1Labels := by
      have ha : raw42034step1 = (fun i j => raw42034step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42034step1 raw42034step0; decide +kernel
      have hl : raw42034step1Labels = raw42034step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42034step0 raw42034step0Labels permutation151 permutation2
    mixedMoment B raw42034step1 raw42034step1Labels = mixedMoment B raw42034step2 raw42034step2Labels := by
      have ha : raw42034step2 = -raw42034step1 := by apply Matrix.ext; change ∀ i j, raw42034step2 i j = -(raw42034step1 i j); unfold raw42034step2 raw42034step1; decide +kernel
      have hl : raw42034step2Labels = raw42034step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42034step2 raw42034step2Labels = mixedMoment B raw42034step3 raw42034step3Labels := by
      have ha : raw42034step3 = raw42034step2 := by apply Matrix.ext; unfold raw42034step3 raw42034step2; decide +kernel
      have hl : raw42034step2Labels = labelEmbedding1 ∘ raw42034step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42034step2 raw42034step2Labels raw42034step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

theorem canonical42035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42035 raw42035Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw42035 raw42035Labels = mixedMoment B raw42035step0 raw42035step0Labels := by
      have hz : ∀ j, raw42035 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42035step0 = (fun i j => raw42035 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42035step0 raw42035; decide +kernel
      have hl : raw42035step0Labels = raw42035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42035 raw42035Labels permutation346 hz
    mixedMoment B raw42035step0 raw42035step0Labels = mixedMoment B raw42035step1 raw42035step1Labels := by
      have ha : raw42035step1 = (fun i j => raw42035step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42035step1 raw42035step0; decide +kernel
      have hl : raw42035step1Labels = raw42035step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42035step0 raw42035step0Labels permutation32 permutation3
    mixedMoment B raw42035step1 raw42035step1Labels = mixedMoment B raw42035step2 raw42035step2Labels := by
      have ha : raw42035step2 = raw42035step1 := by apply Matrix.ext; unfold raw42035step2 raw42035step1; decide +kernel
      have hl : raw42035step1Labels = labelEmbedding7 ∘ raw42035step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42035step1 raw42035step1Labels raw42035step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical42036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42036 raw42036Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw42036 raw42036Labels = mixedMoment B raw42036step0 raw42036step0Labels := by
      have hz : ∀ j, raw42036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42036step0 = (fun i j => raw42036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42036step0 raw42036; decide +kernel
      have hl : raw42036step0Labels = raw42036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42036 raw42036Labels permutation346 hz
    mixedMoment B raw42036step0 raw42036step0Labels = mixedMoment B raw42036step1 raw42036step1Labels := by
      have ha : raw42036step1 = (fun i j => raw42036step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42036step1 raw42036step0; decide +kernel
      have hl : raw42036step1Labels = raw42036step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42036step0 raw42036step0Labels permutation151 permutation2
    mixedMoment B raw42036step1 raw42036step1Labels = mixedMoment B raw42036step2 raw42036step2Labels := by
      have ha : raw42036step2 = -raw42036step1 := by apply Matrix.ext; change ∀ i j, raw42036step2 i j = -(raw42036step1 i j); unfold raw42036step2 raw42036step1; decide +kernel
      have hl : raw42036step2Labels = raw42036step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42036step2 raw42036step2Labels = mixedMoment B raw42036step3 raw42036step3Labels := by
      have ha : raw42036step3 = raw42036step2 := by apply Matrix.ext; unfold raw42036step3 raw42036step2; decide +kernel
      have hl : raw42036step2Labels = labelEmbedding1 ∘ raw42036step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42036step2 raw42036step2Labels raw42036step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3856 node3856Labels := by rfl

theorem canonical42037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42037 raw42037Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw42037 raw42037Labels = mixedMoment B raw42037step0 raw42037step0Labels := by
      have hz : ∀ j, raw42037 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42037step0 = (fun i j => raw42037 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42037step0 raw42037; decide +kernel
      have hl : raw42037step0Labels = raw42037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42037 raw42037Labels permutation346 hz
    mixedMoment B raw42037step0 raw42037step0Labels = mixedMoment B raw42037step1 raw42037step1Labels := by
      have ha : raw42037step1 = (fun i j => raw42037step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42037step1 raw42037step0; decide +kernel
      have hl : raw42037step1Labels = raw42037step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42037step0 raw42037step0Labels permutation32 permutation3
    mixedMoment B raw42037step1 raw42037step1Labels = mixedMoment B raw42037step2 raw42037step2Labels := by
      have ha : raw42037step2 = raw42037step1 := by apply Matrix.ext; unfold raw42037step2 raw42037step1; decide +kernel
      have hl : raw42037step1Labels = labelEmbedding7 ∘ raw42037step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42037step1 raw42037step1Labels raw42037step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical42038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42038 raw42038Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw42038 raw42038Labels = mixedMoment B raw42038step0 raw42038step0Labels := by
      have hz : ∀ j, raw42038 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42038step0 = (fun i j => raw42038 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42038step0 raw42038; decide +kernel
      have hl : raw42038step0Labels = raw42038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42038 raw42038Labels permutation346 hz
    mixedMoment B raw42038step0 raw42038step0Labels = mixedMoment B raw42038step1 raw42038step1Labels := by
      have ha : raw42038step1 = (fun i j => raw42038step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42038step1 raw42038step0; decide +kernel
      have hl : raw42038step1Labels = raw42038step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42038step0 raw42038step0Labels permutation145 permutation4
    mixedMoment B raw42038step1 raw42038step1Labels = mixedMoment B raw42038step2 raw42038step2Labels := by
      have ha : raw42038step2 = raw42038step1 := by apply Matrix.ext; unfold raw42038step2 raw42038step1; decide +kernel
      have hl : raw42038step1Labels = labelEmbedding1 ∘ raw42038step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42038step1 raw42038step1Labels raw42038step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2753 node2753Labels := by rfl

theorem canonical42039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42039 raw42039Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw42039 raw42039Labels = mixedMoment B raw42039step0 raw42039step0Labels := by
      have hz : ∀ j, raw42039 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42039step0 = (fun i j => raw42039 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42039step0 raw42039; decide +kernel
      have hl : raw42039step0Labels = raw42039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42039 raw42039Labels permutation346 hz
    mixedMoment B raw42039step0 raw42039step0Labels = mixedMoment B raw42039step1 raw42039step1Labels := by
      have ha : raw42039step1 = (fun i j => raw42039step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42039step1 raw42039step0; decide +kernel
      have hl : raw42039step1Labels = raw42039step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42039step0 raw42039step0Labels permutation145 permutation4
    mixedMoment B raw42039step1 raw42039step1Labels = mixedMoment B raw42039step2 raw42039step2Labels := by
      have ha : raw42039step2 = raw42039step1 := by apply Matrix.ext; unfold raw42039step2 raw42039step1; decide +kernel
      have hl : raw42039step1Labels = labelEmbedding10 ∘ raw42039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42039step1 raw42039step1Labels raw42039step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical42040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42040 raw42040Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw42040 raw42040Labels = mixedMoment B raw42040step0 raw42040step0Labels := by
      have hz : ∀ j, raw42040 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42040step0 = (fun i j => raw42040 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42040step0 raw42040; decide +kernel
      have hl : raw42040step0Labels = raw42040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42040 raw42040Labels permutation346 hz
    mixedMoment B raw42040step0 raw42040step0Labels = mixedMoment B raw42040step1 raw42040step1Labels := by
      have ha : raw42040step1 = (fun i j => raw42040step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42040step1 raw42040step0; decide +kernel
      have hl : raw42040step1Labels = raw42040step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42040step0 raw42040step0Labels permutation151 permutation4
    mixedMoment B raw42040step1 raw42040step1Labels = mixedMoment B raw42040step2 raw42040step2Labels := by
      have ha : raw42040step2 = raw42040step1 := by apply Matrix.ext; unfold raw42040step2 raw42040step1; decide +kernel
      have hl : raw42040step1Labels = labelEmbedding1 ∘ raw42040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42040step1 raw42040step1Labels raw42040step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3996 node3996Labels := by rfl

theorem canonical42041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42041 raw42041Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw42041 raw42041Labels = mixedMoment B raw42041step0 raw42041step0Labels := by
      have hz : ∀ j, raw42041 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42041step0 = (fun i j => raw42041 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42041step0 raw42041; decide +kernel
      have hl : raw42041step0Labels = raw42041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42041 raw42041Labels permutation346 hz
    mixedMoment B raw42041step0 raw42041step0Labels = mixedMoment B raw42041step1 raw42041step1Labels := by
      have ha : raw42041step1 = (fun i j => raw42041step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42041step1 raw42041step0; decide +kernel
      have hl : raw42041step1Labels = raw42041step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42041step0 raw42041step0Labels permutation32 permutation5
    mixedMoment B raw42041step1 raw42041step1Labels = mixedMoment B raw42041step2 raw42041step2Labels := by
      have ha : raw42041step2 = -raw42041step1 := by apply Matrix.ext; change ∀ i j, raw42041step2 i j = -(raw42041step1 i j); unfold raw42041step2 raw42041step1; decide +kernel
      have hl : raw42041step2Labels = raw42041step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42041step2 raw42041step2Labels = mixedMoment B raw42041step3 raw42041step3Labels := by
      have ha : raw42041step3 = raw42041step2 := by apply Matrix.ext; unfold raw42041step3 raw42041step2; decide +kernel
      have hl : raw42041step2Labels = labelEmbedding9 ∘ raw42041step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42041step2 raw42041step2Labels raw42041step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical42042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42042 raw42042Labels = mixedMoment B node3 node3Labels := by
  calc
    mixedMoment B raw42042 raw42042Labels = mixedMoment B raw42042step0 raw42042step0Labels := by
      have hz : ∀ j, raw42042 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42042step0 = (fun i j => raw42042 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42042step0 raw42042; decide +kernel
      have hl : raw42042step0Labels = raw42042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42042 raw42042Labels permutation346 hz
    mixedMoment B raw42042step0 raw42042step0Labels = mixedMoment B raw42042step1 raw42042step1Labels := by
      have hz : ∀ i, raw42042step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42042step1 = (fun i j => raw42042step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42042step1 raw42042step0; decide +kernel
      have hl : raw42042step1Labels = (fun j => raw42042step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42042step0 raw42042step0Labels permutation6 hz
    mixedMoment B raw42042step1 raw42042step1Labels = mixedMoment B raw42042step2 raw42042step2Labels := by
      have ha : raw42042step2 = raw42042step1 := by apply Matrix.ext; unfold raw42042step2 raw42042step1; decide +kernel
      have hl : raw42042step1Labels = labelEmbedding0 ∘ raw42042step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42042step1 raw42042step1Labels raw42042step2Labels labelEmbedding0 hl
    _ = mixedMoment B node3 node3Labels := by rfl

theorem canonical42043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42043 raw42043Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw42043 raw42043Labels = mixedMoment B raw42043step0 raw42043step0Labels := by
      have hz : ∀ j, raw42043 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42043step0 = (fun i j => raw42043 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42043step0 raw42043; decide +kernel
      have hl : raw42043step0Labels = raw42043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42043 raw42043Labels permutation346 hz
    mixedMoment B raw42043step0 raw42043step0Labels = mixedMoment B raw42043step1 raw42043step1Labels := by
      have hz : ∀ i, raw42043step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42043step1 = (fun i j => raw42043step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42043step1 raw42043step0; decide +kernel
      have hl : raw42043step1Labels = (fun j => raw42043step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42043step0 raw42043step0Labels permutation6 hz
    mixedMoment B raw42043step1 raw42043step1Labels = mixedMoment B raw42043step2 raw42043step2Labels := by
      have ha : raw42043step2 = raw42043step1 := by apply Matrix.ext; unfold raw42043step2 raw42043step1; decide +kernel
      have hl : raw42043step1Labels = labelEmbedding3 ∘ raw42043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42043step1 raw42043step1Labels raw42043step2Labels labelEmbedding3 hl
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical42044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42044 raw42044Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw42044 raw42044Labels = mixedMoment B raw42044step0 raw42044step0Labels := by
      have ha : raw42044step0 = (fun i j => raw42044 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42044step0 raw42044; decide +kernel
      have hl : raw42044step0Labels = raw42044Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42044 raw42044Labels permutation682 permutation2
    mixedMoment B raw42044step0 raw42044step0Labels = mixedMoment B raw42044step1 raw42044step1Labels := by
      have ha : raw42044step1 = -raw42044step0 := by apply Matrix.ext; change ∀ i j, raw42044step1 i j = -(raw42044step0 i j); unfold raw42044step1 raw42044step0; decide +kernel
      have hl : raw42044step1Labels = raw42044step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42044step1 raw42044step1Labels = mixedMoment B raw42044step2 raw42044step2Labels := by
      have ha : raw42044step2 = raw42044step1 := by apply Matrix.ext; unfold raw42044step2 raw42044step1; decide +kernel
      have hl : raw42044step1Labels = labelEmbedding1 ∘ raw42044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42044step1 raw42044step1Labels raw42044step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

theorem canonical42045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42045 raw42045Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw42045 raw42045Labels = mixedMoment B raw42045step0 raw42045step0Labels := by
      have ha : raw42045step0 = (fun i j => raw42045 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42045step0 raw42045; decide +kernel
      have hl : raw42045step0Labels = raw42045Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42045 raw42045Labels permutation152 permutation3
    mixedMoment B raw42045step0 raw42045step0Labels = mixedMoment B raw42045step1 raw42045step1Labels := by
      have ha : raw42045step1 = raw42045step0 := by apply Matrix.ext; unfold raw42045step1 raw42045step0; decide +kernel
      have hl : raw42045step0Labels = labelEmbedding7 ∘ raw42045step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42045step0 raw42045step0Labels raw42045step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical42046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42046 raw42046Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw42046 raw42046Labels = mixedMoment B raw42046step0 raw42046step0Labels := by
      have ha : raw42046step0 = (fun i j => raw42046 (permutation640 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42046step0 raw42046; decide +kernel
      have hl : raw42046step0Labels = raw42046Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42046 raw42046Labels permutation640 permutation4
    mixedMoment B raw42046step0 raw42046step0Labels = mixedMoment B raw42046step1 raw42046step1Labels := by
      have ha : raw42046step1 = raw42046step0 := by apply Matrix.ext; unfold raw42046step1 raw42046step0; decide +kernel
      have hl : raw42046step0Labels = labelEmbedding1 ∘ raw42046step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42046step0 raw42046step0Labels raw42046step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3977 node3977Labels := by rfl

theorem canonical42047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42047 raw42047Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw42047 raw42047Labels = mixedMoment B raw42047step0 raw42047step0Labels := by
      have ha : raw42047step0 = (fun i j => raw42047 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42047step0 raw42047; decide +kernel
      have hl : raw42047step0Labels = raw42047Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42047 raw42047Labels permutation160 permutation5
    mixedMoment B raw42047step0 raw42047step0Labels = mixedMoment B raw42047step1 raw42047step1Labels := by
      have ha : raw42047step1 = -raw42047step0 := by apply Matrix.ext; change ∀ i j, raw42047step1 i j = -(raw42047step0 i j); unfold raw42047step1 raw42047step0; decide +kernel
      have hl : raw42047step1Labels = raw42047step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42047step1 raw42047step1Labels = mixedMoment B raw42047step2 raw42047step2Labels := by
      have ha : raw42047step2 = raw42047step1 := by apply Matrix.ext; unfold raw42047step2 raw42047step1; decide +kernel
      have hl : raw42047step1Labels = labelEmbedding9 ∘ raw42047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42047step1 raw42047step1Labels raw42047step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2336 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2336) =
      Integer.Sparse.eval keyMomentRow2336 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2336).leftCharge (GramAssembly.key 2336).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3109) := by
    have ha : gramCharges (GramAssembly.key 2336).leftCharge (GramAssembly.key 2336).rightCharge = raw41984 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41984Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41984 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2336).leftCharge (GramAssembly.key 2336).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5271) := by
    have ha : gramCharges (GramAssembly.key 2336).leftCharge (GramAssembly.key 2336).rightCharge = raw41985 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41985Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41985 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2336).leftCharge (GramAssembly.key 2336).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2336).leftCharge (GramAssembly.key 2336).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2336, Integer.Sparse.eval]
  ring

theorem keyMoment2337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2337) =
      Integer.Sparse.eval keyMomentRow2337 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2337).leftCharge (GramAssembly.key 2337).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3039) := by
    have ha : gramCharges (GramAssembly.key 2337).leftCharge (GramAssembly.key 2337).rightCharge = raw41986 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41986Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41986 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2337).leftCharge (GramAssembly.key 2337).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5266) := by
    have ha : gramCharges (GramAssembly.key 2337).leftCharge (GramAssembly.key 2337).rightCharge = raw41987 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41987Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41987 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2337).leftCharge (GramAssembly.key 2337).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2337).leftCharge (GramAssembly.key 2337).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2337, Integer.Sparse.eval]
  ring

theorem keyMoment2338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2338) =
      Integer.Sparse.eval keyMomentRow2338 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2338).leftCharge (GramAssembly.key 2338).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3038) := by
    have ha : gramCharges (GramAssembly.key 2338).leftCharge (GramAssembly.key 2338).rightCharge = raw41988 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41988Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41988 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2338).leftCharge (GramAssembly.key 2338).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2338).leftCharge (GramAssembly.key 2338).rightCharge = raw41989 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41989Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41989 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2338).leftCharge (GramAssembly.key 2338).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2338).leftCharge (GramAssembly.key 2338).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2338, Integer.Sparse.eval]
  ring

theorem keyMoment2339 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2339) =
      Integer.Sparse.eval keyMomentRow2339 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2339).leftCharge (GramAssembly.key 2339).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3088) := by
    have ha : gramCharges (GramAssembly.key 2339).leftCharge (GramAssembly.key 2339).rightCharge = raw41990 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41990Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41990 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2339).leftCharge (GramAssembly.key 2339).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5259) := by
    have ha : gramCharges (GramAssembly.key 2339).leftCharge (GramAssembly.key 2339).rightCharge = raw41991 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41991Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41991 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2339).leftCharge (GramAssembly.key 2339).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2339).leftCharge (GramAssembly.key 2339).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2339, Integer.Sparse.eval]
  ring

theorem keyMoment2340 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2340) =
      Integer.Sparse.eval keyMomentRow2340 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2340).leftCharge (GramAssembly.key 2340).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3111) := by
    have ha : gramCharges (GramAssembly.key 2340).leftCharge (GramAssembly.key 2340).rightCharge = raw41992 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41992Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41992 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2340).leftCharge (GramAssembly.key 2340).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5273) := by
    have ha : gramCharges (GramAssembly.key 2340).leftCharge (GramAssembly.key 2340).rightCharge = raw41993 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41993Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41993 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2340).leftCharge (GramAssembly.key 2340).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2340).leftCharge (GramAssembly.key 2340).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2340, Integer.Sparse.eval]
  ring

theorem keyMoment2341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2341) =
      Integer.Sparse.eval keyMomentRow2341 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2341).leftCharge (GramAssembly.key 2341).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3037) := by
    have ha : gramCharges (GramAssembly.key 2341).leftCharge (GramAssembly.key 2341).rightCharge = raw41994 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41994Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41994 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2341).leftCharge (GramAssembly.key 2341).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2341).leftCharge (GramAssembly.key 2341).rightCharge = raw41995 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41995Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41995 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2341).leftCharge (GramAssembly.key 2341).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2341).leftCharge (GramAssembly.key 2341).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2341, Integer.Sparse.eval]
  ring

theorem keyMoment2342 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2342) =
      Integer.Sparse.eval keyMomentRow2342 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2342).leftCharge (GramAssembly.key 2342).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3065) := by
    have ha : gramCharges (GramAssembly.key 2342).leftCharge (GramAssembly.key 2342).rightCharge = raw41996 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41996Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41996 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2342).leftCharge (GramAssembly.key 2342).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5250) := by
    have ha : gramCharges (GramAssembly.key 2342).leftCharge (GramAssembly.key 2342).rightCharge = raw41997 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41997Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41997 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2342).leftCharge (GramAssembly.key 2342).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2342).leftCharge (GramAssembly.key 2342).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2342, Integer.Sparse.eval]
  ring

theorem keyMoment2343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2343) =
      Integer.Sparse.eval keyMomentRow2343 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2343).leftCharge (GramAssembly.key 2343).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3087) := by
    have ha : gramCharges (GramAssembly.key 2343).leftCharge (GramAssembly.key 2343).rightCharge = raw41998 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41998Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41998 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2343).leftCharge (GramAssembly.key 2343).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5257) := by
    have ha : gramCharges (GramAssembly.key 2343).leftCharge (GramAssembly.key 2343).rightCharge = raw41999 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41999Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41999 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2343).leftCharge (GramAssembly.key 2343).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2343).leftCharge (GramAssembly.key 2343).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2343, Integer.Sparse.eval]
  ring

theorem keyMoment2344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2344) =
      Integer.Sparse.eval keyMomentRow2344 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2344).leftCharge (GramAssembly.key 2344).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3064) := by
    have ha : gramCharges (GramAssembly.key 2344).leftCharge (GramAssembly.key 2344).rightCharge = raw42000 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42000Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42000 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2344).leftCharge (GramAssembly.key 2344).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2344).leftCharge (GramAssembly.key 2344).rightCharge = raw42001 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42001Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42001 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2344).leftCharge (GramAssembly.key 2344).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2344).leftCharge (GramAssembly.key 2344).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2344, Integer.Sparse.eval]
  ring

theorem keyMoment2345 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2345) =
      Integer.Sparse.eval keyMomentRow2345 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2345).leftCharge (GramAssembly.key 2345).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3103) := by
    have ha : gramCharges (GramAssembly.key 2345).leftCharge (GramAssembly.key 2345).rightCharge = raw42002 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42002Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42002 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2345).leftCharge (GramAssembly.key 2345).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5291) := by
    have ha : gramCharges (GramAssembly.key 2345).leftCharge (GramAssembly.key 2345).rightCharge = raw42003 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42003Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42003 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2345).leftCharge (GramAssembly.key 2345).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2345).leftCharge (GramAssembly.key 2345).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2345, Integer.Sparse.eval]
  ring

theorem keyMoment2346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2346) =
      Integer.Sparse.eval keyMomentRow2346 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2346).leftCharge (GramAssembly.key 2346).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3119) := by
    have ha : gramCharges (GramAssembly.key 2346).leftCharge (GramAssembly.key 2346).rightCharge = raw42004 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42004Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42004 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2346).leftCharge (GramAssembly.key 2346).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5304) := by
    have ha : gramCharges (GramAssembly.key 2346).leftCharge (GramAssembly.key 2346).rightCharge = raw42005 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42005Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42005 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2346).leftCharge (GramAssembly.key 2346).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2346).leftCharge (GramAssembly.key 2346).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2346, Integer.Sparse.eval]
  ring

theorem keyMoment2347 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2347) =
      Integer.Sparse.eval keyMomentRow2347 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2347).leftCharge (GramAssembly.key 2347).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3055) := by
    have ha : gramCharges (GramAssembly.key 2347).leftCharge (GramAssembly.key 2347).rightCharge = raw42006 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42006Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42006 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2347).leftCharge (GramAssembly.key 2347).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5300) := by
    have ha : gramCharges (GramAssembly.key 2347).leftCharge (GramAssembly.key 2347).rightCharge = raw42007 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42007Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42007 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2347).leftCharge (GramAssembly.key 2347).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2347).leftCharge (GramAssembly.key 2347).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2347, Integer.Sparse.eval]
  ring

theorem keyMoment2348 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2348) =
      Integer.Sparse.eval keyMomentRow2348 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2348).leftCharge (GramAssembly.key 2348).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3051) := by
    have ha : gramCharges (GramAssembly.key 2348).leftCharge (GramAssembly.key 2348).rightCharge = raw42008 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42008Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42008 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2348).leftCharge (GramAssembly.key 2348).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2348).leftCharge (GramAssembly.key 2348).rightCharge = raw42009 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42009Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42009 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2348).leftCharge (GramAssembly.key 2348).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2348).leftCharge (GramAssembly.key 2348).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2348, Integer.Sparse.eval]
  ring

theorem keyMoment2349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2349) =
      Integer.Sparse.eval keyMomentRow2349 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2349).leftCharge (GramAssembly.key 2349).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3078) := by
    have ha : gramCharges (GramAssembly.key 2349).leftCharge (GramAssembly.key 2349).rightCharge = raw42010 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42010Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42010 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2349).leftCharge (GramAssembly.key 2349).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5282) := by
    have ha : gramCharges (GramAssembly.key 2349).leftCharge (GramAssembly.key 2349).rightCharge = raw42011 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42011Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42011 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2349).leftCharge (GramAssembly.key 2349).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2349).leftCharge (GramAssembly.key 2349).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2349, Integer.Sparse.eval]
  ring

theorem keyMoment2350 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2350) =
      Integer.Sparse.eval keyMomentRow2350 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2350).leftCharge (GramAssembly.key 2350).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3099) := by
    have ha : gramCharges (GramAssembly.key 2350).leftCharge (GramAssembly.key 2350).rightCharge = raw42012 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42012Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42012 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2350).leftCharge (GramAssembly.key 2350).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5290) := by
    have ha : gramCharges (GramAssembly.key 2350).leftCharge (GramAssembly.key 2350).rightCharge = raw42013 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42013Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42013 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2350).leftCharge (GramAssembly.key 2350).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2350).leftCharge (GramAssembly.key 2350).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2350, Integer.Sparse.eval]
  ring

theorem keyMoment2351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2351) =
      Integer.Sparse.eval keyMomentRow2351 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2351).leftCharge (GramAssembly.key 2351).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3074) := by
    have ha : gramCharges (GramAssembly.key 2351).leftCharge (GramAssembly.key 2351).rightCharge = raw42014 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42014Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42014 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2351).leftCharge (GramAssembly.key 2351).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5281) := by
    have ha : gramCharges (GramAssembly.key 2351).leftCharge (GramAssembly.key 2351).rightCharge = raw42015 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42015Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42015 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2351).leftCharge (GramAssembly.key 2351).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2351).leftCharge (GramAssembly.key 2351).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2351, Integer.Sparse.eval]
  ring

theorem keyMoment2352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2352) =
      Integer.Sparse.eval keyMomentRow2352 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2352).leftCharge (GramAssembly.key 2352).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3052) := by
    have ha : gramCharges (GramAssembly.key 2352).leftCharge (GramAssembly.key 2352).rightCharge = raw42016 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42016Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42016 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2352).leftCharge (GramAssembly.key 2352).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5276) := by
    have ha : gramCharges (GramAssembly.key 2352).leftCharge (GramAssembly.key 2352).rightCharge = raw42017 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42017Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42017 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2352).leftCharge (GramAssembly.key 2352).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2352).leftCharge (GramAssembly.key 2352).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2352, Integer.Sparse.eval]
  ring

theorem keyMoment2353 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2353) =
      Integer.Sparse.eval keyMomentRow2353 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2353).leftCharge (GramAssembly.key 2353).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3075) := by
    have ha : gramCharges (GramAssembly.key 2353).leftCharge (GramAssembly.key 2353).rightCharge = raw42018 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42018Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42018 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2353).leftCharge (GramAssembly.key 2353).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5270) := by
    have ha : gramCharges (GramAssembly.key 2353).leftCharge (GramAssembly.key 2353).rightCharge = raw42019 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42019Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42019 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2353).leftCharge (GramAssembly.key 2353).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2353).leftCharge (GramAssembly.key 2353).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2353, Integer.Sparse.eval]
  ring

theorem keyMoment2354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2354) =
      Integer.Sparse.eval keyMomentRow2354 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2354).leftCharge (GramAssembly.key 2354).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1) := by
    have ha : gramCharges (GramAssembly.key 2354).leftCharge (GramAssembly.key 2354).rightCharge = raw42020 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42020Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42020 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2354).leftCharge (GramAssembly.key 2354).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4084) := by
    have ha : gramCharges (GramAssembly.key 2354).leftCharge (GramAssembly.key 2354).rightCharge = raw42021 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42021Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42021 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2354).leftCharge (GramAssembly.key 2354).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2354).leftCharge (GramAssembly.key 2354).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2354, Integer.Sparse.eval]
  ring

theorem keyMoment2355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2355) =
      Integer.Sparse.eval keyMomentRow2355 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2355).leftCharge (GramAssembly.key 2355).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3112) := by
    have ha : gramCharges (GramAssembly.key 2355).leftCharge (GramAssembly.key 2355).rightCharge = raw42022 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42022Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42022 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2355).leftCharge (GramAssembly.key 2355).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5274) := by
    have ha : gramCharges (GramAssembly.key 2355).leftCharge (GramAssembly.key 2355).rightCharge = raw42023 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42023Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42023 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2355).leftCharge (GramAssembly.key 2355).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2355).leftCharge (GramAssembly.key 2355).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2355, Integer.Sparse.eval]
  ring

theorem keyMoment2356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2356) =
      Integer.Sparse.eval keyMomentRow2356 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2356).leftCharge (GramAssembly.key 2356).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4) := by
    have ha : gramCharges (GramAssembly.key 2356).leftCharge (GramAssembly.key 2356).rightCharge = raw42024 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42024Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42024 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2356).leftCharge (GramAssembly.key 2356).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4092) := by
    have ha : gramCharges (GramAssembly.key 2356).leftCharge (GramAssembly.key 2356).rightCharge = raw42025 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42025Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42025 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2356).leftCharge (GramAssembly.key 2356).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2356).leftCharge (GramAssembly.key 2356).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2356, Integer.Sparse.eval]
  ring

theorem keyMoment2357 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2357) =
      Integer.Sparse.eval keyMomentRow2357 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2357).leftCharge (GramAssembly.key 2357).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4006) := by
    have ha : gramCharges (GramAssembly.key 2357).leftCharge (GramAssembly.key 2357).rightCharge = raw42026 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42026Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42026 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2357).leftCharge (GramAssembly.key 2357).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5413) := by
    have ha : gramCharges (GramAssembly.key 2357).leftCharge (GramAssembly.key 2357).rightCharge = raw42027 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42027Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42027 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2357).leftCharge (GramAssembly.key 2357).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2357).leftCharge (GramAssembly.key 2357).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2357, Integer.Sparse.eval]
  ring

theorem keyMoment2358 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2358) =
      Integer.Sparse.eval keyMomentRow2358 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2358).leftCharge (GramAssembly.key 2358).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2776) := by
    have ha : gramCharges (GramAssembly.key 2358).leftCharge (GramAssembly.key 2358).rightCharge = raw42028 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42028Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42028 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2358).leftCharge (GramAssembly.key 2358).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5302) := by
    have ha : gramCharges (GramAssembly.key 2358).leftCharge (GramAssembly.key 2358).rightCharge = raw42029 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42029Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42029 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2358).leftCharge (GramAssembly.key 2358).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2358).leftCharge (GramAssembly.key 2358).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2358, Integer.Sparse.eval]
  ring

theorem keyMoment2359 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2359) =
      Integer.Sparse.eval keyMomentRow2359 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2359).leftCharge (GramAssembly.key 2359).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4035) := by
    have ha : gramCharges (GramAssembly.key 2359).leftCharge (GramAssembly.key 2359).rightCharge = raw42030 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42030Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42030 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2359).leftCharge (GramAssembly.key 2359).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5409) := by
    have ha : gramCharges (GramAssembly.key 2359).leftCharge (GramAssembly.key 2359).rightCharge = raw42031 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42031Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42031 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2359).leftCharge (GramAssembly.key 2359).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2359).leftCharge (GramAssembly.key 2359).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2359, Integer.Sparse.eval]
  ring

theorem keyMoment2360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2360) =
      Integer.Sparse.eval keyMomentRow2360 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2360).leftCharge (GramAssembly.key 2360).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3996) := by
    have ha : gramCharges (GramAssembly.key 2360).leftCharge (GramAssembly.key 2360).rightCharge = raw42032 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42032Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42032 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2360).leftCharge (GramAssembly.key 2360).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5410) := by
    have ha : gramCharges (GramAssembly.key 2360).leftCharge (GramAssembly.key 2360).rightCharge = raw42033 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42033Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42033 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2360).leftCharge (GramAssembly.key 2360).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2360).leftCharge (GramAssembly.key 2360).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2360, Integer.Sparse.eval]
  ring

theorem keyMoment2361 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2361) =
      Integer.Sparse.eval keyMomentRow2361 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2361).leftCharge (GramAssembly.key 2361).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3883) := by
    have ha : gramCharges (GramAssembly.key 2361).leftCharge (GramAssembly.key 2361).rightCharge = raw42034 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42034Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42034 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2361).leftCharge (GramAssembly.key 2361).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5411) := by
    have ha : gramCharges (GramAssembly.key 2361).leftCharge (GramAssembly.key 2361).rightCharge = raw42035 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42035Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42035 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2361).leftCharge (GramAssembly.key 2361).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2361).leftCharge (GramAssembly.key 2361).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2361, Integer.Sparse.eval]
  ring

theorem keyMoment2362 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2362) =
      Integer.Sparse.eval keyMomentRow2362 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2362).leftCharge (GramAssembly.key 2362).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3856) := by
    have ha : gramCharges (GramAssembly.key 2362).leftCharge (GramAssembly.key 2362).rightCharge = raw42036 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42036Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42036 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2362).leftCharge (GramAssembly.key 2362).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5412) := by
    have ha : gramCharges (GramAssembly.key 2362).leftCharge (GramAssembly.key 2362).rightCharge = raw42037 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42037Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42037 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2362).leftCharge (GramAssembly.key 2362).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2362).leftCharge (GramAssembly.key 2362).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2362, Integer.Sparse.eval]
  ring

theorem keyMoment2363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2363) =
      Integer.Sparse.eval keyMomentRow2363 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2363).leftCharge (GramAssembly.key 2363).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2753) := by
    have ha : gramCharges (GramAssembly.key 2363).leftCharge (GramAssembly.key 2363).rightCharge = raw42038 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42038Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42038 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2363).leftCharge (GramAssembly.key 2363).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5284) := by
    have ha : gramCharges (GramAssembly.key 2363).leftCharge (GramAssembly.key 2363).rightCharge = raw42039 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42039Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42039 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2363).leftCharge (GramAssembly.key 2363).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2363).leftCharge (GramAssembly.key 2363).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2363, Integer.Sparse.eval]
  ring

theorem keyMoment2364 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2364) =
      Integer.Sparse.eval keyMomentRow2364 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2364).leftCharge (GramAssembly.key 2364).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3996) := by
    have ha : gramCharges (GramAssembly.key 2364).leftCharge (GramAssembly.key 2364).rightCharge = raw42040 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42040Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42040 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2364).leftCharge (GramAssembly.key 2364).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5410) := by
    have ha : gramCharges (GramAssembly.key 2364).leftCharge (GramAssembly.key 2364).rightCharge = raw42041 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42041Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42041 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2364).leftCharge (GramAssembly.key 2364).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2364).leftCharge (GramAssembly.key 2364).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2364, Integer.Sparse.eval]
  ring

theorem keyMoment2365 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2365) =
      Integer.Sparse.eval keyMomentRow2365 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2365).leftCharge (GramAssembly.key 2365).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3) := by
    have ha : gramCharges (GramAssembly.key 2365).leftCharge (GramAssembly.key 2365).rightCharge = raw42042 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42042Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42042 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2365).leftCharge (GramAssembly.key 2365).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4091) := by
    have ha : gramCharges (GramAssembly.key 2365).leftCharge (GramAssembly.key 2365).rightCharge = raw42043 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42043Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42043 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2365).leftCharge (GramAssembly.key 2365).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2365).leftCharge (GramAssembly.key 2365).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2365, Integer.Sparse.eval]
  ring

theorem keyMoment2366 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2366) =
      Integer.Sparse.eval keyMomentRow2366 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2366).leftCharge (GramAssembly.key 2366).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3847) := by
    have ha : gramCharges (GramAssembly.key 2366).leftCharge (GramAssembly.key 2366).rightCharge = raw42044 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42044Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42044 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2366).leftCharge (GramAssembly.key 2366).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5406) := by
    have ha : gramCharges (GramAssembly.key 2366).leftCharge (GramAssembly.key 2366).rightCharge = raw42045 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42045Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42045 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2366).leftCharge (GramAssembly.key 2366).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2366).leftCharge (GramAssembly.key 2366).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2366, Integer.Sparse.eval]
  ring

theorem keyMoment2367 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2367) =
      Integer.Sparse.eval keyMomentRow2367 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2367).leftCharge (GramAssembly.key 2367).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3977) := by
    have ha : gramCharges (GramAssembly.key 2367).leftCharge (GramAssembly.key 2367).rightCharge = raw42046 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42046Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42046 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2367).leftCharge (GramAssembly.key 2367).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5405) := by
    have ha : gramCharges (GramAssembly.key 2367).leftCharge (GramAssembly.key 2367).rightCharge = raw42047 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42047Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42047 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2367).leftCharge (GramAssembly.key 2367).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2367).leftCharge (GramAssembly.key 2367).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2367, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2336 : keyMomentRows (2336 : Fin 2886) =
    keyMomentRow2336 := by decide +kernel

theorem keyMomentRowsAt2337 : keyMomentRows (2337 : Fin 2886) =
    keyMomentRow2337 := by decide +kernel

theorem keyMomentRowsAt2338 : keyMomentRows (2338 : Fin 2886) =
    keyMomentRow2338 := by decide +kernel

theorem keyMomentRowsAt2339 : keyMomentRows (2339 : Fin 2886) =
    keyMomentRow2339 := by decide +kernel

theorem keyMomentRowsAt2340 : keyMomentRows (2340 : Fin 2886) =
    keyMomentRow2340 := by decide +kernel

theorem keyMomentRowsAt2341 : keyMomentRows (2341 : Fin 2886) =
    keyMomentRow2341 := by decide +kernel

theorem keyMomentRowsAt2342 : keyMomentRows (2342 : Fin 2886) =
    keyMomentRow2342 := by decide +kernel

theorem keyMomentRowsAt2343 : keyMomentRows (2343 : Fin 2886) =
    keyMomentRow2343 := by decide +kernel

theorem keyMomentRowsAt2344 : keyMomentRows (2344 : Fin 2886) =
    keyMomentRow2344 := by decide +kernel

theorem keyMomentRowsAt2345 : keyMomentRows (2345 : Fin 2886) =
    keyMomentRow2345 := by decide +kernel

theorem keyMomentRowsAt2346 : keyMomentRows (2346 : Fin 2886) =
    keyMomentRow2346 := by decide +kernel

theorem keyMomentRowsAt2347 : keyMomentRows (2347 : Fin 2886) =
    keyMomentRow2347 := by decide +kernel

theorem keyMomentRowsAt2348 : keyMomentRows (2348 : Fin 2886) =
    keyMomentRow2348 := by decide +kernel

theorem keyMomentRowsAt2349 : keyMomentRows (2349 : Fin 2886) =
    keyMomentRow2349 := by decide +kernel

theorem keyMomentRowsAt2350 : keyMomentRows (2350 : Fin 2886) =
    keyMomentRow2350 := by decide +kernel

theorem keyMomentRowsAt2351 : keyMomentRows (2351 : Fin 2886) =
    keyMomentRow2351 := by decide +kernel

theorem keyMomentRowsAt2352 : keyMomentRows (2352 : Fin 2886) =
    keyMomentRow2352 := by decide +kernel

theorem keyMomentRowsAt2353 : keyMomentRows (2353 : Fin 2886) =
    keyMomentRow2353 := by decide +kernel

theorem keyMomentRowsAt2354 : keyMomentRows (2354 : Fin 2886) =
    keyMomentRow2354 := by decide +kernel

theorem keyMomentRowsAt2355 : keyMomentRows (2355 : Fin 2886) =
    keyMomentRow2355 := by decide +kernel

theorem keyMomentRowsAt2356 : keyMomentRows (2356 : Fin 2886) =
    keyMomentRow2356 := by decide +kernel

theorem keyMomentRowsAt2357 : keyMomentRows (2357 : Fin 2886) =
    keyMomentRow2357 := by decide +kernel

theorem keyMomentRowsAt2358 : keyMomentRows (2358 : Fin 2886) =
    keyMomentRow2358 := by decide +kernel

theorem keyMomentRowsAt2359 : keyMomentRows (2359 : Fin 2886) =
    keyMomentRow2359 := by decide +kernel

theorem keyMomentRowsAt2360 : keyMomentRows (2360 : Fin 2886) =
    keyMomentRow2360 := by decide +kernel

theorem keyMomentRowsAt2361 : keyMomentRows (2361 : Fin 2886) =
    keyMomentRow2361 := by decide +kernel

theorem keyMomentRowsAt2362 : keyMomentRows (2362 : Fin 2886) =
    keyMomentRow2362 := by decide +kernel

theorem keyMomentRowsAt2363 : keyMomentRows (2363 : Fin 2886) =
    keyMomentRow2363 := by decide +kernel

theorem keyMomentRowsAt2364 : keyMomentRows (2364 : Fin 2886) =
    keyMomentRow2364 := by decide +kernel

theorem keyMomentRowsAt2365 : keyMomentRows (2365 : Fin 2886) =
    keyMomentRow2365 := by decide +kernel

theorem keyMomentRowsAt2366 : keyMomentRows (2366 : Fin 2886) =
    keyMomentRow2366 := by decide +kernel

theorem keyMomentRowsAt2367 : keyMomentRows (2367 : Fin 2886) =
    keyMomentRow2367 := by decide +kernel

theorem keyMomentChunkSound73_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 73) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2336 ∨ k.val = 2337 ∨ k.val = 2338 ∨ k.val = 2339 ∨ k.val = 2340 ∨ k.val = 2341 ∨ k.val = 2342 ∨ k.val = 2343 ∨ k.val = 2344 ∨ k.val = 2345 ∨ k.val = 2346 ∨ k.val = 2347 ∨ k.val = 2348 ∨ k.val = 2349 ∨ k.val = 2350 ∨ k.val = 2351 ∨ k.val = 2352 ∨ k.val = 2353 ∨ k.val = 2354 ∨ k.val = 2355 ∨ k.val = 2356 ∨ k.val = 2357 ∨ k.val = 2358 ∨ k.val = 2359 ∨ k.val = 2360 ∨ k.val = 2361 ∨ k.val = 2362 ∨ k.val = 2363 ∨ k.val = 2364 ∨ k.val = 2365 ∨ k.val = 2366 ∨ k.val = 2367 := by omega
  rcases heq with h2336 | h2337 | h2338 | h2339 | h2340 | h2341 | h2342 | h2343 | h2344 | h2345 | h2346 | h2347 | h2348 | h2349 | h2350 | h2351 | h2352 | h2353 | h2354 | h2355 | h2356 | h2357 | h2358 | h2359 | h2360 | h2361 | h2362 | h2363 | h2364 | h2365 | h2366 | h2367
  · have he : k = (2336 : Fin 2886) := Fin.ext h2336
    subst k
    rw [keyMomentRowsAt2336]
    exact keyMoment2336 B hB
  · have he : k = (2337 : Fin 2886) := Fin.ext h2337
    subst k
    rw [keyMomentRowsAt2337]
    exact keyMoment2337 B hB
  · have he : k = (2338 : Fin 2886) := Fin.ext h2338
    subst k
    rw [keyMomentRowsAt2338]
    exact keyMoment2338 B hB
  · have he : k = (2339 : Fin 2886) := Fin.ext h2339
    subst k
    rw [keyMomentRowsAt2339]
    exact keyMoment2339 B hB
  · have he : k = (2340 : Fin 2886) := Fin.ext h2340
    subst k
    rw [keyMomentRowsAt2340]
    exact keyMoment2340 B hB
  · have he : k = (2341 : Fin 2886) := Fin.ext h2341
    subst k
    rw [keyMomentRowsAt2341]
    exact keyMoment2341 B hB
  · have he : k = (2342 : Fin 2886) := Fin.ext h2342
    subst k
    rw [keyMomentRowsAt2342]
    exact keyMoment2342 B hB
  · have he : k = (2343 : Fin 2886) := Fin.ext h2343
    subst k
    rw [keyMomentRowsAt2343]
    exact keyMoment2343 B hB
  · have he : k = (2344 : Fin 2886) := Fin.ext h2344
    subst k
    rw [keyMomentRowsAt2344]
    exact keyMoment2344 B hB
  · have he : k = (2345 : Fin 2886) := Fin.ext h2345
    subst k
    rw [keyMomentRowsAt2345]
    exact keyMoment2345 B hB
  · have he : k = (2346 : Fin 2886) := Fin.ext h2346
    subst k
    rw [keyMomentRowsAt2346]
    exact keyMoment2346 B hB
  · have he : k = (2347 : Fin 2886) := Fin.ext h2347
    subst k
    rw [keyMomentRowsAt2347]
    exact keyMoment2347 B hB
  · have he : k = (2348 : Fin 2886) := Fin.ext h2348
    subst k
    rw [keyMomentRowsAt2348]
    exact keyMoment2348 B hB
  · have he : k = (2349 : Fin 2886) := Fin.ext h2349
    subst k
    rw [keyMomentRowsAt2349]
    exact keyMoment2349 B hB
  · have he : k = (2350 : Fin 2886) := Fin.ext h2350
    subst k
    rw [keyMomentRowsAt2350]
    exact keyMoment2350 B hB
  · have he : k = (2351 : Fin 2886) := Fin.ext h2351
    subst k
    rw [keyMomentRowsAt2351]
    exact keyMoment2351 B hB
  · have he : k = (2352 : Fin 2886) := Fin.ext h2352
    subst k
    rw [keyMomentRowsAt2352]
    exact keyMoment2352 B hB
  · have he : k = (2353 : Fin 2886) := Fin.ext h2353
    subst k
    rw [keyMomentRowsAt2353]
    exact keyMoment2353 B hB
  · have he : k = (2354 : Fin 2886) := Fin.ext h2354
    subst k
    rw [keyMomentRowsAt2354]
    exact keyMoment2354 B hB
  · have he : k = (2355 : Fin 2886) := Fin.ext h2355
    subst k
    rw [keyMomentRowsAt2355]
    exact keyMoment2355 B hB
  · have he : k = (2356 : Fin 2886) := Fin.ext h2356
    subst k
    rw [keyMomentRowsAt2356]
    exact keyMoment2356 B hB
  · have he : k = (2357 : Fin 2886) := Fin.ext h2357
    subst k
    rw [keyMomentRowsAt2357]
    exact keyMoment2357 B hB
  · have he : k = (2358 : Fin 2886) := Fin.ext h2358
    subst k
    rw [keyMomentRowsAt2358]
    exact keyMoment2358 B hB
  · have he : k = (2359 : Fin 2886) := Fin.ext h2359
    subst k
    rw [keyMomentRowsAt2359]
    exact keyMoment2359 B hB
  · have he : k = (2360 : Fin 2886) := Fin.ext h2360
    subst k
    rw [keyMomentRowsAt2360]
    exact keyMoment2360 B hB
  · have he : k = (2361 : Fin 2886) := Fin.ext h2361
    subst k
    rw [keyMomentRowsAt2361]
    exact keyMoment2361 B hB
  · have he : k = (2362 : Fin 2886) := Fin.ext h2362
    subst k
    rw [keyMomentRowsAt2362]
    exact keyMoment2362 B hB
  · have he : k = (2363 : Fin 2886) := Fin.ext h2363
    subst k
    rw [keyMomentRowsAt2363]
    exact keyMoment2363 B hB
  · have he : k = (2364 : Fin 2886) := Fin.ext h2364
    subst k
    rw [keyMomentRowsAt2364]
    exact keyMoment2364 B hB
  · have he : k = (2365 : Fin 2886) := Fin.ext h2365
    subst k
    rw [keyMomentRowsAt2365]
    exact keyMoment2365 B hB
  · have he : k = (2366 : Fin 2886) := Fin.ext h2366
    subst k
    rw [keyMomentRowsAt2366]
    exact keyMoment2366 B hB
  · have he : k = (2367 : Fin 2886) := Fin.ext h2367
    subst k
    rw [keyMomentRowsAt2367]
    exact keyMoment2367 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound73_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound73_e_oai
