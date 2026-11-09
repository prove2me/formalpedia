-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound65_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:00:21.763386+00:00
-- url     : https://prove2.me/submissions/d9f76d3f-c086-48b8-b4ae-c75f5fae4292

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical324
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41493 raw41493Labels = mixedMoment B node2818 node2818Labels := by
  calc
    mixedMoment B raw41493 raw41493Labels = mixedMoment B raw41493step0 raw41493step0Labels := by
      have hz : ∀ j, raw41493 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41493step0 = (fun i j => raw41493 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41493step0 raw41493; decide +kernel
      have hl : raw41493step0Labels = raw41493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41493 raw41493Labels permutation434 hz
    mixedMoment B raw41493step0 raw41493step0Labels = mixedMoment B raw41493step1 raw41493step1Labels := by
      have ha : raw41493step1 = (fun i j => raw41493step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41493step1 raw41493step0; decide +kernel
      have hl : raw41493step1Labels = raw41493step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41493step0 raw41493step0Labels permutation144 permutation6
    _ = mixedMoment B node2818 node2818Labels := by rfl

theorem canonical41494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41494 raw41494Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw41494 raw41494Labels = mixedMoment B raw41494step0 raw41494step0Labels := by
      have hz : ∀ j, raw41494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41494step0 = (fun i j => raw41494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41494step0 raw41494; decide +kernel
      have hl : raw41494step0Labels = raw41494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41494 raw41494Labels permutation434 hz
    mixedMoment B raw41494step0 raw41494step0Labels = mixedMoment B raw41494step1 raw41494step1Labels := by
      have ha : raw41494step1 = (fun i j => raw41494step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41494step1 raw41494step0; decide +kernel
      have hl : raw41494step1Labels = raw41494step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41494step0 raw41494step0Labels permutation96 permutation6
    _ = mixedMoment B node3694 node3694Labels := by rfl

theorem canonical41495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41495 raw41495Labels = mixedMoment B node3672 node3672Labels := by
  calc
    mixedMoment B raw41495 raw41495Labels = mixedMoment B raw41495step0 raw41495step0Labels := by
      have ha : raw41495step0 = (fun i j => raw41495 (permutation413 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41495step0 raw41495; decide +kernel
      have hl : raw41495step0Labels = raw41495Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41495 raw41495Labels permutation413 permutation6
    _ = mixedMoment B node3672 node3672Labels := by rfl

theorem canonical41496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41496 raw41496Labels = mixedMoment B node1139 node1139Labels := by
  calc
    mixedMoment B raw41496 raw41496Labels = mixedMoment B raw41496step0 raw41496step0Labels := by
      have hz : ∀ j, raw41496 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41496step0 = (fun i j => raw41496 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41496step0 raw41496; decide +kernel
      have hl : raw41496step0Labels = raw41496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41496 raw41496Labels permutation434 hz
    mixedMoment B raw41496step0 raw41496step0Labels = mixedMoment B raw41496step1 raw41496step1Labels := by
      have ha : raw41496step1 = (fun i j => raw41496step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41496step1 raw41496step0; decide +kernel
      have hl : raw41496step1Labels = raw41496step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41496step0 raw41496step0Labels permutation144 permutation6
    _ = mixedMoment B node1139 node1139Labels := by rfl

theorem canonical41497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41497 raw41497Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw41497 raw41497Labels = mixedMoment B raw41497step0 raw41497step0Labels := by
      have hz : ∀ j, raw41497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41497step0 = (fun i j => raw41497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41497step0 raw41497; decide +kernel
      have hl : raw41497step0Labels = raw41497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41497 raw41497Labels permutation434 hz
    mixedMoment B raw41497step0 raw41497step0Labels = mixedMoment B raw41497step1 raw41497step1Labels := by
      have ha : raw41497step1 = (fun i j => raw41497step0 (permutation120 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41497step1 raw41497step0; decide +kernel
      have hl : raw41497step1Labels = raw41497step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41497step0 raw41497step0Labels permutation120 permutation6
    _ = mixedMoment B node2489 node2489Labels := by rfl

theorem canonical41498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41498 raw41498Labels = mixedMoment B node2432 node2432Labels := by
  calc
    mixedMoment B raw41498 raw41498Labels = mixedMoment B raw41498step0 raw41498step0Labels := by
      have ha : raw41498step0 = (fun i j => raw41498 (permutation551 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41498step0 raw41498; decide +kernel
      have hl : raw41498step0Labels = raw41498Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41498 raw41498Labels permutation551 permutation6
    _ = mixedMoment B node2432 node2432Labels := by rfl

theorem canonical41499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41499 raw41499Labels = mixedMoment B node614 node614Labels := by
  calc
    mixedMoment B raw41499 raw41499Labels = mixedMoment B raw41499step0 raw41499step0Labels := by
      have hz : ∀ j, raw41499 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41499step0 = (fun i j => raw41499 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41499step0 raw41499; decide +kernel
      have hl : raw41499step0Labels = raw41499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41499 raw41499Labels permutation434 hz
    mixedMoment B raw41499step0 raw41499step0Labels = mixedMoment B raw41499step1 raw41499step1Labels := by
      have hz : ∀ j, raw41499step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41499step1 = (fun i j => raw41499step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41499step1 raw41499step0; decide +kernel
      have hl : raw41499step1Labels = raw41499step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41499step0 raw41499step0Labels permutation80 hz
    mixedMoment B raw41499step1 raw41499step1Labels = mixedMoment B raw41499step2 raw41499step2Labels := by
      have ha : raw41499step2 = (fun i j => raw41499step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41499step2 raw41499step1; decide +kernel
      have hl : raw41499step2Labels = raw41499step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41499step1 raw41499step1Labels permutation30 permutation6
    _ = mixedMoment B node614 node614Labels := by rfl

theorem canonical41500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41500 raw41500Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw41500 raw41500Labels = mixedMoment B raw41500step0 raw41500step0Labels := by
      have hz : ∀ j, raw41500 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41500step0 = (fun i j => raw41500 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41500step0 raw41500; decide +kernel
      have hl : raw41500step0Labels = raw41500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41500 raw41500Labels permutation434 hz
    mixedMoment B raw41500step0 raw41500step0Labels = mixedMoment B raw41500step1 raw41500step1Labels := by
      have hz : ∀ j, raw41500step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41500step1 = (fun i j => raw41500step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41500step1 raw41500step0; decide +kernel
      have hl : raw41500step1Labels = raw41500step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41500step0 raw41500step0Labels permutation80 hz
    mixedMoment B raw41500step1 raw41500step1Labels = mixedMoment B raw41500step2 raw41500step2Labels := by
      have ha : raw41500step2 = (fun i j => raw41500step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41500step2 raw41500step1; decide +kernel
      have hl : raw41500step2Labels = raw41500step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41500step1 raw41500step1Labels permutation24 permutation6
    _ = mixedMoment B node1050 node1050Labels := by rfl

theorem canonical41501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41501 raw41501Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw41501 raw41501Labels = mixedMoment B raw41501step0 raw41501step0Labels := by
      have hz : ∀ j, raw41501 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41501step0 = (fun i j => raw41501 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41501step0 raw41501; decide +kernel
      have hl : raw41501step0Labels = raw41501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41501 raw41501Labels permutation346 hz
    mixedMoment B raw41501step0 raw41501step0Labels = mixedMoment B raw41501step1 raw41501step1Labels := by
      have ha : raw41501step1 = (fun i j => raw41501step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41501step1 raw41501step0; decide +kernel
      have hl : raw41501step1Labels = raw41501step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41501step0 raw41501step0Labels permutation126 permutation6
    _ = mixedMoment B node933 node933Labels := by rfl

theorem canonical41502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41502 raw41502Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw41502 raw41502Labels = mixedMoment B raw41502step0 raw41502step0Labels := by
      have hz : ∀ j, raw41502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41502step0 = (fun i j => raw41502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41502step0 raw41502; decide +kernel
      have hl : raw41502step0Labels = raw41502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41502 raw41502Labels permutation346 hz
    mixedMoment B raw41502step0 raw41502step0Labels = mixedMoment B raw41502step1 raw41502step1Labels := by
      have ha : raw41502step1 = (fun i j => raw41502step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41502step1 raw41502step0; decide +kernel
      have hl : raw41502step1Labels = raw41502step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41502step0 raw41502step0Labels permutation126 permutation6
    _ = mixedMoment B node2342 node2342Labels := by rfl

theorem canonical41503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41503 raw41503Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw41503 raw41503Labels = mixedMoment B raw41503step0 raw41503step0Labels := by
      have hz : ∀ j, raw41503 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41503step0 = (fun i j => raw41503 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41503step0 raw41503; decide +kernel
      have hl : raw41503step0Labels = raw41503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41503 raw41503Labels permutation520 hz
    mixedMoment B raw41503step0 raw41503step0Labels = mixedMoment B raw41503step1 raw41503step1Labels := by
      have hz : ∀ j, raw41503step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41503step1 = (fun i j => raw41503step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41503step1 raw41503step0; decide +kernel
      have hl : raw41503step1Labels = raw41503step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41503step0 raw41503step0Labels permutation104 hz
    mixedMoment B raw41503step1 raw41503step1Labels = mixedMoment B raw41503step2 raw41503step2Labels := by
      have ha : raw41503step2 = (fun i j => raw41503step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41503step2 raw41503step1; decide +kernel
      have hl : raw41503step2Labels = raw41503step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41503step1 raw41503step1Labels permutation24 permutation6
    _ = mixedMoment B node1818 node1818Labels := by rfl

theorem canonical41504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41504 raw41504Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw41504 raw41504Labels = mixedMoment B raw41504step0 raw41504step0Labels := by
      have hz : ∀ j, raw41504 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41504step0 = (fun i j => raw41504 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41504step0 raw41504; decide +kernel
      have hl : raw41504step0Labels = raw41504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41504 raw41504Labels permutation520 hz
    mixedMoment B raw41504step0 raw41504step0Labels = mixedMoment B raw41504step1 raw41504step1Labels := by
      have ha : raw41504step1 = (fun i j => raw41504step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41504step1 raw41504step0; decide +kernel
      have hl : raw41504step1Labels = raw41504step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41504step0 raw41504step0Labels permutation59 permutation6
    mixedMoment B raw41504step1 raw41504step1Labels = mixedMoment B raw41504step2 raw41504step2Labels := by
      have ha : raw41504step2 = -raw41504step1 := by apply Matrix.ext; change ∀ i j, raw41504step2 i j = -(raw41504step1 i j); unfold raw41504step2 raw41504step1; decide +kernel
      have hl : raw41504step2Labels = raw41504step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2341 node2341Labels := by rfl

theorem canonical41505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41505 raw41505Labels = mixedMoment B node2330 node2330Labels := by
  calc
    mixedMoment B raw41505 raw41505Labels = mixedMoment B raw41505step0 raw41505step0Labels := by
      have ha : raw41505step0 = (fun i j => raw41505 (permutation282 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41505step0 raw41505; decide +kernel
      have hl : raw41505step0Labels = raw41505Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41505 raw41505Labels permutation282 permutation6
    mixedMoment B raw41505step0 raw41505step0Labels = mixedMoment B raw41505step1 raw41505step1Labels := by
      have ha : raw41505step1 = -raw41505step0 := by apply Matrix.ext; change ∀ i j, raw41505step1 i j = -(raw41505step0 i j); unfold raw41505step1 raw41505step0; decide +kernel
      have hl : raw41505step1Labels = raw41505step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2330 node2330Labels := by rfl

theorem canonical41506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41506 raw41506Labels = mixedMoment B node2345 node2345Labels := by
  calc
    mixedMoment B raw41506 raw41506Labels = mixedMoment B raw41506step0 raw41506step0Labels := by
      have hz : ∀ j, raw41506 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41506step0 = (fun i j => raw41506 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41506step0 raw41506; decide +kernel
      have hl : raw41506step0Labels = raw41506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41506 raw41506Labels permutation520 hz
    mixedMoment B raw41506step0 raw41506step0Labels = mixedMoment B raw41506step1 raw41506step1Labels := by
      have hz : ∀ j, raw41506step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41506step1 = (fun i j => raw41506step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41506step1 raw41506step0; decide +kernel
      have hl : raw41506step1Labels = raw41506step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41506step0 raw41506step0Labels permutation104 hz
    mixedMoment B raw41506step1 raw41506step1Labels = mixedMoment B raw41506step2 raw41506step2Labels := by
      have ha : raw41506step2 = (fun i j => raw41506step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41506step2 raw41506step1; decide +kernel
      have hl : raw41506step2Labels = raw41506step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41506step1 raw41506step1Labels permutation14 permutation6
    mixedMoment B raw41506step2 raw41506step2Labels = mixedMoment B raw41506step3 raw41506step3Labels := by
      have ha : raw41506step3 = -raw41506step2 := by apply Matrix.ext; change ∀ i j, raw41506step3 i j = -(raw41506step2 i j); unfold raw41506step3 raw41506step2; decide +kernel
      have hl : raw41506step3Labels = raw41506step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2345 node2345Labels := by rfl

theorem canonical41507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41507 raw41507Labels = mixedMoment B node2337 node2337Labels := by
  calc
    mixedMoment B raw41507 raw41507Labels = mixedMoment B raw41507step0 raw41507step0Labels := by
      have hz : ∀ j, raw41507 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41507step0 = (fun i j => raw41507 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41507step0 raw41507; decide +kernel
      have hl : raw41507step0Labels = raw41507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41507 raw41507Labels permutation434 hz
    mixedMoment B raw41507step0 raw41507step0Labels = mixedMoment B raw41507step1 raw41507step1Labels := by
      have ha : raw41507step1 = (fun i j => raw41507step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41507step1 raw41507step0; decide +kernel
      have hl : raw41507step1Labels = raw41507step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41507step0 raw41507step0Labels permutation61 permutation6
    mixedMoment B raw41507step1 raw41507step1Labels = mixedMoment B raw41507step2 raw41507step2Labels := by
      have ha : raw41507step2 = -raw41507step1 := by apply Matrix.ext; change ∀ i j, raw41507step2 i j = -(raw41507step1 i j); unfold raw41507step2 raw41507step1; decide +kernel
      have hl : raw41507step2Labels = raw41507step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2337 node2337Labels := by rfl

theorem canonical41508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41508 raw41508Labels = mixedMoment B node2338 node2338Labels := by
  calc
    mixedMoment B raw41508 raw41508Labels = mixedMoment B raw41508step0 raw41508step0Labels := by
      have ha : raw41508step0 = (fun i j => raw41508 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41508step0 raw41508; decide +kernel
      have hl : raw41508step0Labels = raw41508Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41508 raw41508Labels permutation265 permutation6
    mixedMoment B raw41508step0 raw41508step0Labels = mixedMoment B raw41508step1 raw41508step1Labels := by
      have ha : raw41508step1 = -raw41508step0 := by apply Matrix.ext; change ∀ i j, raw41508step1 i j = -(raw41508step0 i j); unfold raw41508step1 raw41508step0; decide +kernel
      have hl : raw41508step1Labels = raw41508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2338 node2338Labels := by rfl

theorem canonical41509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41509 raw41509Labels = mixedMoment B node2339 node2339Labels := by
  calc
    mixedMoment B raw41509 raw41509Labels = mixedMoment B raw41509step0 raw41509step0Labels := by
      have hz : ∀ j, raw41509 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41509step0 = (fun i j => raw41509 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41509step0 raw41509; decide +kernel
      have hl : raw41509step0Labels = raw41509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41509 raw41509Labels permutation520 hz
    mixedMoment B raw41509step0 raw41509step0Labels = mixedMoment B raw41509step1 raw41509step1Labels := by
      have ha : raw41509step1 = (fun i j => raw41509step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41509step1 raw41509step0; decide +kernel
      have hl : raw41509step1Labels = raw41509step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41509step0 raw41509step0Labels permutation56 permutation6
    mixedMoment B raw41509step1 raw41509step1Labels = mixedMoment B raw41509step2 raw41509step2Labels := by
      have ha : raw41509step2 = -raw41509step1 := by apply Matrix.ext; change ∀ i j, raw41509step2 i j = -(raw41509step1 i j); unfold raw41509step2 raw41509step1; decide +kernel
      have hl : raw41509step2Labels = raw41509step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2339 node2339Labels := by rfl

theorem canonical41510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41510 raw41510Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw41510 raw41510Labels = mixedMoment B raw41510step0 raw41510step0Labels := by
      have hz : ∀ j, raw41510 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41510step0 = (fun i j => raw41510 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41510step0 raw41510; decide +kernel
      have hl : raw41510step0Labels = raw41510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41510 raw41510Labels permutation520 hz
    mixedMoment B raw41510step0 raw41510step0Labels = mixedMoment B raw41510step1 raw41510step1Labels := by
      have hz : ∀ j, raw41510step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41510step1 = (fun i j => raw41510step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41510step1 raw41510step0; decide +kernel
      have hl : raw41510step1Labels = raw41510step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41510step0 raw41510step0Labels permutation104 hz
    mixedMoment B raw41510step1 raw41510step1Labels = mixedMoment B raw41510step2 raw41510step2Labels := by
      have ha : raw41510step2 = (fun i j => raw41510step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41510step2 raw41510step1; decide +kernel
      have hl : raw41510step2Labels = raw41510step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41510step1 raw41510step1Labels permutation30 permutation6
    _ = mixedMoment B node1144 node1144Labels := by rfl

theorem canonical41511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41511 raw41511Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw41511 raw41511Labels = mixedMoment B raw41511step0 raw41511step0Labels := by
      have hz : ∀ j, raw41511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41511step0 = (fun i j => raw41511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41511step0 raw41511; decide +kernel
      have hl : raw41511step0Labels = raw41511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41511 raw41511Labels permutation434 hz
    mixedMoment B raw41511step0 raw41511step0Labels = mixedMoment B raw41511step1 raw41511step1Labels := by
      have ha : raw41511step1 = (fun i j => raw41511step0 (permutation60 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41511step1 raw41511step0; decide +kernel
      have hl : raw41511step1Labels = raw41511step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41511step0 raw41511step0Labels permutation60 permutation6
    mixedMoment B raw41511step1 raw41511step1Labels = mixedMoment B raw41511step2 raw41511step2Labels := by
      have ha : raw41511step2 = -raw41511step1 := by apply Matrix.ext; change ∀ i j, raw41511step2 i j = -(raw41511step1 i j); unfold raw41511step2 raw41511step1; decide +kernel
      have hl : raw41511step2Labels = raw41511step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2334 node2334Labels := by rfl

theorem canonical41512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41512 raw41512Labels = mixedMoment B node619 node619Labels := by
  calc
    mixedMoment B raw41512 raw41512Labels = mixedMoment B raw41512step0 raw41512step0Labels := by
      have hz : ∀ j, raw41512 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41512step0 = (fun i j => raw41512 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41512step0 raw41512; decide +kernel
      have hl : raw41512step0Labels = raw41512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41512 raw41512Labels permutation520 hz
    mixedMoment B raw41512step0 raw41512step0Labels = mixedMoment B raw41512step1 raw41512step1Labels := by
      have hz : ∀ j, raw41512step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41512step1 = (fun i j => raw41512step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41512step1 raw41512step0; decide +kernel
      have hl : raw41512step1Labels = raw41512step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41512step0 raw41512step0Labels permutation104 hz
    mixedMoment B raw41512step1 raw41512step1Labels = mixedMoment B raw41512step2 raw41512step2Labels := by
      have hz : ∀ j, raw41512step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41512step2 = (fun i j => raw41512step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41512step2 raw41512step1; decide +kernel
      have hl : raw41512step2Labels = raw41512step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41512step1 raw41512step1Labels permutation20 hz
    mixedMoment B raw41512step2 raw41512step2Labels = mixedMoment B raw41512step3 raw41512step3Labels := by
      have ha : raw41512step3 = (fun i j => raw41512step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41512step3 raw41512step2; decide +kernel
      have hl : raw41512step3Labels = raw41512step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41512step2 raw41512step2Labels permutation6 permutation6
    _ = mixedMoment B node619 node619Labels := by rfl

theorem canonical41513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41513 raw41513Labels = mixedMoment B node2344 node2344Labels := by
  calc
    mixedMoment B raw41513 raw41513Labels = mixedMoment B raw41513step0 raw41513step0Labels := by
      have hz : ∀ j, raw41513 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41513step0 = (fun i j => raw41513 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41513step0 raw41513; decide +kernel
      have hl : raw41513step0Labels = raw41513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41513 raw41513Labels permutation434 hz
    mixedMoment B raw41513step0 raw41513step0Labels = mixedMoment B raw41513step1 raw41513step1Labels := by
      have hz : ∀ j, raw41513step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41513step1 = (fun i j => raw41513step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41513step1 raw41513step0; decide +kernel
      have hl : raw41513step1Labels = raw41513step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41513step0 raw41513step0Labels permutation80 hz
    mixedMoment B raw41513step1 raw41513step1Labels = mixedMoment B raw41513step2 raw41513step2Labels := by
      have ha : raw41513step2 = (fun i j => raw41513step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41513step2 raw41513step1; decide +kernel
      have hl : raw41513step2Labels = raw41513step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41513step1 raw41513step1Labels permutation24 permutation6
    _ = mixedMoment B node2344 node2344Labels := by rfl

theorem canonical41514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41514 raw41514Labels = mixedMoment B node2 node2Labels := by
  calc
    mixedMoment B raw41514 raw41514Labels = mixedMoment B raw41514step0 raw41514step0Labels := by
      have hz : ∀ j, raw41514 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41514step0 = (fun i j => raw41514 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41514step0 raw41514; decide +kernel
      have hl : raw41514step0Labels = raw41514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41514 raw41514Labels permutation520 hz
    mixedMoment B raw41514step0 raw41514step0Labels = mixedMoment B raw41514step1 raw41514step1Labels := by
      have hz : ∀ j, raw41514step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41514step1 = (fun i j => raw41514step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41514step1 raw41514step0; decide +kernel
      have hl : raw41514step1Labels = raw41514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41514step0 raw41514step0Labels permutation104 hz
    mixedMoment B raw41514step1 raw41514step1Labels = mixedMoment B raw41514step2 raw41514step2Labels := by
      have hz : ∀ j, raw41514step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41514step2 = (fun i j => raw41514step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41514step2 raw41514step1; decide +kernel
      have hl : raw41514step2Labels = raw41514step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41514step1 raw41514step1Labels permutation20 hz
    mixedMoment B raw41514step2 raw41514step2Labels = mixedMoment B raw41514step3 raw41514step3Labels := by
      have hz : ∀ j, raw41514step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw41514step3 = (fun i j => raw41514step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw41514step3 raw41514step2; decide +kernel
      have hl : raw41514step3Labels = raw41514step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41514step2 raw41514step2Labels permutation4 hz
    mixedMoment B raw41514step3 raw41514step3Labels = mixedMoment B raw41514step4 raw41514step4Labels := by
      have hz : ∀ i, raw41514step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw41514step4 = (fun i j => raw41514step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw41514step4 raw41514step3; decide +kernel
      have hl : raw41514step4Labels = (fun j => raw41514step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw41514step3 raw41514step3Labels permutation6 hz
    mixedMoment B raw41514step4 raw41514step4Labels = mixedMoment B raw41514step5 raw41514step5Labels := by
      have ha : raw41514step5 = raw41514step4 := by apply Matrix.ext; unfold raw41514step5 raw41514step4; decide +kernel
      have hl : raw41514step4Labels = labelEmbedding0 ∘ raw41514step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41514step4 raw41514step4Labels raw41514step5Labels labelEmbedding0 hl
    _ = mixedMoment B node2 node2Labels := by rfl

theorem canonical41515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41515 raw41515Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw41515 raw41515Labels = mixedMoment B raw41515step0 raw41515step0Labels := by
      have hz : ∀ j, raw41515 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41515step0 = (fun i j => raw41515 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41515step0 raw41515; decide +kernel
      have hl : raw41515step0Labels = raw41515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41515 raw41515Labels permutation520 hz
    mixedMoment B raw41515step0 raw41515step0Labels = mixedMoment B raw41515step1 raw41515step1Labels := by
      have hz : ∀ j, raw41515step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41515step1 = (fun i j => raw41515step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41515step1 raw41515step0; decide +kernel
      have hl : raw41515step1Labels = raw41515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41515step0 raw41515step0Labels permutation104 hz
    mixedMoment B raw41515step1 raw41515step1Labels = mixedMoment B raw41515step2 raw41515step2Labels := by
      have hz : ∀ j, raw41515step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41515step2 = (fun i j => raw41515step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41515step2 raw41515step1; decide +kernel
      have hl : raw41515step2Labels = raw41515step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41515step1 raw41515step1Labels permutation20 hz
    mixedMoment B raw41515step2 raw41515step2Labels = mixedMoment B raw41515step3 raw41515step3Labels := by
      have hz : ∀ j, raw41515step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw41515step3 = (fun i j => raw41515step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw41515step3 raw41515step2; decide +kernel
      have hl : raw41515step3Labels = raw41515step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41515step2 raw41515step2Labels permutation4 hz
    mixedMoment B raw41515step3 raw41515step3Labels = mixedMoment B raw41515step4 raw41515step4Labels := by
      have hz : ∀ i, raw41515step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw41515step4 = (fun i j => raw41515step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw41515step4 raw41515step3; decide +kernel
      have hl : raw41515step4Labels = (fun j => raw41515step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw41515step3 raw41515step3Labels permutation6 hz
    mixedMoment B raw41515step4 raw41515step4Labels = mixedMoment B raw41515step5 raw41515step5Labels := by
      have ha : raw41515step5 = raw41515step4 := by apply Matrix.ext; unfold raw41515step5 raw41515step4; decide +kernel
      have hl : raw41515step4Labels = labelEmbedding3 ∘ raw41515step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41515step4 raw41515step4Labels raw41515step5Labels labelEmbedding3 hl
    _ = mixedMoment B node4085 node4085Labels := by rfl

theorem canonical41516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41516 raw41516Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw41516 raw41516Labels = mixedMoment B raw41516step0 raw41516step0Labels := by
      have hz : ∀ j, raw41516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41516step0 = (fun i j => raw41516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41516step0 raw41516; decide +kernel
      have hl : raw41516step0Labels = raw41516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41516 raw41516Labels permutation434 hz
    mixedMoment B raw41516step0 raw41516step0Labels = mixedMoment B raw41516step1 raw41516step1Labels := by
      have hz : ∀ j, raw41516step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41516step1 = (fun i j => raw41516step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41516step1 raw41516step0; decide +kernel
      have hl : raw41516step1Labels = raw41516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41516step0 raw41516step0Labels permutation80 hz
    mixedMoment B raw41516step1 raw41516step1Labels = mixedMoment B raw41516step2 raw41516step2Labels := by
      have hz : ∀ j, raw41516step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41516step2 = (fun i j => raw41516step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41516step2 raw41516step1; decide +kernel
      have hl : raw41516step2Labels = raw41516step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41516step1 raw41516step1Labels permutation14 hz
    mixedMoment B raw41516step2 raw41516step2Labels = mixedMoment B raw41516step3 raw41516step3Labels := by
      have ha : raw41516step3 = (fun i j => raw41516step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41516step3 raw41516step2; decide +kernel
      have hl : raw41516step3Labels = raw41516step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41516step2 raw41516step2Labels permutation7 permutation4
    mixedMoment B raw41516step3 raw41516step3Labels = mixedMoment B raw41516step4 raw41516step4Labels := by
      have ha : raw41516step4 = raw41516step3 := by apply Matrix.ext; unfold raw41516step4 raw41516step3; decide +kernel
      have hl : raw41516step3Labels = labelEmbedding1 ∘ raw41516step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41516step3 raw41516step3Labels raw41516step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3114 node3114Labels := by rfl

theorem canonical41517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41517 raw41517Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw41517 raw41517Labels = mixedMoment B raw41517step0 raw41517step0Labels := by
      have hz : ∀ j, raw41517 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41517step0 = (fun i j => raw41517 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41517step0 raw41517; decide +kernel
      have hl : raw41517step0Labels = raw41517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41517 raw41517Labels permutation434 hz
    mixedMoment B raw41517step0 raw41517step0Labels = mixedMoment B raw41517step1 raw41517step1Labels := by
      have hz : ∀ j, raw41517step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41517step1 = (fun i j => raw41517step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41517step1 raw41517step0; decide +kernel
      have hl : raw41517step1Labels = raw41517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41517step0 raw41517step0Labels permutation80 hz
    mixedMoment B raw41517step1 raw41517step1Labels = mixedMoment B raw41517step2 raw41517step2Labels := by
      have hz : ∀ j, raw41517step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41517step2 = (fun i j => raw41517step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41517step2 raw41517step1; decide +kernel
      have hl : raw41517step2Labels = raw41517step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41517step1 raw41517step1Labels permutation14 hz
    mixedMoment B raw41517step2 raw41517step2Labels = mixedMoment B raw41517step3 raw41517step3Labels := by
      have ha : raw41517step3 = (fun i j => raw41517step2 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41517step3 raw41517step2; decide +kernel
      have hl : raw41517step3Labels = raw41517step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41517step2 raw41517step2Labels permutation2 permutation5
    mixedMoment B raw41517step3 raw41517step3Labels = mixedMoment B raw41517step4 raw41517step4Labels := by
      have ha : raw41517step4 = -raw41517step3 := by apply Matrix.ext; change ∀ i j, raw41517step4 i j = -(raw41517step3 i j); unfold raw41517step4 raw41517step3; decide +kernel
      have hl : raw41517step4Labels = raw41517step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41517step4 raw41517step4Labels = mixedMoment B raw41517step5 raw41517step5Labels := by
      have ha : raw41517step5 = raw41517step4 := by apply Matrix.ext; unfold raw41517step5 raw41517step4; decide +kernel
      have hl : raw41517step4Labels = labelEmbedding9 ∘ raw41517step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41517step4 raw41517step4Labels raw41517step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

theorem canonical41518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41518 raw41518Labels = mixedMoment B node1 node1Labels := by
  calc
    mixedMoment B raw41518 raw41518Labels = mixedMoment B raw41518step0 raw41518step0Labels := by
      have hz : ∀ j, raw41518 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41518step0 = (fun i j => raw41518 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41518step0 raw41518; decide +kernel
      have hl : raw41518step0Labels = raw41518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41518 raw41518Labels permutation434 hz
    mixedMoment B raw41518step0 raw41518step0Labels = mixedMoment B raw41518step1 raw41518step1Labels := by
      have hz : ∀ j, raw41518step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41518step1 = (fun i j => raw41518step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41518step1 raw41518step0; decide +kernel
      have hl : raw41518step1Labels = raw41518step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41518step0 raw41518step0Labels permutation80 hz
    mixedMoment B raw41518step1 raw41518step1Labels = mixedMoment B raw41518step2 raw41518step2Labels := by
      have hz : ∀ j, raw41518step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41518step2 = (fun i j => raw41518step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41518step2 raw41518step1; decide +kernel
      have hl : raw41518step2Labels = raw41518step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41518step1 raw41518step1Labels permutation14 hz
    mixedMoment B raw41518step2 raw41518step2Labels = mixedMoment B raw41518step3 raw41518step3Labels := by
      have hz : ∀ i, raw41518step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw41518step3 = (fun i j => raw41518step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw41518step3 raw41518step2; decide +kernel
      have hl : raw41518step3Labels = (fun j => raw41518step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw41518step2 raw41518step2Labels permutation6 hz
    mixedMoment B raw41518step3 raw41518step3Labels = mixedMoment B raw41518step4 raw41518step4Labels := by
      have ha : raw41518step4 = raw41518step3 := by apply Matrix.ext; unfold raw41518step4 raw41518step3; decide +kernel
      have hl : raw41518step3Labels = labelEmbedding0 ∘ raw41518step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41518step3 raw41518step3Labels raw41518step4Labels labelEmbedding0 hl
    _ = mixedMoment B node1 node1Labels := by rfl

theorem canonical41519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41519 raw41519Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw41519 raw41519Labels = mixedMoment B raw41519step0 raw41519step0Labels := by
      have hz : ∀ j, raw41519 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41519step0 = (fun i j => raw41519 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41519step0 raw41519; decide +kernel
      have hl : raw41519step0Labels = raw41519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41519 raw41519Labels permutation434 hz
    mixedMoment B raw41519step0 raw41519step0Labels = mixedMoment B raw41519step1 raw41519step1Labels := by
      have hz : ∀ j, raw41519step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41519step1 = (fun i j => raw41519step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41519step1 raw41519step0; decide +kernel
      have hl : raw41519step1Labels = raw41519step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41519step0 raw41519step0Labels permutation80 hz
    mixedMoment B raw41519step1 raw41519step1Labels = mixedMoment B raw41519step2 raw41519step2Labels := by
      have hz : ∀ j, raw41519step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41519step2 = (fun i j => raw41519step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41519step2 raw41519step1; decide +kernel
      have hl : raw41519step2Labels = raw41519step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41519step1 raw41519step1Labels permutation14 hz
    mixedMoment B raw41519step2 raw41519step2Labels = mixedMoment B raw41519step3 raw41519step3Labels := by
      have hz : ∀ i, raw41519step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw41519step3 = (fun i j => raw41519step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw41519step3 raw41519step2; decide +kernel
      have hl : raw41519step3Labels = (fun j => raw41519step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw41519step2 raw41519step2Labels permutation6 hz
    mixedMoment B raw41519step3 raw41519step3Labels = mixedMoment B raw41519step4 raw41519step4Labels := by
      have ha : raw41519step4 = raw41519step3 := by apply Matrix.ext; unfold raw41519step4 raw41519step3; decide +kernel
      have hl : raw41519step3Labels = labelEmbedding3 ∘ raw41519step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41519step3 raw41519step3Labels raw41519step4Labels labelEmbedding3 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical41520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41520 raw41520Labels = mixedMoment B node3231 node3231Labels := by
  calc
    mixedMoment B raw41520 raw41520Labels = mixedMoment B raw41520step0 raw41520step0Labels := by
      have hz : ∀ j, raw41520 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41520step0 = (fun i j => raw41520 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41520step0 raw41520; decide +kernel
      have hl : raw41520step0Labels = raw41520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41520 raw41520Labels permutation434 hz
    mixedMoment B raw41520step0 raw41520step0Labels = mixedMoment B raw41520step1 raw41520step1Labels := by
      have hz : ∀ j, raw41520step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41520step1 = (fun i j => raw41520step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41520step1 raw41520step0; decide +kernel
      have hl : raw41520step1Labels = raw41520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41520step0 raw41520step0Labels permutation80 hz
    mixedMoment B raw41520step1 raw41520step1Labels = mixedMoment B raw41520step2 raw41520step2Labels := by
      have hz : ∀ j, raw41520step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41520step2 = (fun i j => raw41520step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41520step2 raw41520step1; decide +kernel
      have hl : raw41520step2Labels = raw41520step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41520step1 raw41520step1Labels permutation14 hz
    mixedMoment B raw41520step2 raw41520step2Labels = mixedMoment B raw41520step3 raw41520step3Labels := by
      have ha : raw41520step3 = raw41520step2 := by apply Matrix.ext; unfold raw41520step3 raw41520step2; decide +kernel
      have hl : raw41520step2Labels = labelEmbedding1 ∘ raw41520step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41520step2 raw41520step2Labels raw41520step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3231 node3231Labels := by rfl

theorem canonical41521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41521 raw41521Labels = mixedMoment B node4901 node4901Labels := by
  calc
    mixedMoment B raw41521 raw41521Labels = mixedMoment B raw41521step0 raw41521step0Labels := by
      have hz : ∀ j, raw41521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41521step0 = (fun i j => raw41521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41521step0 raw41521; decide +kernel
      have hl : raw41521step0Labels = raw41521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41521 raw41521Labels permutation434 hz
    mixedMoment B raw41521step0 raw41521step0Labels = mixedMoment B raw41521step1 raw41521step1Labels := by
      have hz : ∀ j, raw41521step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41521step1 = (fun i j => raw41521step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41521step1 raw41521step0; decide +kernel
      have hl : raw41521step1Labels = raw41521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41521step0 raw41521step0Labels permutation80 hz
    mixedMoment B raw41521step1 raw41521step1Labels = mixedMoment B raw41521step2 raw41521step2Labels := by
      have hz : ∀ j, raw41521step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41521step2 = (fun i j => raw41521step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41521step2 raw41521step1; decide +kernel
      have hl : raw41521step2Labels = raw41521step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41521step1 raw41521step1Labels permutation14 hz
    mixedMoment B raw41521step2 raw41521step2Labels = mixedMoment B raw41521step3 raw41521step3Labels := by
      have ha : raw41521step3 = (fun i j => raw41521step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41521step3 raw41521step2; decide +kernel
      have hl : raw41521step3Labels = raw41521step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41521step2 raw41521step2Labels permutation2 permutation3
    mixedMoment B raw41521step3 raw41521step3Labels = mixedMoment B raw41521step4 raw41521step4Labels := by
      have ha : raw41521step4 = raw41521step3 := by apply Matrix.ext; unfold raw41521step4 raw41521step3; decide +kernel
      have hl : raw41521step3Labels = labelEmbedding7 ∘ raw41521step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41521step3 raw41521step3Labels raw41521step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4901 node4901Labels := by rfl

theorem canonical41522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41522 raw41522Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw41522 raw41522Labels = mixedMoment B raw41522step0 raw41522step0Labels := by
      have hz : ∀ j, raw41522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41522step0 = (fun i j => raw41522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41522step0 raw41522; decide +kernel
      have hl : raw41522step0Labels = raw41522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41522 raw41522Labels permutation434 hz
    mixedMoment B raw41522step0 raw41522step0Labels = mixedMoment B raw41522step1 raw41522step1Labels := by
      have hz : ∀ j, raw41522step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41522step1 = (fun i j => raw41522step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41522step1 raw41522step0; decide +kernel
      have hl : raw41522step1Labels = raw41522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41522step0 raw41522step0Labels permutation80 hz
    mixedMoment B raw41522step1 raw41522step1Labels = mixedMoment B raw41522step2 raw41522step2Labels := by
      have hz : ∀ j, raw41522step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41522step2 = (fun i j => raw41522step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41522step2 raw41522step1; decide +kernel
      have hl : raw41522step2Labels = raw41522step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41522step1 raw41522step1Labels permutation14 hz
    mixedMoment B raw41522step2 raw41522step2Labels = mixedMoment B raw41522step3 raw41522step3Labels := by
      have ha : raw41522step3 = (fun i j => raw41522step2 (permutation5 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41522step3 raw41522step2; decide +kernel
      have hl : raw41522step3Labels = raw41522step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41522step2 raw41522step2Labels permutation5 permutation4
    mixedMoment B raw41522step3 raw41522step3Labels = mixedMoment B raw41522step4 raw41522step4Labels := by
      have ha : raw41522step4 = raw41522step3 := by apply Matrix.ext; unfold raw41522step4 raw41522step3; decide +kernel
      have hl : raw41522step3Labels = labelEmbedding1 ∘ raw41522step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41522step3 raw41522step3Labels raw41522step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2778 node2778Labels := by rfl

theorem canonical41523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41523 raw41523Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw41523 raw41523Labels = mixedMoment B raw41523step0 raw41523step0Labels := by
      have hz : ∀ j, raw41523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41523step0 = (fun i j => raw41523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41523step0 raw41523; decide +kernel
      have hl : raw41523step0Labels = raw41523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41523 raw41523Labels permutation434 hz
    mixedMoment B raw41523step0 raw41523step0Labels = mixedMoment B raw41523step1 raw41523step1Labels := by
      have hz : ∀ j, raw41523step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41523step1 = (fun i j => raw41523step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41523step1 raw41523step0; decide +kernel
      have hl : raw41523step1Labels = raw41523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41523step0 raw41523step0Labels permutation80 hz
    mixedMoment B raw41523step1 raw41523step1Labels = mixedMoment B raw41523step2 raw41523step2Labels := by
      have hz : ∀ j, raw41523step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41523step2 = (fun i j => raw41523step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41523step2 raw41523step1; decide +kernel
      have hl : raw41523step2Labels = raw41523step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41523step1 raw41523step1Labels permutation14 hz
    mixedMoment B raw41523step2 raw41523step2Labels = mixedMoment B raw41523step3 raw41523step3Labels := by
      have ha : raw41523step3 = (fun i j => raw41523step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41523step3 raw41523step2; decide +kernel
      have hl : raw41523step3Labels = raw41523step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41523step2 raw41523step2Labels permutation3 permutation5
    mixedMoment B raw41523step3 raw41523step3Labels = mixedMoment B raw41523step4 raw41523step4Labels := by
      have ha : raw41523step4 = -raw41523step3 := by apply Matrix.ext; change ∀ i j, raw41523step4 i j = -(raw41523step3 i j); unfold raw41523step4 raw41523step3; decide +kernel
      have hl : raw41523step4Labels = raw41523step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41523step4 raw41523step4Labels = mixedMoment B raw41523step5 raw41523step5Labels := by
      have ha : raw41523step5 = raw41523step4 := by apply Matrix.ext; unfold raw41523step5 raw41523step4; decide +kernel
      have hl : raw41523step4Labels = labelEmbedding9 ∘ raw41523step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41523step4 raw41523step4Labels raw41523step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

theorem canonical41524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41524 raw41524Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw41524 raw41524Labels = mixedMoment B raw41524step0 raw41524step0Labels := by
      have hz : ∀ j, raw41524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41524step0 = (fun i j => raw41524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41524step0 raw41524; decide +kernel
      have hl : raw41524step0Labels = raw41524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41524 raw41524Labels permutation346 hz
    mixedMoment B raw41524step0 raw41524step0Labels = mixedMoment B raw41524step1 raw41524step1Labels := by
      have hz : ∀ j, raw41524step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41524step1 = (fun i j => raw41524step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41524step1 raw41524step0; decide +kernel
      have hl : raw41524step1Labels = raw41524step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41524step0 raw41524step0Labels permutation56 hz
    mixedMoment B raw41524step1 raw41524step1Labels = mixedMoment B raw41524step2 raw41524step2Labels := by
      have ha : raw41524step2 = raw41524step1 := by apply Matrix.ext; unfold raw41524step2 raw41524step1; decide +kernel
      have hl : raw41524step1Labels = labelEmbedding1 ∘ raw41524step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41524step1 raw41524step1Labels raw41524step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3230 node3230Labels := by rfl

theorem canonical41525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41525 raw41525Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw41525 raw41525Labels = mixedMoment B raw41525step0 raw41525step0Labels := by
      have hz : ∀ j, raw41525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41525step0 = (fun i j => raw41525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41525step0 raw41525; decide +kernel
      have hl : raw41525step0Labels = raw41525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41525 raw41525Labels permutation346 hz
    mixedMoment B raw41525step0 raw41525step0Labels = mixedMoment B raw41525step1 raw41525step1Labels := by
      have hz : ∀ j, raw41525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41525step1 = (fun i j => raw41525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41525step1 raw41525step0; decide +kernel
      have hl : raw41525step1Labels = raw41525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41525step0 raw41525step0Labels permutation56 hz
    mixedMoment B raw41525step1 raw41525step1Labels = mixedMoment B raw41525step2 raw41525step2Labels := by
      have ha : raw41525step2 = (fun i j => raw41525step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41525step2 raw41525step1; decide +kernel
      have hl : raw41525step2Labels = raw41525step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41525step1 raw41525step1Labels permutation8 permutation3
    mixedMoment B raw41525step2 raw41525step2Labels = mixedMoment B raw41525step3 raw41525step3Labels := by
      have ha : raw41525step3 = raw41525step2 := by apply Matrix.ext; unfold raw41525step3 raw41525step2; decide +kernel
      have hl : raw41525step2Labels = labelEmbedding7 ∘ raw41525step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41525step2 raw41525step2Labels raw41525step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4894 node4894Labels := by rfl

theorem canonical41526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41526 raw41526Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw41526 raw41526Labels = mixedMoment B raw41526step0 raw41526step0Labels := by
      have hz : ∀ j, raw41526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41526step0 = (fun i j => raw41526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41526step0 raw41526; decide +kernel
      have hl : raw41526step0Labels = raw41526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41526 raw41526Labels permutation346 hz
    mixedMoment B raw41526step0 raw41526step0Labels = mixedMoment B raw41526step1 raw41526step1Labels := by
      have hz : ∀ j, raw41526step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41526step1 = (fun i j => raw41526step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41526step1 raw41526step0; decide +kernel
      have hl : raw41526step1Labels = raw41526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41526step0 raw41526step0Labels permutation56 hz
    mixedMoment B raw41526step1 raw41526step1Labels = mixedMoment B raw41526step2 raw41526step2Labels := by
      have ha : raw41526step2 = raw41526step1 := by apply Matrix.ext; unfold raw41526step2 raw41526step1; decide +kernel
      have hl : raw41526step1Labels = labelEmbedding1 ∘ raw41526step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41526step1 raw41526step1Labels raw41526step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3229 node3229Labels := by rfl

theorem canonical41527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41527 raw41527Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw41527 raw41527Labels = mixedMoment B raw41527step0 raw41527step0Labels := by
      have hz : ∀ j, raw41527 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41527step0 = (fun i j => raw41527 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41527step0 raw41527; decide +kernel
      have hl : raw41527step0Labels = raw41527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41527 raw41527Labels permutation346 hz
    mixedMoment B raw41527step0 raw41527step0Labels = mixedMoment B raw41527step1 raw41527step1Labels := by
      have hz : ∀ j, raw41527step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41527step1 = (fun i j => raw41527step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41527step1 raw41527step0; decide +kernel
      have hl : raw41527step1Labels = raw41527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41527step0 raw41527step0Labels permutation56 hz
    mixedMoment B raw41527step1 raw41527step1Labels = mixedMoment B raw41527step2 raw41527step2Labels := by
      have ha : raw41527step2 = (fun i j => raw41527step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41527step2 raw41527step1; decide +kernel
      have hl : raw41527step2Labels = raw41527step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41527step1 raw41527step1Labels permutation8 permutation3
    mixedMoment B raw41527step2 raw41527step2Labels = mixedMoment B raw41527step3 raw41527step3Labels := by
      have ha : raw41527step3 = raw41527step2 := by apply Matrix.ext; unfold raw41527step3 raw41527step2; decide +kernel
      have hl : raw41527step2Labels = labelEmbedding7 ∘ raw41527step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41527step2 raw41527step2Labels raw41527step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical41528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41528 raw41528Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw41528 raw41528Labels = mixedMoment B raw41528step0 raw41528step0Labels := by
      have hz : ∀ j, raw41528 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41528step0 = (fun i j => raw41528 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41528step0 raw41528; decide +kernel
      have hl : raw41528step0Labels = raw41528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41528 raw41528Labels permutation346 hz
    mixedMoment B raw41528step0 raw41528step0Labels = mixedMoment B raw41528step1 raw41528step1Labels := by
      have hz : ∀ j, raw41528step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41528step1 = (fun i j => raw41528step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41528step1 raw41528step0; decide +kernel
      have hl : raw41528step1Labels = raw41528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41528step0 raw41528step0Labels permutation56 hz
    mixedMoment B raw41528step1 raw41528step1Labels = mixedMoment B raw41528step2 raw41528step2Labels := by
      have ha : raw41528step2 = (fun i j => raw41528step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41528step2 raw41528step1; decide +kernel
      have hl : raw41528step2Labels = raw41528step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41528step1 raw41528step1Labels permutation12 permutation4
    mixedMoment B raw41528step2 raw41528step2Labels = mixedMoment B raw41528step3 raw41528step3Labels := by
      have ha : raw41528step3 = -raw41528step2 := by apply Matrix.ext; change ∀ i j, raw41528step3 i j = -(raw41528step2 i j); unfold raw41528step3 raw41528step2; decide +kernel
      have hl : raw41528step3Labels = raw41528step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41528step3 raw41528step3Labels = mixedMoment B raw41528step4 raw41528step4Labels := by
      have ha : raw41528step4 = raw41528step3 := by apply Matrix.ext; unfold raw41528step4 raw41528step3; decide +kernel
      have hl : raw41528step3Labels = labelEmbedding1 ∘ raw41528step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41528step3 raw41528step3Labels raw41528step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3225 node3225Labels := by rfl

theorem canonical41529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41529 raw41529Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw41529 raw41529Labels = mixedMoment B raw41529step0 raw41529step0Labels := by
      have hz : ∀ j, raw41529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41529step0 = (fun i j => raw41529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41529step0 raw41529; decide +kernel
      have hl : raw41529step0Labels = raw41529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41529 raw41529Labels permutation346 hz
    mixedMoment B raw41529step0 raw41529step0Labels = mixedMoment B raw41529step1 raw41529step1Labels := by
      have hz : ∀ j, raw41529step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41529step1 = (fun i j => raw41529step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41529step1 raw41529step0; decide +kernel
      have hl : raw41529step1Labels = raw41529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41529step0 raw41529step0Labels permutation56 hz
    mixedMoment B raw41529step1 raw41529step1Labels = mixedMoment B raw41529step2 raw41529step2Labels := by
      have ha : raw41529step2 = (fun i j => raw41529step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41529step2 raw41529step1; decide +kernel
      have hl : raw41529step2Labels = raw41529step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41529step1 raw41529step1Labels permutation8 permutation3
    mixedMoment B raw41529step2 raw41529step2Labels = mixedMoment B raw41529step3 raw41529step3Labels := by
      have ha : raw41529step3 = raw41529step2 := by apply Matrix.ext; unfold raw41529step3 raw41529step2; decide +kernel
      have hl : raw41529step2Labels = labelEmbedding7 ∘ raw41529step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41529step2 raw41529step2Labels raw41529step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical41530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41530 raw41530Labels = mixedMoment B node3224 node3224Labels := by
  calc
    mixedMoment B raw41530 raw41530Labels = mixedMoment B raw41530step0 raw41530step0Labels := by
      have hz : ∀ j, raw41530 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41530step0 = (fun i j => raw41530 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41530step0 raw41530; decide +kernel
      have hl : raw41530step0Labels = raw41530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41530 raw41530Labels permutation346 hz
    mixedMoment B raw41530step0 raw41530step0Labels = mixedMoment B raw41530step1 raw41530step1Labels := by
      have hz : ∀ j, raw41530step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41530step1 = (fun i j => raw41530step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41530step1 raw41530step0; decide +kernel
      have hl : raw41530step1Labels = raw41530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41530step0 raw41530step0Labels permutation56 hz
    mixedMoment B raw41530step1 raw41530step1Labels = mixedMoment B raw41530step2 raw41530step2Labels := by
      have ha : raw41530step2 = raw41530step1 := by apply Matrix.ext; unfold raw41530step2 raw41530step1; decide +kernel
      have hl : raw41530step1Labels = labelEmbedding1 ∘ raw41530step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41530step1 raw41530step1Labels raw41530step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3224 node3224Labels := by rfl

theorem canonical41531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41531 raw41531Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw41531 raw41531Labels = mixedMoment B raw41531step0 raw41531step0Labels := by
      have hz : ∀ j, raw41531 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41531step0 = (fun i j => raw41531 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41531step0 raw41531; decide +kernel
      have hl : raw41531step0Labels = raw41531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41531 raw41531Labels permutation346 hz
    mixedMoment B raw41531step0 raw41531step0Labels = mixedMoment B raw41531step1 raw41531step1Labels := by
      have hz : ∀ j, raw41531step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41531step1 = (fun i j => raw41531step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41531step1 raw41531step0; decide +kernel
      have hl : raw41531step1Labels = raw41531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41531step0 raw41531step0Labels permutation56 hz
    mixedMoment B raw41531step1 raw41531step1Labels = mixedMoment B raw41531step2 raw41531step2Labels := by
      have ha : raw41531step2 = (fun i j => raw41531step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41531step2 raw41531step1; decide +kernel
      have hl : raw41531step2Labels = raw41531step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41531step1 raw41531step1Labels permutation8 permutation3
    mixedMoment B raw41531step2 raw41531step2Labels = mixedMoment B raw41531step3 raw41531step3Labels := by
      have ha : raw41531step3 = raw41531step2 := by apply Matrix.ext; unfold raw41531step3 raw41531step2; decide +kernel
      have hl : raw41531step2Labels = labelEmbedding7 ∘ raw41531step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41531step2 raw41531step2Labels raw41531step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

theorem canonical41532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41532 raw41532Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw41532 raw41532Labels = mixedMoment B raw41532step0 raw41532step0Labels := by
      have hz : ∀ j, raw41532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41532step0 = (fun i j => raw41532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41532step0 raw41532; decide +kernel
      have hl : raw41532step0Labels = raw41532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41532 raw41532Labels permutation346 hz
    mixedMoment B raw41532step0 raw41532step0Labels = mixedMoment B raw41532step1 raw41532step1Labels := by
      have hz : ∀ j, raw41532step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41532step1 = (fun i j => raw41532step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41532step1 raw41532step0; decide +kernel
      have hl : raw41532step1Labels = raw41532step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41532step0 raw41532step0Labels permutation56 hz
    mixedMoment B raw41532step1 raw41532step1Labels = mixedMoment B raw41532step2 raw41532step2Labels := by
      have ha : raw41532step2 = (fun i j => raw41532step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41532step2 raw41532step1; decide +kernel
      have hl : raw41532step2Labels = raw41532step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41532step1 raw41532step1Labels permutation29 permutation4
    mixedMoment B raw41532step2 raw41532step2Labels = mixedMoment B raw41532step3 raw41532step3Labels := by
      have ha : raw41532step3 = raw41532step2 := by apply Matrix.ext; unfold raw41532step3 raw41532step2; decide +kernel
      have hl : raw41532step2Labels = labelEmbedding1 ∘ raw41532step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41532step2 raw41532step2Labels raw41532step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2755 node2755Labels := by rfl

theorem canonical41533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41533 raw41533Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw41533 raw41533Labels = mixedMoment B raw41533step0 raw41533step0Labels := by
      have hz : ∀ j, raw41533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41533step0 = (fun i j => raw41533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41533step0 raw41533; decide +kernel
      have hl : raw41533step0Labels = raw41533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41533 raw41533Labels permutation346 hz
    mixedMoment B raw41533step0 raw41533step0Labels = mixedMoment B raw41533step1 raw41533step1Labels := by
      have hz : ∀ j, raw41533step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41533step1 = (fun i j => raw41533step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41533step1 raw41533step0; decide +kernel
      have hl : raw41533step1Labels = raw41533step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41533step0 raw41533step0Labels permutation56 hz
    mixedMoment B raw41533step1 raw41533step1Labels = mixedMoment B raw41533step2 raw41533step2Labels := by
      have ha : raw41533step2 = (fun i j => raw41533step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41533step2 raw41533step1; decide +kernel
      have hl : raw41533step2Labels = raw41533step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41533step1 raw41533step1Labels permutation8 permutation5
    mixedMoment B raw41533step2 raw41533step2Labels = mixedMoment B raw41533step3 raw41533step3Labels := by
      have ha : raw41533step3 = -raw41533step2 := by apply Matrix.ext; change ∀ i j, raw41533step3 i j = -(raw41533step2 i j); unfold raw41533step3 raw41533step2; decide +kernel
      have hl : raw41533step3Labels = raw41533step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41533step3 raw41533step3Labels = mixedMoment B raw41533step4 raw41533step4Labels := by
      have ha : raw41533step4 = raw41533step3 := by apply Matrix.ext; unfold raw41533step4 raw41533step3; decide +kernel
      have hl : raw41533step3Labels = labelEmbedding9 ∘ raw41533step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41533step3 raw41533step3Labels raw41533step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical41534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41534 raw41534Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw41534 raw41534Labels = mixedMoment B raw41534step0 raw41534step0Labels := by
      have hz : ∀ j, raw41534 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41534step0 = (fun i j => raw41534 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41534step0 raw41534; decide +kernel
      have hl : raw41534step0Labels = raw41534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41534 raw41534Labels permutation346 hz
    mixedMoment B raw41534step0 raw41534step0Labels = mixedMoment B raw41534step1 raw41534step1Labels := by
      have hz : ∀ j, raw41534step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41534step1 = (fun i j => raw41534step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41534step1 raw41534step0; decide +kernel
      have hl : raw41534step1Labels = raw41534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41534step0 raw41534step0Labels permutation56 hz
    mixedMoment B raw41534step1 raw41534step1Labels = mixedMoment B raw41534step2 raw41534step2Labels := by
      have ha : raw41534step2 = (fun i j => raw41534step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41534step2 raw41534step1; decide +kernel
      have hl : raw41534step2Labels = raw41534step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41534step1 raw41534step1Labels permutation8 permutation4
    mixedMoment B raw41534step2 raw41534step2Labels = mixedMoment B raw41534step3 raw41534step3Labels := by
      have ha : raw41534step3 = -raw41534step2 := by apply Matrix.ext; change ∀ i j, raw41534step3 i j = -(raw41534step2 i j); unfold raw41534step3 raw41534step2; decide +kernel
      have hl : raw41534step3Labels = raw41534step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41534step3 raw41534step3Labels = mixedMoment B raw41534step4 raw41534step4Labels := by
      have ha : raw41534step4 = raw41534step3 := by apply Matrix.ext; unfold raw41534step4 raw41534step3; decide +kernel
      have hl : raw41534step3Labels = labelEmbedding1 ∘ raw41534step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41534step3 raw41534step3Labels raw41534step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3229 node3229Labels := by rfl

theorem canonical41535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41535 raw41535Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw41535 raw41535Labels = mixedMoment B raw41535step0 raw41535step0Labels := by
      have hz : ∀ j, raw41535 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41535step0 = (fun i j => raw41535 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41535step0 raw41535; decide +kernel
      have hl : raw41535step0Labels = raw41535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41535 raw41535Labels permutation346 hz
    mixedMoment B raw41535step0 raw41535step0Labels = mixedMoment B raw41535step1 raw41535step1Labels := by
      have hz : ∀ j, raw41535step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41535step1 = (fun i j => raw41535step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41535step1 raw41535step0; decide +kernel
      have hl : raw41535step1Labels = raw41535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41535step0 raw41535step0Labels permutation56 hz
    mixedMoment B raw41535step1 raw41535step1Labels = mixedMoment B raw41535step2 raw41535step2Labels := by
      have ha : raw41535step2 = (fun i j => raw41535step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41535step2 raw41535step1; decide +kernel
      have hl : raw41535step2Labels = raw41535step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41535step1 raw41535step1Labels permutation8 permutation5
    mixedMoment B raw41535step2 raw41535step2Labels = mixedMoment B raw41535step3 raw41535step3Labels := by
      have ha : raw41535step3 = -raw41535step2 := by apply Matrix.ext; change ∀ i j, raw41535step3 i j = -(raw41535step2 i j); unfold raw41535step3 raw41535step2; decide +kernel
      have hl : raw41535step3Labels = raw41535step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41535step3 raw41535step3Labels = mixedMoment B raw41535step4 raw41535step4Labels := by
      have ha : raw41535step4 = raw41535step3 := by apply Matrix.ext; unfold raw41535step4 raw41535step3; decide +kernel
      have hl : raw41535step3Labels = labelEmbedding9 ∘ raw41535step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41535step3 raw41535step3Labels raw41535step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2080 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2080) =
      Integer.Sparse.eval keyMomentRow2080 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2080).leftCharge (GramAssembly.key 2080).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2818) := by
    have ha : gramCharges (GramAssembly.key 2080).leftCharge (GramAssembly.key 2080).rightCharge = raw41493 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41493Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41493 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2080).leftCharge (GramAssembly.key 2080).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2080, Integer.Sparse.eval]

theorem keyMoment2081 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2081) =
      Integer.Sparse.eval keyMomentRow2081 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2081).leftCharge (GramAssembly.key 2081).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3694) := by
    have ha : gramCharges (GramAssembly.key 2081).leftCharge (GramAssembly.key 2081).rightCharge = raw41494 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41494Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41494 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2081).leftCharge (GramAssembly.key 2081).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2081, Integer.Sparse.eval]

theorem keyMoment2082 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2082) =
      Integer.Sparse.eval keyMomentRow2082 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2082).leftCharge (GramAssembly.key 2082).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3672) := by
    have ha : gramCharges (GramAssembly.key 2082).leftCharge (GramAssembly.key 2082).rightCharge = raw41495 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41495Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41495 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2082).leftCharge (GramAssembly.key 2082).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2082, Integer.Sparse.eval]

theorem keyMoment2083 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2083) =
      Integer.Sparse.eval keyMomentRow2083 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2083).leftCharge (GramAssembly.key 2083).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1139) := by
    have ha : gramCharges (GramAssembly.key 2083).leftCharge (GramAssembly.key 2083).rightCharge = raw41496 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41496Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41496 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2083).leftCharge (GramAssembly.key 2083).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2083, Integer.Sparse.eval]

theorem keyMoment2084 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2084) =
      Integer.Sparse.eval keyMomentRow2084 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2084).leftCharge (GramAssembly.key 2084).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2489) := by
    have ha : gramCharges (GramAssembly.key 2084).leftCharge (GramAssembly.key 2084).rightCharge = raw41497 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41497Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41497 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2084).leftCharge (GramAssembly.key 2084).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2084, Integer.Sparse.eval]

theorem keyMoment2085 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2085) =
      Integer.Sparse.eval keyMomentRow2085 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2085).leftCharge (GramAssembly.key 2085).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2432) := by
    have ha : gramCharges (GramAssembly.key 2085).leftCharge (GramAssembly.key 2085).rightCharge = raw41498 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41498Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41498 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2085).leftCharge (GramAssembly.key 2085).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2085, Integer.Sparse.eval]

theorem keyMoment2086 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2086) =
      Integer.Sparse.eval keyMomentRow2086 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2086).leftCharge (GramAssembly.key 2086).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 614) := by
    have ha : gramCharges (GramAssembly.key 2086).leftCharge (GramAssembly.key 2086).rightCharge = raw41499 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41499Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41499 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2086).leftCharge (GramAssembly.key 2086).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2086, Integer.Sparse.eval]

theorem keyMoment2087 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2087) =
      Integer.Sparse.eval keyMomentRow2087 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2087).leftCharge (GramAssembly.key 2087).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1050) := by
    have ha : gramCharges (GramAssembly.key 2087).leftCharge (GramAssembly.key 2087).rightCharge = raw41500 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41500Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41500 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2087).leftCharge (GramAssembly.key 2087).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2087, Integer.Sparse.eval]

theorem keyMoment2088 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2088) =
      Integer.Sparse.eval keyMomentRow2088 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2088).leftCharge (GramAssembly.key 2088).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 933) := by
    have ha : gramCharges (GramAssembly.key 2088).leftCharge (GramAssembly.key 2088).rightCharge = raw41501 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41501Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41501 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2088).leftCharge (GramAssembly.key 2088).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2088, Integer.Sparse.eval]

theorem keyMoment2089 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2089) =
      Integer.Sparse.eval keyMomentRow2089 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2089).leftCharge (GramAssembly.key 2089).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2342) := by
    have ha : gramCharges (GramAssembly.key 2089).leftCharge (GramAssembly.key 2089).rightCharge = raw41502 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41502Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41502 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2089).leftCharge (GramAssembly.key 2089).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2089, Integer.Sparse.eval]

theorem keyMoment2090 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2090) =
      Integer.Sparse.eval keyMomentRow2090 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2090).leftCharge (GramAssembly.key 2090).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1818) := by
    have ha : gramCharges (GramAssembly.key 2090).leftCharge (GramAssembly.key 2090).rightCharge = raw41503 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41503Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41503 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2090).leftCharge (GramAssembly.key 2090).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2090, Integer.Sparse.eval]

theorem keyMoment2091 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2091) =
      Integer.Sparse.eval keyMomentRow2091 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2091).leftCharge (GramAssembly.key 2091).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2341) := by
    have ha : gramCharges (GramAssembly.key 2091).leftCharge (GramAssembly.key 2091).rightCharge = raw41504 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41504Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41504 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2091).leftCharge (GramAssembly.key 2091).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2091, Integer.Sparse.eval]

theorem keyMoment2092 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2092) =
      Integer.Sparse.eval keyMomentRow2092 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2092).leftCharge (GramAssembly.key 2092).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2330) := by
    have ha : gramCharges (GramAssembly.key 2092).leftCharge (GramAssembly.key 2092).rightCharge = raw41505 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41505Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41505 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2092).leftCharge (GramAssembly.key 2092).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2092, Integer.Sparse.eval]

theorem keyMoment2093 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2093) =
      Integer.Sparse.eval keyMomentRow2093 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2093).leftCharge (GramAssembly.key 2093).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2345) := by
    have ha : gramCharges (GramAssembly.key 2093).leftCharge (GramAssembly.key 2093).rightCharge = raw41506 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41506Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41506 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2093).leftCharge (GramAssembly.key 2093).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2093, Integer.Sparse.eval]

theorem keyMoment2094 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2094) =
      Integer.Sparse.eval keyMomentRow2094 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2094).leftCharge (GramAssembly.key 2094).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2337) := by
    have ha : gramCharges (GramAssembly.key 2094).leftCharge (GramAssembly.key 2094).rightCharge = raw41507 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41507Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41507 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2094).leftCharge (GramAssembly.key 2094).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2094, Integer.Sparse.eval]

theorem keyMoment2095 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2095) =
      Integer.Sparse.eval keyMomentRow2095 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2095).leftCharge (GramAssembly.key 2095).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2338) := by
    have ha : gramCharges (GramAssembly.key 2095).leftCharge (GramAssembly.key 2095).rightCharge = raw41508 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41508Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41508 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2095).leftCharge (GramAssembly.key 2095).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2095, Integer.Sparse.eval]

theorem keyMoment2096 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2096) =
      Integer.Sparse.eval keyMomentRow2096 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2096).leftCharge (GramAssembly.key 2096).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2339) := by
    have ha : gramCharges (GramAssembly.key 2096).leftCharge (GramAssembly.key 2096).rightCharge = raw41509 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41509Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41509 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2096).leftCharge (GramAssembly.key 2096).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2096, Integer.Sparse.eval]

theorem keyMoment2097 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2097) =
      Integer.Sparse.eval keyMomentRow2097 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2097).leftCharge (GramAssembly.key 2097).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1144) := by
    have ha : gramCharges (GramAssembly.key 2097).leftCharge (GramAssembly.key 2097).rightCharge = raw41510 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41510Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41510 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2097).leftCharge (GramAssembly.key 2097).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2097, Integer.Sparse.eval]

theorem keyMoment2098 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2098) =
      Integer.Sparse.eval keyMomentRow2098 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2098).leftCharge (GramAssembly.key 2098).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2334) := by
    have ha : gramCharges (GramAssembly.key 2098).leftCharge (GramAssembly.key 2098).rightCharge = raw41511 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41511Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41511 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2098).leftCharge (GramAssembly.key 2098).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2098, Integer.Sparse.eval]

theorem keyMoment2099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2099) =
      Integer.Sparse.eval keyMomentRow2099 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2099).leftCharge (GramAssembly.key 2099).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 619) := by
    have ha : gramCharges (GramAssembly.key 2099).leftCharge (GramAssembly.key 2099).rightCharge = raw41512 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41512Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41512 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2099).leftCharge (GramAssembly.key 2099).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2099, Integer.Sparse.eval]

theorem keyMoment2100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2100) =
      Integer.Sparse.eval keyMomentRow2100 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2100).leftCharge (GramAssembly.key 2100).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2344) := by
    have ha : gramCharges (GramAssembly.key 2100).leftCharge (GramAssembly.key 2100).rightCharge = raw41513 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41513Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41513 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2100).leftCharge (GramAssembly.key 2100).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2100, Integer.Sparse.eval]

theorem keyMoment2101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2101) =
      Integer.Sparse.eval keyMomentRow2101 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2101).leftCharge (GramAssembly.key 2101).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2) := by
    have ha : gramCharges (GramAssembly.key 2101).leftCharge (GramAssembly.key 2101).rightCharge = raw41514 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41514Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41514 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2101).leftCharge (GramAssembly.key 2101).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4085) := by
    have ha : gramCharges (GramAssembly.key 2101).leftCharge (GramAssembly.key 2101).rightCharge = raw41515 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41515Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41515 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2101).leftCharge (GramAssembly.key 2101).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2101).leftCharge (GramAssembly.key 2101).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2101, Integer.Sparse.eval]
  ring

theorem keyMoment2102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2102) =
      Integer.Sparse.eval keyMomentRow2102 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2102).leftCharge (GramAssembly.key 2102).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3114) := by
    have ha : gramCharges (GramAssembly.key 2102).leftCharge (GramAssembly.key 2102).rightCharge = raw41516 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41516Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41516 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2102).leftCharge (GramAssembly.key 2102).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4897) := by
    have ha : gramCharges (GramAssembly.key 2102).leftCharge (GramAssembly.key 2102).rightCharge = raw41517 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41517Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41517 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2102).leftCharge (GramAssembly.key 2102).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2102).leftCharge (GramAssembly.key 2102).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2102, Integer.Sparse.eval]
  ring

theorem keyMoment2103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2103) =
      Integer.Sparse.eval keyMomentRow2103 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2103).leftCharge (GramAssembly.key 2103).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1) := by
    have ha : gramCharges (GramAssembly.key 2103).leftCharge (GramAssembly.key 2103).rightCharge = raw41518 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41518Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41518 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2103).leftCharge (GramAssembly.key 2103).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4084) := by
    have ha : gramCharges (GramAssembly.key 2103).leftCharge (GramAssembly.key 2103).rightCharge = raw41519 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41519Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41519 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2103).leftCharge (GramAssembly.key 2103).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2103).leftCharge (GramAssembly.key 2103).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2103, Integer.Sparse.eval]
  ring

theorem keyMoment2104 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2104) =
      Integer.Sparse.eval keyMomentRow2104 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2104).leftCharge (GramAssembly.key 2104).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3231) := by
    have ha : gramCharges (GramAssembly.key 2104).leftCharge (GramAssembly.key 2104).rightCharge = raw41520 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41520Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41520 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2104).leftCharge (GramAssembly.key 2104).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4901) := by
    have ha : gramCharges (GramAssembly.key 2104).leftCharge (GramAssembly.key 2104).rightCharge = raw41521 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41521Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41521 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2104).leftCharge (GramAssembly.key 2104).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2104).leftCharge (GramAssembly.key 2104).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2104, Integer.Sparse.eval]
  ring

theorem keyMoment2105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2105) =
      Integer.Sparse.eval keyMomentRow2105 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2105).leftCharge (GramAssembly.key 2105).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2778) := by
    have ha : gramCharges (GramAssembly.key 2105).leftCharge (GramAssembly.key 2105).rightCharge = raw41522 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41522Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41522 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2105).leftCharge (GramAssembly.key 2105).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4899) := by
    have ha : gramCharges (GramAssembly.key 2105).leftCharge (GramAssembly.key 2105).rightCharge = raw41523 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41523Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41523 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2105).leftCharge (GramAssembly.key 2105).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2105).leftCharge (GramAssembly.key 2105).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2105, Integer.Sparse.eval]
  ring

theorem keyMoment2106 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2106) =
      Integer.Sparse.eval keyMomentRow2106 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2106).leftCharge (GramAssembly.key 2106).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3230) := by
    have ha : gramCharges (GramAssembly.key 2106).leftCharge (GramAssembly.key 2106).rightCharge = raw41524 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41524Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41524 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2106).leftCharge (GramAssembly.key 2106).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4894) := by
    have ha : gramCharges (GramAssembly.key 2106).leftCharge (GramAssembly.key 2106).rightCharge = raw41525 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41525Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41525 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2106).leftCharge (GramAssembly.key 2106).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2106).leftCharge (GramAssembly.key 2106).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2106, Integer.Sparse.eval]
  ring

theorem keyMoment2107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2107) =
      Integer.Sparse.eval keyMomentRow2107 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2107).leftCharge (GramAssembly.key 2107).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3229) := by
    have ha : gramCharges (GramAssembly.key 2107).leftCharge (GramAssembly.key 2107).rightCharge = raw41526 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41526Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41526 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2107).leftCharge (GramAssembly.key 2107).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4895) := by
    have ha : gramCharges (GramAssembly.key 2107).leftCharge (GramAssembly.key 2107).rightCharge = raw41527 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41527Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41527 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2107).leftCharge (GramAssembly.key 2107).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2107).leftCharge (GramAssembly.key 2107).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2107, Integer.Sparse.eval]
  ring

theorem keyMoment2108 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2108) =
      Integer.Sparse.eval keyMomentRow2108 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2108).leftCharge (GramAssembly.key 2108).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3225) := by
    have ha : gramCharges (GramAssembly.key 2108).leftCharge (GramAssembly.key 2108).rightCharge = raw41528 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41528Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41528 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2108).leftCharge (GramAssembly.key 2108).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4896) := by
    have ha : gramCharges (GramAssembly.key 2108).leftCharge (GramAssembly.key 2108).rightCharge = raw41529 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41529Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41529 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2108).leftCharge (GramAssembly.key 2108).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2108).leftCharge (GramAssembly.key 2108).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2108, Integer.Sparse.eval]
  ring

theorem keyMoment2109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2109) =
      Integer.Sparse.eval keyMomentRow2109 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2109).leftCharge (GramAssembly.key 2109).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3224) := by
    have ha : gramCharges (GramAssembly.key 2109).leftCharge (GramAssembly.key 2109).rightCharge = raw41530 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41530Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41530 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2109).leftCharge (GramAssembly.key 2109).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4898) := by
    have ha : gramCharges (GramAssembly.key 2109).leftCharge (GramAssembly.key 2109).rightCharge = raw41531 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41531Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41531 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2109).leftCharge (GramAssembly.key 2109).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2109).leftCharge (GramAssembly.key 2109).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2109, Integer.Sparse.eval]
  ring

theorem keyMoment2110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2110) =
      Integer.Sparse.eval keyMomentRow2110 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2110).leftCharge (GramAssembly.key 2110).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2755) := by
    have ha : gramCharges (GramAssembly.key 2110).leftCharge (GramAssembly.key 2110).rightCharge = raw41532 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41532Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41532 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2110).leftCharge (GramAssembly.key 2110).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4890) := by
    have ha : gramCharges (GramAssembly.key 2110).leftCharge (GramAssembly.key 2110).rightCharge = raw41533 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41533Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41533 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2110).leftCharge (GramAssembly.key 2110).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2110).leftCharge (GramAssembly.key 2110).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2110, Integer.Sparse.eval]
  ring

theorem keyMoment2111 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2111) =
      Integer.Sparse.eval keyMomentRow2111 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2111).leftCharge (GramAssembly.key 2111).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3229) := by
    have ha : gramCharges (GramAssembly.key 2111).leftCharge (GramAssembly.key 2111).rightCharge = raw41534 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41534Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41534 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2111).leftCharge (GramAssembly.key 2111).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4895) := by
    have ha : gramCharges (GramAssembly.key 2111).leftCharge (GramAssembly.key 2111).rightCharge = raw41535 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41535Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41535 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2111).leftCharge (GramAssembly.key 2111).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2111).leftCharge (GramAssembly.key 2111).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2111, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2080 : keyMomentRows (2080 : Fin 2886) =
    keyMomentRow2080 := by decide +kernel

theorem keyMomentRowsAt2081 : keyMomentRows (2081 : Fin 2886) =
    keyMomentRow2081 := by decide +kernel

theorem keyMomentRowsAt2082 : keyMomentRows (2082 : Fin 2886) =
    keyMomentRow2082 := by decide +kernel

theorem keyMomentRowsAt2083 : keyMomentRows (2083 : Fin 2886) =
    keyMomentRow2083 := by decide +kernel

theorem keyMomentRowsAt2084 : keyMomentRows (2084 : Fin 2886) =
    keyMomentRow2084 := by decide +kernel

theorem keyMomentRowsAt2085 : keyMomentRows (2085 : Fin 2886) =
    keyMomentRow2085 := by decide +kernel

theorem keyMomentRowsAt2086 : keyMomentRows (2086 : Fin 2886) =
    keyMomentRow2086 := by decide +kernel

theorem keyMomentRowsAt2087 : keyMomentRows (2087 : Fin 2886) =
    keyMomentRow2087 := by decide +kernel

theorem keyMomentRowsAt2088 : keyMomentRows (2088 : Fin 2886) =
    keyMomentRow2088 := by decide +kernel

theorem keyMomentRowsAt2089 : keyMomentRows (2089 : Fin 2886) =
    keyMomentRow2089 := by decide +kernel

theorem keyMomentRowsAt2090 : keyMomentRows (2090 : Fin 2886) =
    keyMomentRow2090 := by decide +kernel

theorem keyMomentRowsAt2091 : keyMomentRows (2091 : Fin 2886) =
    keyMomentRow2091 := by decide +kernel

theorem keyMomentRowsAt2092 : keyMomentRows (2092 : Fin 2886) =
    keyMomentRow2092 := by decide +kernel

theorem keyMomentRowsAt2093 : keyMomentRows (2093 : Fin 2886) =
    keyMomentRow2093 := by decide +kernel

theorem keyMomentRowsAt2094 : keyMomentRows (2094 : Fin 2886) =
    keyMomentRow2094 := by decide +kernel

theorem keyMomentRowsAt2095 : keyMomentRows (2095 : Fin 2886) =
    keyMomentRow2095 := by decide +kernel

theorem keyMomentRowsAt2096 : keyMomentRows (2096 : Fin 2886) =
    keyMomentRow2096 := by decide +kernel

theorem keyMomentRowsAt2097 : keyMomentRows (2097 : Fin 2886) =
    keyMomentRow2097 := by decide +kernel

theorem keyMomentRowsAt2098 : keyMomentRows (2098 : Fin 2886) =
    keyMomentRow2098 := by decide +kernel

theorem keyMomentRowsAt2099 : keyMomentRows (2099 : Fin 2886) =
    keyMomentRow2099 := by decide +kernel

theorem keyMomentRowsAt2100 : keyMomentRows (2100 : Fin 2886) =
    keyMomentRow2100 := by decide +kernel

theorem keyMomentRowsAt2101 : keyMomentRows (2101 : Fin 2886) =
    keyMomentRow2101 := by decide +kernel

theorem keyMomentRowsAt2102 : keyMomentRows (2102 : Fin 2886) =
    keyMomentRow2102 := by decide +kernel

theorem keyMomentRowsAt2103 : keyMomentRows (2103 : Fin 2886) =
    keyMomentRow2103 := by decide +kernel

theorem keyMomentRowsAt2104 : keyMomentRows (2104 : Fin 2886) =
    keyMomentRow2104 := by decide +kernel

theorem keyMomentRowsAt2105 : keyMomentRows (2105 : Fin 2886) =
    keyMomentRow2105 := by decide +kernel

theorem keyMomentRowsAt2106 : keyMomentRows (2106 : Fin 2886) =
    keyMomentRow2106 := by decide +kernel

theorem keyMomentRowsAt2107 : keyMomentRows (2107 : Fin 2886) =
    keyMomentRow2107 := by decide +kernel

theorem keyMomentRowsAt2108 : keyMomentRows (2108 : Fin 2886) =
    keyMomentRow2108 := by decide +kernel

theorem keyMomentRowsAt2109 : keyMomentRows (2109 : Fin 2886) =
    keyMomentRow2109 := by decide +kernel

theorem keyMomentRowsAt2110 : keyMomentRows (2110 : Fin 2886) =
    keyMomentRow2110 := by decide +kernel

theorem keyMomentRowsAt2111 : keyMomentRows (2111 : Fin 2886) =
    keyMomentRow2111 := by decide +kernel

theorem keyMomentChunkSound65_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 65) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2080 ∨ k.val = 2081 ∨ k.val = 2082 ∨ k.val = 2083 ∨ k.val = 2084 ∨ k.val = 2085 ∨ k.val = 2086 ∨ k.val = 2087 ∨ k.val = 2088 ∨ k.val = 2089 ∨ k.val = 2090 ∨ k.val = 2091 ∨ k.val = 2092 ∨ k.val = 2093 ∨ k.val = 2094 ∨ k.val = 2095 ∨ k.val = 2096 ∨ k.val = 2097 ∨ k.val = 2098 ∨ k.val = 2099 ∨ k.val = 2100 ∨ k.val = 2101 ∨ k.val = 2102 ∨ k.val = 2103 ∨ k.val = 2104 ∨ k.val = 2105 ∨ k.val = 2106 ∨ k.val = 2107 ∨ k.val = 2108 ∨ k.val = 2109 ∨ k.val = 2110 ∨ k.val = 2111 := by omega
  rcases heq with h2080 | h2081 | h2082 | h2083 | h2084 | h2085 | h2086 | h2087 | h2088 | h2089 | h2090 | h2091 | h2092 | h2093 | h2094 | h2095 | h2096 | h2097 | h2098 | h2099 | h2100 | h2101 | h2102 | h2103 | h2104 | h2105 | h2106 | h2107 | h2108 | h2109 | h2110 | h2111
  · have he : k = (2080 : Fin 2886) := Fin.ext h2080
    subst k
    rw [keyMomentRowsAt2080]
    exact keyMoment2080 B hB
  · have he : k = (2081 : Fin 2886) := Fin.ext h2081
    subst k
    rw [keyMomentRowsAt2081]
    exact keyMoment2081 B hB
  · have he : k = (2082 : Fin 2886) := Fin.ext h2082
    subst k
    rw [keyMomentRowsAt2082]
    exact keyMoment2082 B hB
  · have he : k = (2083 : Fin 2886) := Fin.ext h2083
    subst k
    rw [keyMomentRowsAt2083]
    exact keyMoment2083 B hB
  · have he : k = (2084 : Fin 2886) := Fin.ext h2084
    subst k
    rw [keyMomentRowsAt2084]
    exact keyMoment2084 B hB
  · have he : k = (2085 : Fin 2886) := Fin.ext h2085
    subst k
    rw [keyMomentRowsAt2085]
    exact keyMoment2085 B hB
  · have he : k = (2086 : Fin 2886) := Fin.ext h2086
    subst k
    rw [keyMomentRowsAt2086]
    exact keyMoment2086 B hB
  · have he : k = (2087 : Fin 2886) := Fin.ext h2087
    subst k
    rw [keyMomentRowsAt2087]
    exact keyMoment2087 B hB
  · have he : k = (2088 : Fin 2886) := Fin.ext h2088
    subst k
    rw [keyMomentRowsAt2088]
    exact keyMoment2088 B hB
  · have he : k = (2089 : Fin 2886) := Fin.ext h2089
    subst k
    rw [keyMomentRowsAt2089]
    exact keyMoment2089 B hB
  · have he : k = (2090 : Fin 2886) := Fin.ext h2090
    subst k
    rw [keyMomentRowsAt2090]
    exact keyMoment2090 B hB
  · have he : k = (2091 : Fin 2886) := Fin.ext h2091
    subst k
    rw [keyMomentRowsAt2091]
    exact keyMoment2091 B hB
  · have he : k = (2092 : Fin 2886) := Fin.ext h2092
    subst k
    rw [keyMomentRowsAt2092]
    exact keyMoment2092 B hB
  · have he : k = (2093 : Fin 2886) := Fin.ext h2093
    subst k
    rw [keyMomentRowsAt2093]
    exact keyMoment2093 B hB
  · have he : k = (2094 : Fin 2886) := Fin.ext h2094
    subst k
    rw [keyMomentRowsAt2094]
    exact keyMoment2094 B hB
  · have he : k = (2095 : Fin 2886) := Fin.ext h2095
    subst k
    rw [keyMomentRowsAt2095]
    exact keyMoment2095 B hB
  · have he : k = (2096 : Fin 2886) := Fin.ext h2096
    subst k
    rw [keyMomentRowsAt2096]
    exact keyMoment2096 B hB
  · have he : k = (2097 : Fin 2886) := Fin.ext h2097
    subst k
    rw [keyMomentRowsAt2097]
    exact keyMoment2097 B hB
  · have he : k = (2098 : Fin 2886) := Fin.ext h2098
    subst k
    rw [keyMomentRowsAt2098]
    exact keyMoment2098 B hB
  · have he : k = (2099 : Fin 2886) := Fin.ext h2099
    subst k
    rw [keyMomentRowsAt2099]
    exact keyMoment2099 B hB
  · have he : k = (2100 : Fin 2886) := Fin.ext h2100
    subst k
    rw [keyMomentRowsAt2100]
    exact keyMoment2100 B hB
  · have he : k = (2101 : Fin 2886) := Fin.ext h2101
    subst k
    rw [keyMomentRowsAt2101]
    exact keyMoment2101 B hB
  · have he : k = (2102 : Fin 2886) := Fin.ext h2102
    subst k
    rw [keyMomentRowsAt2102]
    exact keyMoment2102 B hB
  · have he : k = (2103 : Fin 2886) := Fin.ext h2103
    subst k
    rw [keyMomentRowsAt2103]
    exact keyMoment2103 B hB
  · have he : k = (2104 : Fin 2886) := Fin.ext h2104
    subst k
    rw [keyMomentRowsAt2104]
    exact keyMoment2104 B hB
  · have he : k = (2105 : Fin 2886) := Fin.ext h2105
    subst k
    rw [keyMomentRowsAt2105]
    exact keyMoment2105 B hB
  · have he : k = (2106 : Fin 2886) := Fin.ext h2106
    subst k
    rw [keyMomentRowsAt2106]
    exact keyMoment2106 B hB
  · have he : k = (2107 : Fin 2886) := Fin.ext h2107
    subst k
    rw [keyMomentRowsAt2107]
    exact keyMoment2107 B hB
  · have he : k = (2108 : Fin 2886) := Fin.ext h2108
    subst k
    rw [keyMomentRowsAt2108]
    exact keyMoment2108 B hB
  · have he : k = (2109 : Fin 2886) := Fin.ext h2109
    subst k
    rw [keyMomentRowsAt2109]
    exact keyMoment2109 B hB
  · have he : k = (2110 : Fin 2886) := Fin.ext h2110
    subst k
    rw [keyMomentRowsAt2110]
    exact keyMoment2110 B hB
  · have he : k = (2111 : Fin 2886) := Fin.ext h2111
    subst k
    rw [keyMomentRowsAt2111]
    exact keyMoment2111 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound65_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound65_e_oai
