-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound72_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:02:22.379914+00:00
-- url     : https://prove2.me/submissions/b2a1f9f9-1e1e-46f8-869a-479ea5530ed7

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical327
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41920 raw41920Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw41920 raw41920Labels = mixedMoment B raw41920step0 raw41920step0Labels := by
      have hz : ∀ j, raw41920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41920step0 = (fun i j => raw41920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41920step0 raw41920; decide +kernel
      have hl : raw41920step0Labels = raw41920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41920 raw41920Labels permutation346 hz
    mixedMoment B raw41920step0 raw41920step0Labels = mixedMoment B raw41920step1 raw41920step1Labels := by
      have ha : raw41920step1 = (fun i j => raw41920step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41920step1 raw41920step0; decide +kernel
      have hl : raw41920step1Labels = raw41920step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41920step0 raw41920step0Labels permutation37 permutation2
    mixedMoment B raw41920step1 raw41920step1Labels = mixedMoment B raw41920step2 raw41920step2Labels := by
      have ha : raw41920step2 = raw41920step1 := by apply Matrix.ext; unfold raw41920step2 raw41920step1; decide +kernel
      have hl : raw41920step1Labels = labelEmbedding1 ∘ raw41920step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41920step1 raw41920step1Labels raw41920step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

theorem canonical41921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41921 raw41921Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw41921 raw41921Labels = mixedMoment B raw41921step0 raw41921step0Labels := by
      have hz : ∀ j, raw41921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41921step0 = (fun i j => raw41921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41921step0 raw41921; decide +kernel
      have hl : raw41921step0Labels = raw41921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41921 raw41921Labels permutation346 hz
    mixedMoment B raw41921step0 raw41921step0Labels = mixedMoment B raw41921step1 raw41921step1Labels := by
      have ha : raw41921step1 = (fun i j => raw41921step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41921step1 raw41921step0; decide +kernel
      have hl : raw41921step1Labels = raw41921step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41921step0 raw41921step0Labels permutation51 permutation7
    mixedMoment B raw41921step1 raw41921step1Labels = mixedMoment B raw41921step2 raw41921step2Labels := by
      have ha : raw41921step2 = -raw41921step1 := by apply Matrix.ext; change ∀ i j, raw41921step2 i j = -(raw41921step1 i j); unfold raw41921step2 raw41921step1; decide +kernel
      have hl : raw41921step2Labels = raw41921step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41921step2 raw41921step2Labels = mixedMoment B raw41921step3 raw41921step3Labels := by
      have ha : raw41921step3 = raw41921step2 := by apply Matrix.ext; unfold raw41921step3 raw41921step2; decide +kernel
      have hl : raw41921step2Labels = labelEmbedding6 ∘ raw41921step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41921step2 raw41921step2Labels raw41921step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4367 node4367Labels := by rfl

theorem canonical41922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41922 raw41922Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw41922 raw41922Labels = mixedMoment B raw41922step0 raw41922step0Labels := by
      have hz : ∀ j, raw41922 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41922step0 = (fun i j => raw41922 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41922step0 raw41922; decide +kernel
      have hl : raw41922step0Labels = raw41922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41922 raw41922Labels permutation346 hz
    mixedMoment B raw41922step0 raw41922step0Labels = mixedMoment B raw41922step1 raw41922step1Labels := by
      have ha : raw41922step1 = (fun i j => raw41922step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41922step1 raw41922step0; decide +kernel
      have hl : raw41922step1Labels = raw41922step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41922step0 raw41922step0Labels permutation35 permutation2
    mixedMoment B raw41922step1 raw41922step1Labels = mixedMoment B raw41922step2 raw41922step2Labels := by
      have ha : raw41922step2 = raw41922step1 := by apply Matrix.ext; unfold raw41922step2 raw41922step1; decide +kernel
      have hl : raw41922step1Labels = labelEmbedding1 ∘ raw41922step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41922step1 raw41922step1Labels raw41922step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

theorem canonical41923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41923 raw41923Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw41923 raw41923Labels = mixedMoment B raw41923step0 raw41923step0Labels := by
      have hz : ∀ j, raw41923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41923step0 = (fun i j => raw41923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41923step0 raw41923; decide +kernel
      have hl : raw41923step0Labels = raw41923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41923 raw41923Labels permutation346 hz
    mixedMoment B raw41923step0 raw41923step0Labels = mixedMoment B raw41923step1 raw41923step1Labels := by
      have ha : raw41923step1 = (fun i j => raw41923step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41923step1 raw41923step0; decide +kernel
      have hl : raw41923step1Labels = raw41923step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41923step0 raw41923step0Labels permutation48 permutation7
    mixedMoment B raw41923step1 raw41923step1Labels = mixedMoment B raw41923step2 raw41923step2Labels := by
      have ha : raw41923step2 = -raw41923step1 := by apply Matrix.ext; change ∀ i j, raw41923step2 i j = -(raw41923step1 i j); unfold raw41923step2 raw41923step1; decide +kernel
      have hl : raw41923step2Labels = raw41923step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41923step2 raw41923step2Labels = mixedMoment B raw41923step3 raw41923step3Labels := by
      have ha : raw41923step3 = raw41923step2 := by apply Matrix.ext; unfold raw41923step3 raw41923step2; decide +kernel
      have hl : raw41923step2Labels = labelEmbedding6 ∘ raw41923step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41923step2 raw41923step2Labels raw41923step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4440 node4440Labels := by rfl

theorem canonical41924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41924 raw41924Labels = mixedMoment B node1721 node1721Labels := by
  calc
    mixedMoment B raw41924 raw41924Labels = mixedMoment B raw41924step0 raw41924step0Labels := by
      have hz : ∀ j, raw41924 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41924step0 = (fun i j => raw41924 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41924step0 raw41924; decide +kernel
      have hl : raw41924step0Labels = raw41924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41924 raw41924Labels permutation346 hz
    mixedMoment B raw41924step0 raw41924step0Labels = mixedMoment B raw41924step1 raw41924step1Labels := by
      have ha : raw41924step1 = (fun i j => raw41924step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41924step1 raw41924step0; decide +kernel
      have hl : raw41924step1Labels = raw41924step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41924step0 raw41924step0Labels permutation36 permutation2
    mixedMoment B raw41924step1 raw41924step1Labels = mixedMoment B raw41924step2 raw41924step2Labels := by
      have ha : raw41924step2 = raw41924step1 := by apply Matrix.ext; unfold raw41924step2 raw41924step1; decide +kernel
      have hl : raw41924step1Labels = labelEmbedding1 ∘ raw41924step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41924step1 raw41924step1Labels raw41924step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1721 node1721Labels := by rfl

theorem canonical41925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41925 raw41925Labels = mixedMoment B node4369 node4369Labels := by
  calc
    mixedMoment B raw41925 raw41925Labels = mixedMoment B raw41925step0 raw41925step0Labels := by
      have hz : ∀ j, raw41925 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41925step0 = (fun i j => raw41925 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41925step0 raw41925; decide +kernel
      have hl : raw41925step0Labels = raw41925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41925 raw41925Labels permutation346 hz
    mixedMoment B raw41925step0 raw41925step0Labels = mixedMoment B raw41925step1 raw41925step1Labels := by
      have ha : raw41925step1 = (fun i j => raw41925step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41925step1 raw41925step0; decide +kernel
      have hl : raw41925step1Labels = raw41925step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41925step0 raw41925step0Labels permutation50 permutation7
    mixedMoment B raw41925step1 raw41925step1Labels = mixedMoment B raw41925step2 raw41925step2Labels := by
      have ha : raw41925step2 = -raw41925step1 := by apply Matrix.ext; change ∀ i j, raw41925step2 i j = -(raw41925step1 i j); unfold raw41925step2 raw41925step1; decide +kernel
      have hl : raw41925step2Labels = raw41925step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41925step2 raw41925step2Labels = mixedMoment B raw41925step3 raw41925step3Labels := by
      have ha : raw41925step3 = raw41925step2 := by apply Matrix.ext; unfold raw41925step3 raw41925step2; decide +kernel
      have hl : raw41925step2Labels = labelEmbedding6 ∘ raw41925step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41925step2 raw41925step2Labels raw41925step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4369 node4369Labels := by rfl

theorem canonical41926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41926 raw41926Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw41926 raw41926Labels = mixedMoment B raw41926step0 raw41926step0Labels := by
      have ha : raw41926step0 = (fun i j => raw41926 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41926step0 raw41926; decide +kernel
      have hl : raw41926step0Labels = raw41926Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41926 raw41926Labels permutation181 permutation2
    mixedMoment B raw41926step0 raw41926step0Labels = mixedMoment B raw41926step1 raw41926step1Labels := by
      have ha : raw41926step1 = raw41926step0 := by apply Matrix.ext; unfold raw41926step1 raw41926step0; decide +kernel
      have hl : raw41926step0Labels = labelEmbedding1 ∘ raw41926step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41926step0 raw41926step0Labels raw41926step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

theorem canonical41927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41927 raw41927Labels = mixedMoment B node4327 node4327Labels := by
  calc
    mixedMoment B raw41927 raw41927Labels = mixedMoment B raw41927step0 raw41927step0Labels := by
      have ha : raw41927step0 = (fun i j => raw41927 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41927step0 raw41927; decide +kernel
      have hl : raw41927step0Labels = raw41927Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41927 raw41927Labels permutation195 permutation7
    mixedMoment B raw41927step0 raw41927step0Labels = mixedMoment B raw41927step1 raw41927step1Labels := by
      have ha : raw41927step1 = -raw41927step0 := by apply Matrix.ext; change ∀ i j, raw41927step1 i j = -(raw41927step0 i j); unfold raw41927step1 raw41927step0; decide +kernel
      have hl : raw41927step1Labels = raw41927step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41927step1 raw41927step1Labels = mixedMoment B raw41927step2 raw41927step2Labels := by
      have ha : raw41927step2 = raw41927step1 := by apply Matrix.ext; unfold raw41927step2 raw41927step1; decide +kernel
      have hl : raw41927step1Labels = labelEmbedding6 ∘ raw41927step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41927step1 raw41927step1Labels raw41927step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4327 node4327Labels := by rfl

theorem canonical41928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41928 raw41928Labels = mixedMoment B node1757 node1757Labels := by
  calc
    mixedMoment B raw41928 raw41928Labels = mixedMoment B raw41928step0 raw41928step0Labels := by
      have hz : ∀ j, raw41928 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41928step0 = (fun i j => raw41928 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41928step0 raw41928; decide +kernel
      have hl : raw41928step0Labels = raw41928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41928 raw41928Labels permutation434 hz
    mixedMoment B raw41928step0 raw41928step0Labels = mixedMoment B raw41928step1 raw41928step1Labels := by
      have hz : ∀ j, raw41928step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41928step1 = (fun i j => raw41928step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41928step1 raw41928step0; decide +kernel
      have hl : raw41928step1Labels = raw41928step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41928step0 raw41928step0Labels permutation80 hz
    mixedMoment B raw41928step1 raw41928step1Labels = mixedMoment B raw41928step2 raw41928step2Labels := by
      have hz : ∀ j, raw41928step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41928step2 = (fun i j => raw41928step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41928step2 raw41928step1; decide +kernel
      have hl : raw41928step2Labels = raw41928step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41928step1 raw41928step1Labels permutation14 hz
    mixedMoment B raw41928step2 raw41928step2Labels = mixedMoment B raw41928step3 raw41928step3Labels := by
      have ha : raw41928step3 = raw41928step2 := by apply Matrix.ext; unfold raw41928step3 raw41928step2; decide +kernel
      have hl : raw41928step2Labels = labelEmbedding1 ∘ raw41928step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41928step2 raw41928step2Labels raw41928step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1757 node1757Labels := by rfl

theorem canonical41929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41929 raw41929Labels = mixedMoment B node4481 node4481Labels := by
  calc
    mixedMoment B raw41929 raw41929Labels = mixedMoment B raw41929step0 raw41929step0Labels := by
      have hz : ∀ j, raw41929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41929step0 = (fun i j => raw41929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41929step0 raw41929; decide +kernel
      have hl : raw41929step0Labels = raw41929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41929 raw41929Labels permutation434 hz
    mixedMoment B raw41929step0 raw41929step0Labels = mixedMoment B raw41929step1 raw41929step1Labels := by
      have hz : ∀ j, raw41929step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41929step1 = (fun i j => raw41929step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41929step1 raw41929step0; decide +kernel
      have hl : raw41929step1Labels = raw41929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41929step0 raw41929step0Labels permutation80 hz
    mixedMoment B raw41929step1 raw41929step1Labels = mixedMoment B raw41929step2 raw41929step2Labels := by
      have hz : ∀ j, raw41929step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41929step2 = (fun i j => raw41929step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41929step2 raw41929step1; decide +kernel
      have hl : raw41929step2Labels = raw41929step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41929step1 raw41929step1Labels permutation14 hz
    mixedMoment B raw41929step2 raw41929step2Labels = mixedMoment B raw41929step3 raw41929step3Labels := by
      have ha : raw41929step3 = (fun i j => raw41929step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41929step3 raw41929step2; decide +kernel
      have hl : raw41929step3Labels = raw41929step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41929step2 raw41929step2Labels permutation5 permutation6
    _ = mixedMoment B node4481 node4481Labels := by rfl

theorem canonical41930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41930 raw41930Labels = mixedMoment B node1540 node1540Labels := by
  calc
    mixedMoment B raw41930 raw41930Labels = mixedMoment B raw41930step0 raw41930step0Labels := by
      have hz : ∀ j, raw41930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41930step0 = (fun i j => raw41930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41930step0 raw41930; decide +kernel
      have hl : raw41930step0Labels = raw41930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41930 raw41930Labels permutation434 hz
    mixedMoment B raw41930step0 raw41930step0Labels = mixedMoment B raw41930step1 raw41930step1Labels := by
      have hz : ∀ j, raw41930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41930step1 = (fun i j => raw41930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41930step1 raw41930step0; decide +kernel
      have hl : raw41930step1Labels = raw41930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41930step0 raw41930step0Labels permutation80 hz
    mixedMoment B raw41930step1 raw41930step1Labels = mixedMoment B raw41930step2 raw41930step2Labels := by
      have hz : ∀ j, raw41930step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41930step2 = (fun i j => raw41930step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41930step2 raw41930step1; decide +kernel
      have hl : raw41930step2Labels = raw41930step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41930step1 raw41930step1Labels permutation14 hz
    mixedMoment B raw41930step2 raw41930step2Labels = mixedMoment B raw41930step3 raw41930step3Labels := by
      have ha : raw41930step3 = (fun i j => raw41930step2 (permutation6 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41930step3 raw41930step2; decide +kernel
      have hl : raw41930step3Labels = raw41930step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41930step2 raw41930step2Labels permutation6 permutation4
    mixedMoment B raw41930step3 raw41930step3Labels = mixedMoment B raw41930step4 raw41930step4Labels := by
      have ha : raw41930step4 = -raw41930step3 := by apply Matrix.ext; change ∀ i j, raw41930step4 i j = -(raw41930step3 i j); unfold raw41930step4 raw41930step3; decide +kernel
      have hl : raw41930step4Labels = raw41930step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41930step4 raw41930step4Labels = mixedMoment B raw41930step5 raw41930step5Labels := by
      have ha : raw41930step5 = raw41930step4 := by apply Matrix.ext; unfold raw41930step5 raw41930step4; decide +kernel
      have hl : raw41930step4Labels = labelEmbedding1 ∘ raw41930step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41930step4 raw41930step4Labels raw41930step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1540 node1540Labels := by rfl

theorem canonical41931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41931 raw41931Labels = mixedMoment B node4189 node4189Labels := by
  calc
    mixedMoment B raw41931 raw41931Labels = mixedMoment B raw41931step0 raw41931step0Labels := by
      have hz : ∀ j, raw41931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41931step0 = (fun i j => raw41931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41931step0 raw41931; decide +kernel
      have hl : raw41931step0Labels = raw41931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41931 raw41931Labels permutation434 hz
    mixedMoment B raw41931step0 raw41931step0Labels = mixedMoment B raw41931step1 raw41931step1Labels := by
      have hz : ∀ j, raw41931step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41931step1 = (fun i j => raw41931step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41931step1 raw41931step0; decide +kernel
      have hl : raw41931step1Labels = raw41931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41931step0 raw41931step0Labels permutation80 hz
    mixedMoment B raw41931step1 raw41931step1Labels = mixedMoment B raw41931step2 raw41931step2Labels := by
      have hz : ∀ j, raw41931step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41931step2 = (fun i j => raw41931step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41931step2 raw41931step1; decide +kernel
      have hl : raw41931step2Labels = raw41931step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41931step1 raw41931step1Labels permutation14 hz
    mixedMoment B raw41931step2 raw41931step2Labels = mixedMoment B raw41931step3 raw41931step3Labels := by
      have ha : raw41931step3 = (fun i j => raw41931step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41931step3 raw41931step2; decide +kernel
      have hl : raw41931step3Labels = raw41931step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41931step2 raw41931step2Labels permutation7 permutation6
    _ = mixedMoment B node4189 node4189Labels := by rfl

theorem canonical41932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41932 raw41932Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw41932 raw41932Labels = mixedMoment B raw41932step0 raw41932step0Labels := by
      have hz : ∀ j, raw41932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41932step0 = (fun i j => raw41932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41932step0 raw41932; decide +kernel
      have hl : raw41932step0Labels = raw41932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41932 raw41932Labels permutation346 hz
    mixedMoment B raw41932step0 raw41932step0Labels = mixedMoment B raw41932step1 raw41932step1Labels := by
      have hz : ∀ j, raw41932step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41932step1 = (fun i j => raw41932step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41932step1 raw41932step0; decide +kernel
      have hl : raw41932step1Labels = raw41932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41932step0 raw41932step0Labels permutation56 hz
    mixedMoment B raw41932step1 raw41932step1Labels = mixedMoment B raw41932step2 raw41932step2Labels := by
      have ha : raw41932step2 = (fun i j => raw41932step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41932step2 raw41932step1; decide +kernel
      have hl : raw41932step2Labels = raw41932step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41932step1 raw41932step1Labels permutation31 permutation4
    mixedMoment B raw41932step2 raw41932step2Labels = mixedMoment B raw41932step3 raw41932step3Labels := by
      have ha : raw41932step3 = -raw41932step2 := by apply Matrix.ext; change ∀ i j, raw41932step3 i j = -(raw41932step2 i j); unfold raw41932step3 raw41932step2; decide +kernel
      have hl : raw41932step3Labels = raw41932step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41932step3 raw41932step3Labels = mixedMoment B raw41932step4 raw41932step4Labels := by
      have ha : raw41932step4 = raw41932step3 := by apply Matrix.ext; unfold raw41932step4 raw41932step3; decide +kernel
      have hl : raw41932step3Labels = labelEmbedding1 ∘ raw41932step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41932step3 raw41932step3Labels raw41932step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1532 node1532Labels := by rfl

theorem canonical41933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41933 raw41933Labels = mixedMoment B node4159 node4159Labels := by
  calc
    mixedMoment B raw41933 raw41933Labels = mixedMoment B raw41933step0 raw41933step0Labels := by
      have hz : ∀ j, raw41933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41933step0 = (fun i j => raw41933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41933step0 raw41933; decide +kernel
      have hl : raw41933step0Labels = raw41933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41933 raw41933Labels permutation346 hz
    mixedMoment B raw41933step0 raw41933step0Labels = mixedMoment B raw41933step1 raw41933step1Labels := by
      have hz : ∀ j, raw41933step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41933step1 = (fun i j => raw41933step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41933step1 raw41933step0; decide +kernel
      have hl : raw41933step1Labels = raw41933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41933step0 raw41933step0Labels permutation56 hz
    mixedMoment B raw41933step1 raw41933step1Labels = mixedMoment B raw41933step2 raw41933step2Labels := by
      have ha : raw41933step2 = (fun i j => raw41933step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41933step2 raw41933step1; decide +kernel
      have hl : raw41933step2Labels = raw41933step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41933step1 raw41933step1Labels permutation31 permutation6
    _ = mixedMoment B node4159 node4159Labels := by rfl

theorem canonical41934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41934 raw41934Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw41934 raw41934Labels = mixedMoment B raw41934step0 raw41934step0Labels := by
      have hz : ∀ j, raw41934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41934step0 = (fun i j => raw41934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41934step0 raw41934; decide +kernel
      have hl : raw41934step0Labels = raw41934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41934 raw41934Labels permutation346 hz
    mixedMoment B raw41934step0 raw41934step0Labels = mixedMoment B raw41934step1 raw41934step1Labels := by
      have hz : ∀ j, raw41934step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41934step1 = (fun i j => raw41934step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41934step1 raw41934step0; decide +kernel
      have hl : raw41934step1Labels = raw41934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41934step0 raw41934step0Labels permutation56 hz
    mixedMoment B raw41934step1 raw41934step1Labels = mixedMoment B raw41934step2 raw41934step2Labels := by
      have ha : raw41934step2 = (fun i j => raw41934step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41934step2 raw41934step1; decide +kernel
      have hl : raw41934step2Labels = raw41934step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41934step1 raw41934step1Labels permutation16 permutation4
    mixedMoment B raw41934step2 raw41934step2Labels = mixedMoment B raw41934step3 raw41934step3Labels := by
      have ha : raw41934step3 = -raw41934step2 := by apply Matrix.ext; change ∀ i j, raw41934step3 i j = -(raw41934step2 i j); unfold raw41934step3 raw41934step2; decide +kernel
      have hl : raw41934step3Labels = raw41934step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41934step3 raw41934step3Labels = mixedMoment B raw41934step4 raw41934step4Labels := by
      have ha : raw41934step4 = raw41934step3 := by apply Matrix.ext; unfold raw41934step4 raw41934step3; decide +kernel
      have hl : raw41934step3Labels = labelEmbedding1 ∘ raw41934step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41934step3 raw41934step3Labels raw41934step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1695 node1695Labels := by rfl

theorem canonical41935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41935 raw41935Labels = mixedMoment B node4358 node4358Labels := by
  calc
    mixedMoment B raw41935 raw41935Labels = mixedMoment B raw41935step0 raw41935step0Labels := by
      have hz : ∀ j, raw41935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41935step0 = (fun i j => raw41935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41935step0 raw41935; decide +kernel
      have hl : raw41935step0Labels = raw41935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41935 raw41935Labels permutation346 hz
    mixedMoment B raw41935step0 raw41935step0Labels = mixedMoment B raw41935step1 raw41935step1Labels := by
      have hz : ∀ j, raw41935step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41935step1 = (fun i j => raw41935step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41935step1 raw41935step0; decide +kernel
      have hl : raw41935step1Labels = raw41935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41935step0 raw41935step0Labels permutation56 hz
    mixedMoment B raw41935step1 raw41935step1Labels = mixedMoment B raw41935step2 raw41935step2Labels := by
      have ha : raw41935step2 = (fun i j => raw41935step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41935step2 raw41935step1; decide +kernel
      have hl : raw41935step2Labels = raw41935step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41935step1 raw41935step1Labels permutation17 permutation6
    _ = mixedMoment B node4358 node4358Labels := by rfl

theorem canonical41936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41936 raw41936Labels = mixedMoment B node1749 node1749Labels := by
  calc
    mixedMoment B raw41936 raw41936Labels = mixedMoment B raw41936step0 raw41936step0Labels := by
      have hz : ∀ j, raw41936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41936step0 = (fun i j => raw41936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41936step0 raw41936; decide +kernel
      have hl : raw41936step0Labels = raw41936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41936 raw41936Labels permutation346 hz
    mixedMoment B raw41936step0 raw41936step0Labels = mixedMoment B raw41936step1 raw41936step1Labels := by
      have hz : ∀ j, raw41936step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41936step1 = (fun i j => raw41936step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41936step1 raw41936step0; decide +kernel
      have hl : raw41936step1Labels = raw41936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41936step0 raw41936step0Labels permutation56 hz
    mixedMoment B raw41936step1 raw41936step1Labels = mixedMoment B raw41936step2 raw41936step2Labels := by
      have ha : raw41936step2 = (fun i j => raw41936step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41936step2 raw41936step1; decide +kernel
      have hl : raw41936step2Labels = raw41936step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41936step1 raw41936step1Labels permutation11 permutation2
    mixedMoment B raw41936step2 raw41936step2Labels = mixedMoment B raw41936step3 raw41936step3Labels := by
      have ha : raw41936step3 = raw41936step2 := by apply Matrix.ext; unfold raw41936step3 raw41936step2; decide +kernel
      have hl : raw41936step2Labels = labelEmbedding1 ∘ raw41936step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41936step2 raw41936step2Labels raw41936step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1749 node1749Labels := by rfl

theorem canonical41937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41937 raw41937Labels = mixedMoment B node4445 node4445Labels := by
  calc
    mixedMoment B raw41937 raw41937Labels = mixedMoment B raw41937step0 raw41937step0Labels := by
      have hz : ∀ j, raw41937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41937step0 = (fun i j => raw41937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41937step0 raw41937; decide +kernel
      have hl : raw41937step0Labels = raw41937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41937 raw41937Labels permutation346 hz
    mixedMoment B raw41937step0 raw41937step0Labels = mixedMoment B raw41937step1 raw41937step1Labels := by
      have hz : ∀ j, raw41937step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41937step1 = (fun i j => raw41937step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41937step1 raw41937step0; decide +kernel
      have hl : raw41937step1Labels = raw41937step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41937step0 raw41937step0Labels permutation56 hz
    mixedMoment B raw41937step1 raw41937step1Labels = mixedMoment B raw41937step2 raw41937step2Labels := by
      have ha : raw41937step2 = (fun i j => raw41937step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41937step2 raw41937step1; decide +kernel
      have hl : raw41937step2Labels = raw41937step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41937step1 raw41937step1Labels permutation17 permutation6
    _ = mixedMoment B node4445 node4445Labels := by rfl

theorem canonical41938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41938 raw41938Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw41938 raw41938Labels = mixedMoment B raw41938step0 raw41938step0Labels := by
      have hz : ∀ j, raw41938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41938step0 = (fun i j => raw41938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41938step0 raw41938; decide +kernel
      have hl : raw41938step0Labels = raw41938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41938 raw41938Labels permutation346 hz
    mixedMoment B raw41938step0 raw41938step0Labels = mixedMoment B raw41938step1 raw41938step1Labels := by
      have hz : ∀ j, raw41938step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41938step1 = (fun i j => raw41938step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41938step1 raw41938step0; decide +kernel
      have hl : raw41938step1Labels = raw41938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41938step0 raw41938step0Labels permutation56 hz
    mixedMoment B raw41938step1 raw41938step1Labels = mixedMoment B raw41938step2 raw41938step2Labels := by
      have ha : raw41938step2 = (fun i j => raw41938step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41938step2 raw41938step1; decide +kernel
      have hl : raw41938step2Labels = raw41938step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41938step1 raw41938step1Labels permutation13 permutation2
    mixedMoment B raw41938step2 raw41938step2Labels = mixedMoment B raw41938step3 raw41938step3Labels := by
      have ha : raw41938step3 = raw41938step2 := by apply Matrix.ext; unfold raw41938step3 raw41938step2; decide +kernel
      have hl : raw41938step2Labels = labelEmbedding1 ∘ raw41938step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41938step2 raw41938step2Labels raw41938step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1748 node1748Labels := by rfl

theorem canonical41939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41939 raw41939Labels = mixedMoment B node4374 node4374Labels := by
  calc
    mixedMoment B raw41939 raw41939Labels = mixedMoment B raw41939step0 raw41939step0Labels := by
      have hz : ∀ j, raw41939 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41939step0 = (fun i j => raw41939 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41939step0 raw41939; decide +kernel
      have hl : raw41939step0Labels = raw41939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41939 raw41939Labels permutation346 hz
    mixedMoment B raw41939step0 raw41939step0Labels = mixedMoment B raw41939step1 raw41939step1Labels := by
      have hz : ∀ j, raw41939step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41939step1 = (fun i j => raw41939step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41939step1 raw41939step0; decide +kernel
      have hl : raw41939step1Labels = raw41939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41939step0 raw41939step0Labels permutation56 hz
    mixedMoment B raw41939step1 raw41939step1Labels = mixedMoment B raw41939step2 raw41939step2Labels := by
      have ha : raw41939step2 = (fun i j => raw41939step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41939step2 raw41939step1; decide +kernel
      have hl : raw41939step2Labels = raw41939step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41939step1 raw41939step1Labels permutation13 permutation7
    mixedMoment B raw41939step2 raw41939step2Labels = mixedMoment B raw41939step3 raw41939step3Labels := by
      have ha : raw41939step3 = -raw41939step2 := by apply Matrix.ext; change ∀ i j, raw41939step3 i j = -(raw41939step2 i j); unfold raw41939step3 raw41939step2; decide +kernel
      have hl : raw41939step3Labels = raw41939step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41939step3 raw41939step3Labels = mixedMoment B raw41939step4 raw41939step4Labels := by
      have ha : raw41939step4 = raw41939step3 := by apply Matrix.ext; unfold raw41939step4 raw41939step3; decide +kernel
      have hl : raw41939step3Labels = labelEmbedding6 ∘ raw41939step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41939step3 raw41939step3Labels raw41939step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4374 node4374Labels := by rfl

theorem canonical41940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41940 raw41940Labels = mixedMoment B node1688 node1688Labels := by
  calc
    mixedMoment B raw41940 raw41940Labels = mixedMoment B raw41940step0 raw41940step0Labels := by
      have hz : ∀ j, raw41940 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41940step0 = (fun i j => raw41940 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41940step0 raw41940; decide +kernel
      have hl : raw41940step0Labels = raw41940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41940 raw41940Labels permutation265 hz
    mixedMoment B raw41940step0 raw41940step0Labels = mixedMoment B raw41940step1 raw41940step1Labels := by
      have ha : raw41940step1 = (fun i j => raw41940step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41940step1 raw41940step0; decide +kernel
      have hl : raw41940step1Labels = raw41940step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41940step0 raw41940step0Labels permutation37 permutation2
    mixedMoment B raw41940step1 raw41940step1Labels = mixedMoment B raw41940step2 raw41940step2Labels := by
      have ha : raw41940step2 = raw41940step1 := by apply Matrix.ext; unfold raw41940step2 raw41940step1; decide +kernel
      have hl : raw41940step1Labels = labelEmbedding1 ∘ raw41940step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41940step1 raw41940step1Labels raw41940step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1688 node1688Labels := by rfl

theorem canonical41941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41941 raw41941Labels = mixedMoment B node4333 node4333Labels := by
  calc
    mixedMoment B raw41941 raw41941Labels = mixedMoment B raw41941step0 raw41941step0Labels := by
      have hz : ∀ j, raw41941 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41941step0 = (fun i j => raw41941 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41941step0 raw41941; decide +kernel
      have hl : raw41941step0Labels = raw41941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41941 raw41941Labels permutation265 hz
    mixedMoment B raw41941step0 raw41941step0Labels = mixedMoment B raw41941step1 raw41941step1Labels := by
      have ha : raw41941step1 = (fun i j => raw41941step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41941step1 raw41941step0; decide +kernel
      have hl : raw41941step1Labels = raw41941step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41941step0 raw41941step0Labels permutation97 permutation6
    _ = mixedMoment B node4333 node4333Labels := by rfl

theorem canonical41942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41942 raw41942Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw41942 raw41942Labels = mixedMoment B raw41942step0 raw41942step0Labels := by
      have hz : ∀ j, raw41942 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41942step0 = (fun i j => raw41942 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41942step0 raw41942; decide +kernel
      have hl : raw41942step0Labels = raw41942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41942 raw41942Labels permutation265 hz
    mixedMoment B raw41942step0 raw41942step0Labels = mixedMoment B raw41942step1 raw41942step1Labels := by
      have ha : raw41942step1 = (fun i j => raw41942step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41942step1 raw41942step0; decide +kernel
      have hl : raw41942step1Labels = raw41942step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41942step0 raw41942step0Labels permutation37 permutation2
    mixedMoment B raw41942step1 raw41942step1Labels = mixedMoment B raw41942step2 raw41942step2Labels := by
      have ha : raw41942step2 = raw41942step1 := by apply Matrix.ext; unfold raw41942step2 raw41942step1; decide +kernel
      have hl : raw41942step1Labels = labelEmbedding1 ∘ raw41942step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41942step1 raw41942step1Labels raw41942step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

theorem canonical41943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41943 raw41943Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw41943 raw41943Labels = mixedMoment B raw41943step0 raw41943step0Labels := by
      have hz : ∀ j, raw41943 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41943step0 = (fun i j => raw41943 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41943step0 raw41943; decide +kernel
      have hl : raw41943step0Labels = raw41943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41943 raw41943Labels permutation265 hz
    mixedMoment B raw41943step0 raw41943step0Labels = mixedMoment B raw41943step1 raw41943step1Labels := by
      have ha : raw41943step1 = (fun i j => raw41943step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41943step1 raw41943step0; decide +kernel
      have hl : raw41943step1Labels = raw41943step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41943step0 raw41943step0Labels permutation37 permutation7
    mixedMoment B raw41943step1 raw41943step1Labels = mixedMoment B raw41943step2 raw41943step2Labels := by
      have ha : raw41943step2 = -raw41943step1 := by apply Matrix.ext; change ∀ i j, raw41943step2 i j = -(raw41943step1 i j); unfold raw41943step2 raw41943step1; decide +kernel
      have hl : raw41943step2Labels = raw41943step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41943step2 raw41943step2Labels = mixedMoment B raw41943step3 raw41943step3Labels := by
      have ha : raw41943step3 = raw41943step2 := by apply Matrix.ext; unfold raw41943step3 raw41943step2; decide +kernel
      have hl : raw41943step2Labels = labelEmbedding6 ∘ raw41943step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41943step2 raw41943step2Labels raw41943step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4335 node4335Labels := by rfl

theorem canonical41944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41944 raw41944Labels = mixedMoment B node1529 node1529Labels := by
  calc
    mixedMoment B raw41944 raw41944Labels = mixedMoment B raw41944step0 raw41944step0Labels := by
      have hz : ∀ j, raw41944 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41944step0 = (fun i j => raw41944 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41944step0 raw41944; decide +kernel
      have hl : raw41944step0Labels = raw41944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41944 raw41944Labels permutation434 hz
    mixedMoment B raw41944step0 raw41944step0Labels = mixedMoment B raw41944step1 raw41944step1Labels := by
      have hz : ∀ j, raw41944step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41944step1 = (fun i j => raw41944step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41944step1 raw41944step0; decide +kernel
      have hl : raw41944step1Labels = raw41944step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41944step0 raw41944step0Labels permutation80 hz
    mixedMoment B raw41944step1 raw41944step1Labels = mixedMoment B raw41944step2 raw41944step2Labels := by
      have ha : raw41944step2 = raw41944step1 := by apply Matrix.ext; unfold raw41944step2 raw41944step1; decide +kernel
      have hl : raw41944step1Labels = labelEmbedding1 ∘ raw41944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41944step1 raw41944step1Labels raw41944step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1529 node1529Labels := by rfl

theorem canonical41945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41945 raw41945Labels = mixedMoment B node4162 node4162Labels := by
  calc
    mixedMoment B raw41945 raw41945Labels = mixedMoment B raw41945step0 raw41945step0Labels := by
      have hz : ∀ j, raw41945 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41945step0 = (fun i j => raw41945 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41945step0 raw41945; decide +kernel
      have hl : raw41945step0Labels = raw41945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41945 raw41945Labels permutation434 hz
    mixedMoment B raw41945step0 raw41945step0Labels = mixedMoment B raw41945step1 raw41945step1Labels := by
      have hz : ∀ j, raw41945step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41945step1 = (fun i j => raw41945step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41945step1 raw41945step0; decide +kernel
      have hl : raw41945step1Labels = raw41945step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41945step0 raw41945step0Labels permutation80 hz
    mixedMoment B raw41945step1 raw41945step1Labels = mixedMoment B raw41945step2 raw41945step2Labels := by
      have ha : raw41945step2 = (fun i j => raw41945step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41945step2 raw41945step1; decide +kernel
      have hl : raw41945step2Labels = raw41945step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41945step1 raw41945step1Labels permutation11 permutation7
    mixedMoment B raw41945step2 raw41945step2Labels = mixedMoment B raw41945step3 raw41945step3Labels := by
      have ha : raw41945step3 = -raw41945step2 := by apply Matrix.ext; change ∀ i j, raw41945step3 i j = -(raw41945step2 i j); unfold raw41945step3 raw41945step2; decide +kernel
      have hl : raw41945step3Labels = raw41945step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41945step3 raw41945step3Labels = mixedMoment B raw41945step4 raw41945step4Labels := by
      have ha : raw41945step4 = raw41945step3 := by apply Matrix.ext; unfold raw41945step4 raw41945step3; decide +kernel
      have hl : raw41945step3Labels = labelEmbedding6 ∘ raw41945step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41945step3 raw41945step3Labels raw41945step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4162 node4162Labels := by rfl

theorem canonical41946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41946 raw41946Labels = mixedMoment B node1528 node1528Labels := by
  calc
    mixedMoment B raw41946 raw41946Labels = mixedMoment B raw41946step0 raw41946step0Labels := by
      have hz : ∀ j, raw41946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41946step0 = (fun i j => raw41946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41946step0 raw41946; decide +kernel
      have hl : raw41946step0Labels = raw41946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41946 raw41946Labels permutation346 hz
    mixedMoment B raw41946step0 raw41946step0Labels = mixedMoment B raw41946step1 raw41946step1Labels := by
      have ha : raw41946step1 = (fun i j => raw41946step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41946step1 raw41946step0; decide +kernel
      have hl : raw41946step1Labels = raw41946step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41946step0 raw41946step0Labels permutation36 permutation2
    mixedMoment B raw41946step1 raw41946step1Labels = mixedMoment B raw41946step2 raw41946step2Labels := by
      have ha : raw41946step2 = raw41946step1 := by apply Matrix.ext; unfold raw41946step2 raw41946step1; decide +kernel
      have hl : raw41946step1Labels = labelEmbedding1 ∘ raw41946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41946step1 raw41946step1Labels raw41946step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1528 node1528Labels := by rfl

theorem canonical41947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41947 raw41947Labels = mixedMoment B node4157 node4157Labels := by
  calc
    mixedMoment B raw41947 raw41947Labels = mixedMoment B raw41947step0 raw41947step0Labels := by
      have hz : ∀ j, raw41947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41947step0 = (fun i j => raw41947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41947step0 raw41947; decide +kernel
      have hl : raw41947step0Labels = raw41947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41947 raw41947Labels permutation346 hz
    mixedMoment B raw41947step0 raw41947step0Labels = mixedMoment B raw41947step1 raw41947step1Labels := by
      have ha : raw41947step1 = (fun i j => raw41947step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41947step1 raw41947step0; decide +kernel
      have hl : raw41947step1Labels = raw41947step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41947step0 raw41947step0Labels permutation53 permutation7
    mixedMoment B raw41947step1 raw41947step1Labels = mixedMoment B raw41947step2 raw41947step2Labels := by
      have ha : raw41947step2 = -raw41947step1 := by apply Matrix.ext; change ∀ i j, raw41947step2 i j = -(raw41947step1 i j); unfold raw41947step2 raw41947step1; decide +kernel
      have hl : raw41947step2Labels = raw41947step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41947step2 raw41947step2Labels = mixedMoment B raw41947step3 raw41947step3Labels := by
      have ha : raw41947step3 = raw41947step2 := by apply Matrix.ext; unfold raw41947step3 raw41947step2; decide +kernel
      have hl : raw41947step2Labels = labelEmbedding6 ∘ raw41947step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41947step2 raw41947step2Labels raw41947step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4157 node4157Labels := by rfl

theorem canonical41948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41948 raw41948Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw41948 raw41948Labels = mixedMoment B raw41948step0 raw41948step0Labels := by
      have hz : ∀ j, raw41948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41948step0 = (fun i j => raw41948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41948step0 raw41948; decide +kernel
      have hl : raw41948step0Labels = raw41948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41948 raw41948Labels permutation434 hz
    mixedMoment B raw41948step0 raw41948step0Labels = mixedMoment B raw41948step1 raw41948step1Labels := by
      have ha : raw41948step1 = (fun i j => raw41948step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41948step1 raw41948step0; decide +kernel
      have hl : raw41948step1Labels = raw41948step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41948step0 raw41948step0Labels permutation38 permutation2
    mixedMoment B raw41948step1 raw41948step1Labels = mixedMoment B raw41948step2 raw41948step2Labels := by
      have ha : raw41948step2 = raw41948step1 := by apply Matrix.ext; unfold raw41948step2 raw41948step1; decide +kernel
      have hl : raw41948step1Labels = labelEmbedding1 ∘ raw41948step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41948step1 raw41948step1Labels raw41948step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1511 node1511Labels := by rfl

theorem canonical41949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41949 raw41949Labels = mixedMoment B node4154 node4154Labels := by
  calc
    mixedMoment B raw41949 raw41949Labels = mixedMoment B raw41949step0 raw41949step0Labels := by
      have hz : ∀ j, raw41949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41949step0 = (fun i j => raw41949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41949step0 raw41949; decide +kernel
      have hl : raw41949step0Labels = raw41949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41949 raw41949Labels permutation434 hz
    mixedMoment B raw41949step0 raw41949step0Labels = mixedMoment B raw41949step1 raw41949step1Labels := by
      have ha : raw41949step1 = (fun i j => raw41949step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41949step1 raw41949step0; decide +kernel
      have hl : raw41949step1Labels = raw41949step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41949step0 raw41949step0Labels permutation46 permutation7
    mixedMoment B raw41949step1 raw41949step1Labels = mixedMoment B raw41949step2 raw41949step2Labels := by
      have ha : raw41949step2 = -raw41949step1 := by apply Matrix.ext; change ∀ i j, raw41949step2 i j = -(raw41949step1 i j); unfold raw41949step2 raw41949step1; decide +kernel
      have hl : raw41949step2Labels = raw41949step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41949step2 raw41949step2Labels = mixedMoment B raw41949step3 raw41949step3Labels := by
      have ha : raw41949step3 = raw41949step2 := by apply Matrix.ext; unfold raw41949step3 raw41949step2; decide +kernel
      have hl : raw41949step2Labels = labelEmbedding6 ∘ raw41949step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41949step2 raw41949step2Labels raw41949step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4154 node4154Labels := by rfl

theorem canonical41950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41950 raw41950Labels = mixedMoment B node1510 node1510Labels := by
  calc
    mixedMoment B raw41950 raw41950Labels = mixedMoment B raw41950step0 raw41950step0Labels := by
      have ha : raw41950step0 = (fun i j => raw41950 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41950step0 raw41950; decide +kernel
      have hl : raw41950step0Labels = raw41950Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41950 raw41950Labels permutation180 permutation2
    mixedMoment B raw41950step0 raw41950step0Labels = mixedMoment B raw41950step1 raw41950step1Labels := by
      have ha : raw41950step1 = raw41950step0 := by apply Matrix.ext; unfold raw41950step1 raw41950step0; decide +kernel
      have hl : raw41950step0Labels = labelEmbedding1 ∘ raw41950step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41950step0 raw41950step0Labels raw41950step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1510 node1510Labels := by rfl

theorem canonical41951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41951 raw41951Labels = mixedMoment B node4152 node4152Labels := by
  calc
    mixedMoment B raw41951 raw41951Labels = mixedMoment B raw41951step0 raw41951step0Labels := by
      have ha : raw41951step0 = (fun i j => raw41951 (permutation255 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41951step0 raw41951; decide +kernel
      have hl : raw41951step0Labels = raw41951Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41951 raw41951Labels permutation255 permutation7
    mixedMoment B raw41951step0 raw41951step0Labels = mixedMoment B raw41951step1 raw41951step1Labels := by
      have ha : raw41951step1 = -raw41951step0 := by apply Matrix.ext; change ∀ i j, raw41951step1 i j = -(raw41951step0 i j); unfold raw41951step1 raw41951step0; decide +kernel
      have hl : raw41951step1Labels = raw41951step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41951step1 raw41951step1Labels = mixedMoment B raw41951step2 raw41951step2Labels := by
      have ha : raw41951step2 = raw41951step1 := by apply Matrix.ext; unfold raw41951step2 raw41951step1; decide +kernel
      have hl : raw41951step1Labels = labelEmbedding6 ∘ raw41951step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41951step1 raw41951step1Labels raw41951step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4152 node4152Labels := by rfl

theorem canonical41952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41952 raw41952Labels = mixedMoment B node1523 node1523Labels := by
  calc
    mixedMoment B raw41952 raw41952Labels = mixedMoment B raw41952step0 raw41952step0Labels := by
      have hz : ∀ j, raw41952 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41952step0 = (fun i j => raw41952 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41952step0 raw41952; decide +kernel
      have hl : raw41952step0Labels = raw41952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41952 raw41952Labels permutation434 hz
    mixedMoment B raw41952step0 raw41952step0Labels = mixedMoment B raw41952step1 raw41952step1Labels := by
      have hz : ∀ j, raw41952step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41952step1 = (fun i j => raw41952step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41952step1 raw41952step0; decide +kernel
      have hl : raw41952step1Labels = raw41952step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41952step0 raw41952step0Labels permutation80 hz
    mixedMoment B raw41952step1 raw41952step1Labels = mixedMoment B raw41952step2 raw41952step2Labels := by
      have ha : raw41952step2 = raw41952step1 := by apply Matrix.ext; unfold raw41952step2 raw41952step1; decide +kernel
      have hl : raw41952step1Labels = labelEmbedding1 ∘ raw41952step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41952step1 raw41952step1Labels raw41952step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1523 node1523Labels := by rfl

theorem canonical41953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41953 raw41953Labels = mixedMoment B node4160 node4160Labels := by
  calc
    mixedMoment B raw41953 raw41953Labels = mixedMoment B raw41953step0 raw41953step0Labels := by
      have hz : ∀ j, raw41953 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41953step0 = (fun i j => raw41953 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41953step0 raw41953; decide +kernel
      have hl : raw41953step0Labels = raw41953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41953 raw41953Labels permutation434 hz
    mixedMoment B raw41953step0 raw41953step0Labels = mixedMoment B raw41953step1 raw41953step1Labels := by
      have hz : ∀ j, raw41953step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41953step1 = (fun i j => raw41953step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41953step1 raw41953step0; decide +kernel
      have hl : raw41953step1Labels = raw41953step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41953step0 raw41953step0Labels permutation80 hz
    mixedMoment B raw41953step1 raw41953step1Labels = mixedMoment B raw41953step2 raw41953step2Labels := by
      have ha : raw41953step2 = (fun i j => raw41953step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41953step2 raw41953step1; decide +kernel
      have hl : raw41953step2Labels = raw41953step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41953step1 raw41953step1Labels permutation10 permutation7
    mixedMoment B raw41953step2 raw41953step2Labels = mixedMoment B raw41953step3 raw41953step3Labels := by
      have ha : raw41953step3 = -raw41953step2 := by apply Matrix.ext; change ∀ i j, raw41953step3 i j = -(raw41953step2 i j); unfold raw41953step3 raw41953step2; decide +kernel
      have hl : raw41953step3Labels = raw41953step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41953step3 raw41953step3Labels = mixedMoment B raw41953step4 raw41953step4Labels := by
      have ha : raw41953step4 = raw41953step3 := by apply Matrix.ext; unfold raw41953step4 raw41953step3; decide +kernel
      have hl : raw41953step3Labels = labelEmbedding6 ∘ raw41953step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41953step3 raw41953step3Labels raw41953step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4160 node4160Labels := by rfl

theorem canonical41954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41954 raw41954Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw41954 raw41954Labels = mixedMoment B raw41954step0 raw41954step0Labels := by
      have hz : ∀ j, raw41954 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41954step0 = (fun i j => raw41954 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41954step0 raw41954; decide +kernel
      have hl : raw41954step0Labels = raw41954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41954 raw41954Labels permutation346 hz
    mixedMoment B raw41954step0 raw41954step0Labels = mixedMoment B raw41954step1 raw41954step1Labels := by
      have ha : raw41954step1 = (fun i j => raw41954step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41954step1 raw41954step0; decide +kernel
      have hl : raw41954step1Labels = raw41954step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41954step0 raw41954step0Labels permutation37 permutation2
    mixedMoment B raw41954step1 raw41954step1Labels = mixedMoment B raw41954step2 raw41954step2Labels := by
      have ha : raw41954step2 = raw41954step1 := by apply Matrix.ext; unfold raw41954step2 raw41954step1; decide +kernel
      have hl : raw41954step1Labels = labelEmbedding1 ∘ raw41954step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41954step1 raw41954step1Labels raw41954step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1522 node1522Labels := by rfl

theorem canonical41955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41955 raw41955Labels = mixedMoment B node4158 node4158Labels := by
  calc
    mixedMoment B raw41955 raw41955Labels = mixedMoment B raw41955step0 raw41955step0Labels := by
      have hz : ∀ j, raw41955 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41955step0 = (fun i j => raw41955 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41955step0 raw41955; decide +kernel
      have hl : raw41955step0Labels = raw41955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41955 raw41955Labels permutation346 hz
    mixedMoment B raw41955step0 raw41955step0Labels = mixedMoment B raw41955step1 raw41955step1Labels := by
      have ha : raw41955step1 = (fun i j => raw41955step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41955step1 raw41955step0; decide +kernel
      have hl : raw41955step1Labels = raw41955step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41955step0 raw41955step0Labels permutation54 permutation7
    mixedMoment B raw41955step1 raw41955step1Labels = mixedMoment B raw41955step2 raw41955step2Labels := by
      have ha : raw41955step2 = -raw41955step1 := by apply Matrix.ext; change ∀ i j, raw41955step2 i j = -(raw41955step1 i j); unfold raw41955step2 raw41955step1; decide +kernel
      have hl : raw41955step2Labels = raw41955step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41955step2 raw41955step2Labels = mixedMoment B raw41955step3 raw41955step3Labels := by
      have ha : raw41955step3 = raw41955step2 := by apply Matrix.ext; unfold raw41955step3 raw41955step2; decide +kernel
      have hl : raw41955step2Labels = labelEmbedding6 ∘ raw41955step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41955step2 raw41955step2Labels raw41955step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4158 node4158Labels := by rfl

theorem canonical41956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41956 raw41956Labels = mixedMoment B node1501 node1501Labels := by
  calc
    mixedMoment B raw41956 raw41956Labels = mixedMoment B raw41956step0 raw41956step0Labels := by
      have ha : raw41956step0 = raw41956 := by apply Matrix.ext; unfold raw41956step0 raw41956; decide +kernel
      have hl : raw41956Labels = labelEmbedding1 ∘ raw41956step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41956 raw41956Labels raw41956step0Labels labelEmbedding1 hl
    _ = mixedMoment B node1501 node1501Labels := by rfl

theorem canonical41957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41957 raw41957Labels = mixedMoment B node4149 node4149Labels := by
  calc
    mixedMoment B raw41957 raw41957Labels = mixedMoment B raw41957step0 raw41957step0Labels := by
      have ha : raw41957step0 = (fun i j => raw41957 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41957step0 raw41957; decide +kernel
      have hl : raw41957step0Labels = raw41957Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41957 raw41957Labels permutation224 permutation7
    mixedMoment B raw41957step0 raw41957step0Labels = mixedMoment B raw41957step1 raw41957step1Labels := by
      have ha : raw41957step1 = -raw41957step0 := by apply Matrix.ext; change ∀ i j, raw41957step1 i j = -(raw41957step0 i j); unfold raw41957step1 raw41957step0; decide +kernel
      have hl : raw41957step1Labels = raw41957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41957step1 raw41957step1Labels = mixedMoment B raw41957step2 raw41957step2Labels := by
      have ha : raw41957step2 = raw41957step1 := by apply Matrix.ext; unfold raw41957step2 raw41957step1; decide +kernel
      have hl : raw41957step1Labels = labelEmbedding6 ∘ raw41957step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41957step1 raw41957step1Labels raw41957step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4149 node4149Labels := by rfl

theorem canonical41958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41958 raw41958Labels = mixedMoment B node1505 node1505Labels := by
  calc
    mixedMoment B raw41958 raw41958Labels = mixedMoment B raw41958step0 raw41958step0Labels := by
      have hz : ∀ j, raw41958 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41958step0 = (fun i j => raw41958 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41958step0 raw41958; decide +kernel
      have hl : raw41958step0Labels = raw41958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41958 raw41958Labels permutation434 hz
    mixedMoment B raw41958step0 raw41958step0Labels = mixedMoment B raw41958step1 raw41958step1Labels := by
      have ha : raw41958step1 = raw41958step0 := by apply Matrix.ext; unfold raw41958step1 raw41958step0; decide +kernel
      have hl : raw41958step0Labels = labelEmbedding1 ∘ raw41958step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41958step0 raw41958step0Labels raw41958step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1505 node1505Labels := by rfl

theorem canonical41959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41959 raw41959Labels = mixedMoment B node4151 node4151Labels := by
  calc
    mixedMoment B raw41959 raw41959Labels = mixedMoment B raw41959step0 raw41959step0Labels := by
      have hz : ∀ j, raw41959 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41959step0 = (fun i j => raw41959 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41959step0 raw41959; decide +kernel
      have hl : raw41959step0Labels = raw41959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41959 raw41959Labels permutation434 hz
    mixedMoment B raw41959step0 raw41959step0Labels = mixedMoment B raw41959step1 raw41959step1Labels := by
      have ha : raw41959step1 = (fun i j => raw41959step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41959step1 raw41959step0; decide +kernel
      have hl : raw41959step1Labels = raw41959step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41959step0 raw41959step0Labels permutation44 permutation7
    mixedMoment B raw41959step1 raw41959step1Labels = mixedMoment B raw41959step2 raw41959step2Labels := by
      have ha : raw41959step2 = -raw41959step1 := by apply Matrix.ext; change ∀ i j, raw41959step2 i j = -(raw41959step1 i j); unfold raw41959step2 raw41959step1; decide +kernel
      have hl : raw41959step2Labels = raw41959step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41959step2 raw41959step2Labels = mixedMoment B raw41959step3 raw41959step3Labels := by
      have ha : raw41959step3 = raw41959step2 := by apply Matrix.ext; unfold raw41959step3 raw41959step2; decide +kernel
      have hl : raw41959step2Labels = labelEmbedding6 ∘ raw41959step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41959step2 raw41959step2Labels raw41959step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4151 node4151Labels := by rfl

theorem canonical41960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41960 raw41960Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw41960 raw41960Labels = mixedMoment B raw41960step0 raw41960step0Labels := by
      have ha : raw41960step0 = (fun i j => raw41960 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41960step0 raw41960; decide +kernel
      have hl : raw41960step0Labels = raw41960Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41960 raw41960Labels permutation157 permutation2
    mixedMoment B raw41960step0 raw41960step0Labels = mixedMoment B raw41960step1 raw41960step1Labels := by
      have ha : raw41960step1 = raw41960step0 := by apply Matrix.ext; unfold raw41960step1 raw41960step0; decide +kernel
      have hl : raw41960step0Labels = labelEmbedding1 ∘ raw41960step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41960step0 raw41960step0Labels raw41960step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

theorem canonical41961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41961 raw41961Labels = mixedMoment B node4150 node4150Labels := by
  calc
    mixedMoment B raw41961 raw41961Labels = mixedMoment B raw41961step0 raw41961step0Labels := by
      have ha : raw41961step0 = (fun i j => raw41961 (permutation247 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41961step0 raw41961; decide +kernel
      have hl : raw41961step0Labels = raw41961Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41961 raw41961Labels permutation247 permutation7
    mixedMoment B raw41961step0 raw41961step0Labels = mixedMoment B raw41961step1 raw41961step1Labels := by
      have ha : raw41961step1 = -raw41961step0 := by apply Matrix.ext; change ∀ i j, raw41961step1 i j = -(raw41961step0 i j); unfold raw41961step1 raw41961step0; decide +kernel
      have hl : raw41961step1Labels = raw41961step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41961step1 raw41961step1Labels = mixedMoment B raw41961step2 raw41961step2Labels := by
      have ha : raw41961step2 = raw41961step1 := by apply Matrix.ext; unfold raw41961step2 raw41961step1; decide +kernel
      have hl : raw41961step1Labels = labelEmbedding6 ∘ raw41961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41961step1 raw41961step1Labels raw41961step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4150 node4150Labels := by rfl

theorem canonical41962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41962 raw41962Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw41962 raw41962Labels = mixedMoment B raw41962step0 raw41962step0Labels := by
      have hz : ∀ j, raw41962 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41962step0 = (fun i j => raw41962 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41962step0 raw41962; decide +kernel
      have hl : raw41962step0Labels = raw41962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41962 raw41962Labels permutation434 hz
    mixedMoment B raw41962step0 raw41962step0Labels = mixedMoment B raw41962step1 raw41962step1Labels := by
      have hz : ∀ j, raw41962step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41962step1 = (fun i j => raw41962step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41962step1 raw41962step0; decide +kernel
      have hl : raw41962step1Labels = raw41962step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41962step0 raw41962step0Labels permutation80 hz
    mixedMoment B raw41962step1 raw41962step1Labels = mixedMoment B raw41962step2 raw41962step2Labels := by
      have ha : raw41962step2 = raw41962step1 := by apply Matrix.ext; unfold raw41962step2 raw41962step1; decide +kernel
      have hl : raw41962step1Labels = labelEmbedding1 ∘ raw41962step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41962step1 raw41962step1Labels raw41962step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1516 node1516Labels := by rfl

theorem canonical41963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41963 raw41963Labels = mixedMoment B node4156 node4156Labels := by
  calc
    mixedMoment B raw41963 raw41963Labels = mixedMoment B raw41963step0 raw41963step0Labels := by
      have hz : ∀ j, raw41963 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41963step0 = (fun i j => raw41963 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41963step0 raw41963; decide +kernel
      have hl : raw41963step0Labels = raw41963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41963 raw41963Labels permutation434 hz
    mixedMoment B raw41963step0 raw41963step0Labels = mixedMoment B raw41963step1 raw41963step1Labels := by
      have hz : ∀ j, raw41963step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41963step1 = (fun i j => raw41963step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41963step1 raw41963step0; decide +kernel
      have hl : raw41963step1Labels = raw41963step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41963step0 raw41963step0Labels permutation80 hz
    mixedMoment B raw41963step1 raw41963step1Labels = mixedMoment B raw41963step2 raw41963step2Labels := by
      have ha : raw41963step2 = (fun i j => raw41963step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41963step2 raw41963step1; decide +kernel
      have hl : raw41963step2Labels = raw41963step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41963step1 raw41963step1Labels permutation10 permutation7
    mixedMoment B raw41963step2 raw41963step2Labels = mixedMoment B raw41963step3 raw41963step3Labels := by
      have ha : raw41963step3 = -raw41963step2 := by apply Matrix.ext; change ∀ i j, raw41963step3 i j = -(raw41963step2 i j); unfold raw41963step3 raw41963step2; decide +kernel
      have hl : raw41963step3Labels = raw41963step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41963step3 raw41963step3Labels = mixedMoment B raw41963step4 raw41963step4Labels := by
      have ha : raw41963step4 = raw41963step3 := by apply Matrix.ext; unfold raw41963step4 raw41963step3; decide +kernel
      have hl : raw41963step3Labels = labelEmbedding6 ∘ raw41963step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41963step3 raw41963step3Labels raw41963step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4156 node4156Labels := by rfl

theorem canonical41964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41964 raw41964Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw41964 raw41964Labels = mixedMoment B raw41964step0 raw41964step0Labels := by
      have hz : ∀ j, raw41964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41964step0 = (fun i j => raw41964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41964step0 raw41964; decide +kernel
      have hl : raw41964step0Labels = raw41964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41964 raw41964Labels permutation346 hz
    mixedMoment B raw41964step0 raw41964step0Labels = mixedMoment B raw41964step1 raw41964step1Labels := by
      have ha : raw41964step1 = (fun i j => raw41964step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41964step1 raw41964step0; decide +kernel
      have hl : raw41964step1Labels = raw41964step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41964step0 raw41964step0Labels permutation37 permutation2
    mixedMoment B raw41964step1 raw41964step1Labels = mixedMoment B raw41964step2 raw41964step2Labels := by
      have ha : raw41964step2 = raw41964step1 := by apply Matrix.ext; unfold raw41964step2 raw41964step1; decide +kernel
      have hl : raw41964step1Labels = labelEmbedding1 ∘ raw41964step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41964step1 raw41964step1Labels raw41964step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1514 node1514Labels := by rfl

theorem canonical41965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41965 raw41965Labels = mixedMoment B node4153 node4153Labels := by
  calc
    mixedMoment B raw41965 raw41965Labels = mixedMoment B raw41965step0 raw41965step0Labels := by
      have hz : ∀ j, raw41965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41965step0 = (fun i j => raw41965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41965step0 raw41965; decide +kernel
      have hl : raw41965step0Labels = raw41965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41965 raw41965Labels permutation346 hz
    mixedMoment B raw41965step0 raw41965step0Labels = mixedMoment B raw41965step1 raw41965step1Labels := by
      have ha : raw41965step1 = (fun i j => raw41965step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41965step1 raw41965step0; decide +kernel
      have hl : raw41965step1Labels = raw41965step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41965step0 raw41965step0Labels permutation51 permutation7
    mixedMoment B raw41965step1 raw41965step1Labels = mixedMoment B raw41965step2 raw41965step2Labels := by
      have ha : raw41965step2 = -raw41965step1 := by apply Matrix.ext; change ∀ i j, raw41965step2 i j = -(raw41965step1 i j); unfold raw41965step2 raw41965step1; decide +kernel
      have hl : raw41965step2Labels = raw41965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41965step2 raw41965step2Labels = mixedMoment B raw41965step3 raw41965step3Labels := by
      have ha : raw41965step3 = raw41965step2 := by apply Matrix.ext; unfold raw41965step3 raw41965step2; decide +kernel
      have hl : raw41965step2Labels = labelEmbedding6 ∘ raw41965step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41965step2 raw41965step2Labels raw41965step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4153 node4153Labels := by rfl

theorem canonical41966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41966 raw41966Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw41966 raw41966Labels = mixedMoment B raw41966step0 raw41966step0Labels := by
      have hz : ∀ j, raw41966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41966step0 = (fun i j => raw41966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41966step0 raw41966; decide +kernel
      have hl : raw41966step0Labels = raw41966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41966 raw41966Labels permutation346 hz
    mixedMoment B raw41966step0 raw41966step0Labels = mixedMoment B raw41966step1 raw41966step1Labels := by
      have ha : raw41966step1 = (fun i j => raw41966step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41966step1 raw41966step0; decide +kernel
      have hl : raw41966step1Labels = raw41966step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41966step0 raw41966step0Labels permutation36 permutation2
    mixedMoment B raw41966step1 raw41966step1Labels = mixedMoment B raw41966step2 raw41966step2Labels := by
      have ha : raw41966step2 = raw41966step1 := by apply Matrix.ext; unfold raw41966step2 raw41966step1; decide +kernel
      have hl : raw41966step1Labels = labelEmbedding1 ∘ raw41966step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41966step1 raw41966step1Labels raw41966step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1515 node1515Labels := by rfl

theorem canonical41967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41967 raw41967Labels = mixedMoment B node4155 node4155Labels := by
  calc
    mixedMoment B raw41967 raw41967Labels = mixedMoment B raw41967step0 raw41967step0Labels := by
      have hz : ∀ j, raw41967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41967step0 = (fun i j => raw41967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41967step0 raw41967; decide +kernel
      have hl : raw41967step0Labels = raw41967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41967 raw41967Labels permutation346 hz
    mixedMoment B raw41967step0 raw41967step0Labels = mixedMoment B raw41967step1 raw41967step1Labels := by
      have ha : raw41967step1 = (fun i j => raw41967step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41967step1 raw41967step0; decide +kernel
      have hl : raw41967step1Labels = raw41967step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41967step0 raw41967step0Labels permutation50 permutation7
    mixedMoment B raw41967step1 raw41967step1Labels = mixedMoment B raw41967step2 raw41967step2Labels := by
      have ha : raw41967step2 = -raw41967step1 := by apply Matrix.ext; change ∀ i j, raw41967step2 i j = -(raw41967step1 i j); unfold raw41967step2 raw41967step1; decide +kernel
      have hl : raw41967step2Labels = raw41967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41967step2 raw41967step2Labels = mixedMoment B raw41967step3 raw41967step3Labels := by
      have ha : raw41967step3 = raw41967step2 := by apply Matrix.ext; unfold raw41967step3 raw41967step2; decide +kernel
      have hl : raw41967step2Labels = labelEmbedding6 ∘ raw41967step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41967step2 raw41967step2Labels raw41967step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4155 node4155Labels := by rfl

theorem canonical41968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41968 raw41968Labels = mixedMoment B node1534 node1534Labels := by
  calc
    mixedMoment B raw41968 raw41968Labels = mixedMoment B raw41968step0 raw41968step0Labels := by
      have hz : ∀ j, raw41968 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41968step0 = (fun i j => raw41968 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41968step0 raw41968; decide +kernel
      have hl : raw41968step0Labels = raw41968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41968 raw41968Labels permutation434 hz
    mixedMoment B raw41968step0 raw41968step0Labels = mixedMoment B raw41968step1 raw41968step1Labels := by
      have hz : ∀ j, raw41968step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41968step1 = (fun i j => raw41968step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41968step1 raw41968step0; decide +kernel
      have hl : raw41968step1Labels = raw41968step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41968step0 raw41968step0Labels permutation80 hz
    mixedMoment B raw41968step1 raw41968step1Labels = mixedMoment B raw41968step2 raw41968step2Labels := by
      have hz : ∀ j, raw41968step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41968step2 = (fun i j => raw41968step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41968step2 raw41968step1; decide +kernel
      have hl : raw41968step2Labels = raw41968step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41968step1 raw41968step1Labels permutation14 hz
    mixedMoment B raw41968step2 raw41968step2Labels = mixedMoment B raw41968step3 raw41968step3Labels := by
      have ha : raw41968step3 = raw41968step2 := by apply Matrix.ext; unfold raw41968step3 raw41968step2; decide +kernel
      have hl : raw41968step2Labels = labelEmbedding1 ∘ raw41968step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41968step2 raw41968step2Labels raw41968step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1534 node1534Labels := by rfl

theorem canonical41969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41969 raw41969Labels = mixedMoment B node4163 node4163Labels := by
  calc
    mixedMoment B raw41969 raw41969Labels = mixedMoment B raw41969step0 raw41969step0Labels := by
      have hz : ∀ j, raw41969 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41969step0 = (fun i j => raw41969 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41969step0 raw41969; decide +kernel
      have hl : raw41969step0Labels = raw41969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41969 raw41969Labels permutation434 hz
    mixedMoment B raw41969step0 raw41969step0Labels = mixedMoment B raw41969step1 raw41969step1Labels := by
      have hz : ∀ j, raw41969step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41969step1 = (fun i j => raw41969step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41969step1 raw41969step0; decide +kernel
      have hl : raw41969step1Labels = raw41969step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41969step0 raw41969step0Labels permutation80 hz
    mixedMoment B raw41969step1 raw41969step1Labels = mixedMoment B raw41969step2 raw41969step2Labels := by
      have hz : ∀ j, raw41969step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41969step2 = (fun i j => raw41969step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41969step2 raw41969step1; decide +kernel
      have hl : raw41969step2Labels = raw41969step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41969step1 raw41969step1Labels permutation14 hz
    mixedMoment B raw41969step2 raw41969step2Labels = mixedMoment B raw41969step3 raw41969step3Labels := by
      have ha : raw41969step3 = (fun i j => raw41969step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41969step3 raw41969step2; decide +kernel
      have hl : raw41969step3Labels = raw41969step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41969step2 raw41969step2Labels permutation7 permutation6
    _ = mixedMoment B node4163 node4163Labels := by rfl

theorem canonical41970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41970 raw41970Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw41970 raw41970Labels = mixedMoment B raw41970step0 raw41970step0Labels := by
      have hz : ∀ j, raw41970 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41970step0 = (fun i j => raw41970 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41970step0 raw41970; decide +kernel
      have hl : raw41970step0Labels = raw41970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41970 raw41970Labels permutation346 hz
    mixedMoment B raw41970step0 raw41970step0Labels = mixedMoment B raw41970step1 raw41970step1Labels := by
      have hz : ∀ j, raw41970step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41970step1 = (fun i j => raw41970step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41970step1 raw41970step0; decide +kernel
      have hl : raw41970step1Labels = raw41970step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41970step0 raw41970step0Labels permutation56 hz
    mixedMoment B raw41970step1 raw41970step1Labels = mixedMoment B raw41970step2 raw41970step2Labels := by
      have ha : raw41970step2 = (fun i j => raw41970step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41970step2 raw41970step1; decide +kernel
      have hl : raw41970step2Labels = raw41970step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41970step1 raw41970step1Labels permutation13 permutation2
    mixedMoment B raw41970step2 raw41970step2Labels = mixedMoment B raw41970step3 raw41970step3Labels := by
      have ha : raw41970step3 = raw41970step2 := by apply Matrix.ext; unfold raw41970step3 raw41970step2; decide +kernel
      have hl : raw41970step2Labels = labelEmbedding1 ∘ raw41970step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41970step2 raw41970step2Labels raw41970step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1532 node1532Labels := by rfl

theorem canonical41971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41971 raw41971Labels = mixedMoment B node4159 node4159Labels := by
  calc
    mixedMoment B raw41971 raw41971Labels = mixedMoment B raw41971step0 raw41971step0Labels := by
      have hz : ∀ j, raw41971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41971step0 = (fun i j => raw41971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41971step0 raw41971; decide +kernel
      have hl : raw41971step0Labels = raw41971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41971 raw41971Labels permutation346 hz
    mixedMoment B raw41971step0 raw41971step0Labels = mixedMoment B raw41971step1 raw41971step1Labels := by
      have hz : ∀ j, raw41971step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41971step1 = (fun i j => raw41971step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41971step1 raw41971step0; decide +kernel
      have hl : raw41971step1Labels = raw41971step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41971step0 raw41971step0Labels permutation56 hz
    mixedMoment B raw41971step1 raw41971step1Labels = mixedMoment B raw41971step2 raw41971step2Labels := by
      have ha : raw41971step2 = (fun i j => raw41971step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41971step2 raw41971step1; decide +kernel
      have hl : raw41971step2Labels = raw41971step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41971step1 raw41971step1Labels permutation13 permutation7
    mixedMoment B raw41971step2 raw41971step2Labels = mixedMoment B raw41971step3 raw41971step3Labels := by
      have ha : raw41971step3 = -raw41971step2 := by apply Matrix.ext; change ∀ i j, raw41971step3 i j = -(raw41971step2 i j); unfold raw41971step3 raw41971step2; decide +kernel
      have hl : raw41971step3Labels = raw41971step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41971step3 raw41971step3Labels = mixedMoment B raw41971step4 raw41971step4Labels := by
      have ha : raw41971step4 = raw41971step3 := by apply Matrix.ext; unfold raw41971step4 raw41971step3; decide +kernel
      have hl : raw41971step3Labels = labelEmbedding6 ∘ raw41971step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41971step3 raw41971step3Labels raw41971step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4159 node4159Labels := by rfl

theorem canonical41972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41972 raw41972Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw41972 raw41972Labels = mixedMoment B raw41972step0 raw41972step0Labels := by
      have hz : ∀ j, raw41972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41972step0 = (fun i j => raw41972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41972step0 raw41972; decide +kernel
      have hl : raw41972step0Labels = raw41972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41972 raw41972Labels permutation346 hz
    mixedMoment B raw41972step0 raw41972step0Labels = mixedMoment B raw41972step1 raw41972step1Labels := by
      have hz : ∀ j, raw41972step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41972step1 = (fun i j => raw41972step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41972step1 raw41972step0; decide +kernel
      have hl : raw41972step1Labels = raw41972step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41972step0 raw41972step0Labels permutation56 hz
    mixedMoment B raw41972step1 raw41972step1Labels = mixedMoment B raw41972step2 raw41972step2Labels := by
      have ha : raw41972step2 = (fun i j => raw41972step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41972step2 raw41972step1; decide +kernel
      have hl : raw41972step2Labels = raw41972step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41972step1 raw41972step1Labels permutation13 permutation2
    mixedMoment B raw41972step2 raw41972step2Labels = mixedMoment B raw41972step3 raw41972step3Labels := by
      have ha : raw41972step3 = raw41972step2 := by apply Matrix.ext; unfold raw41972step3 raw41972step2; decide +kernel
      have hl : raw41972step2Labels = labelEmbedding1 ∘ raw41972step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41972step2 raw41972step2Labels raw41972step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1533 node1533Labels := by rfl

theorem canonical41973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41973 raw41973Labels = mixedMoment B node4161 node4161Labels := by
  calc
    mixedMoment B raw41973 raw41973Labels = mixedMoment B raw41973step0 raw41973step0Labels := by
      have hz : ∀ j, raw41973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41973step0 = (fun i j => raw41973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41973step0 raw41973; decide +kernel
      have hl : raw41973step0Labels = raw41973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41973 raw41973Labels permutation346 hz
    mixedMoment B raw41973step0 raw41973step0Labels = mixedMoment B raw41973step1 raw41973step1Labels := by
      have hz : ∀ j, raw41973step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41973step1 = (fun i j => raw41973step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41973step1 raw41973step0; decide +kernel
      have hl : raw41973step1Labels = raw41973step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41973step0 raw41973step0Labels permutation56 hz
    mixedMoment B raw41973step1 raw41973step1Labels = mixedMoment B raw41973step2 raw41973step2Labels := by
      have ha : raw41973step2 = (fun i j => raw41973step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41973step2 raw41973step1; decide +kernel
      have hl : raw41973step2Labels = raw41973step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41973step1 raw41973step1Labels permutation13 permutation7
    mixedMoment B raw41973step2 raw41973step2Labels = mixedMoment B raw41973step3 raw41973step3Labels := by
      have ha : raw41973step3 = -raw41973step2 := by apply Matrix.ext; change ∀ i j, raw41973step3 i j = -(raw41973step2 i j); unfold raw41973step3 raw41973step2; decide +kernel
      have hl : raw41973step3Labels = raw41973step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41973step3 raw41973step3Labels = mixedMoment B raw41973step4 raw41973step4Labels := by
      have ha : raw41973step4 = raw41973step3 := by apply Matrix.ext; unfold raw41973step4 raw41973step3; decide +kernel
      have hl : raw41973step3Labels = labelEmbedding6 ∘ raw41973step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41973step3 raw41973step3Labels raw41973step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4161 node4161Labels := by rfl

theorem canonical41974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41974 raw41974Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw41974 raw41974Labels = mixedMoment B raw41974step0 raw41974step0Labels := by
      have hz : ∀ j, raw41974 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41974step0 = (fun i j => raw41974 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41974step0 raw41974; decide +kernel
      have hl : raw41974step0Labels = raw41974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41974 raw41974Labels permutation520 hz
    mixedMoment B raw41974step0 raw41974step0Labels = mixedMoment B raw41974step1 raw41974step1Labels := by
      have hz : ∀ j, raw41974step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41974step1 = (fun i j => raw41974step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41974step1 raw41974step0; decide +kernel
      have hl : raw41974step1Labels = raw41974step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41974step0 raw41974step0Labels permutation104 hz
    mixedMoment B raw41974step1 raw41974step1Labels = mixedMoment B raw41974step2 raw41974step2Labels := by
      have hz : ∀ j, raw41974step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41974step2 = (fun i j => raw41974step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41974step2 raw41974step1; decide +kernel
      have hl : raw41974step2Labels = raw41974step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41974step1 raw41974step1Labels permutation20 hz
    mixedMoment B raw41974step2 raw41974step2Labels = mixedMoment B raw41974step3 raw41974step3Labels := by
      have ha : raw41974step3 = (fun i j => raw41974step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41974step3 raw41974step2; decide +kernel
      have hl : raw41974step3Labels = raw41974step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41974step2 raw41974step2Labels permutation2 permutation4
    mixedMoment B raw41974step3 raw41974step3Labels = mixedMoment B raw41974step4 raw41974step4Labels := by
      have ha : raw41974step4 = -raw41974step3 := by apply Matrix.ext; change ∀ i j, raw41974step4 i j = -(raw41974step3 i j); unfold raw41974step4 raw41974step3; decide +kernel
      have hl : raw41974step4Labels = raw41974step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41974step4 raw41974step4Labels = mixedMoment B raw41974step5 raw41974step5Labels := by
      have ha : raw41974step5 = raw41974step4 := by apply Matrix.ext; unfold raw41974step5 raw41974step4; decide +kernel
      have hl : raw41974step4Labels = labelEmbedding1 ∘ raw41974step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41974step4 raw41974step4Labels raw41974step5Labels labelEmbedding1 hl
    _ = mixedMoment B node3114 node3114Labels := by rfl

theorem canonical41975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41975 raw41975Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw41975 raw41975Labels = mixedMoment B raw41975step0 raw41975step0Labels := by
      have hz : ∀ j, raw41975 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41975step0 = (fun i j => raw41975 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41975step0 raw41975; decide +kernel
      have hl : raw41975step0Labels = raw41975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41975 raw41975Labels permutation520 hz
    mixedMoment B raw41975step0 raw41975step0Labels = mixedMoment B raw41975step1 raw41975step1Labels := by
      have hz : ∀ j, raw41975step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41975step1 = (fun i j => raw41975step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41975step1 raw41975step0; decide +kernel
      have hl : raw41975step1Labels = raw41975step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41975step0 raw41975step0Labels permutation104 hz
    mixedMoment B raw41975step1 raw41975step1Labels = mixedMoment B raw41975step2 raw41975step2Labels := by
      have hz : ∀ j, raw41975step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41975step2 = (fun i j => raw41975step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41975step2 raw41975step1; decide +kernel
      have hl : raw41975step2Labels = raw41975step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41975step1 raw41975step1Labels permutation20 hz
    mixedMoment B raw41975step2 raw41975step2Labels = mixedMoment B raw41975step3 raw41975step3Labels := by
      have ha : raw41975step3 = (fun i j => raw41975step2 (permutation7 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41975step3 raw41975step2; decide +kernel
      have hl : raw41975step3Labels = raw41975step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41975step2 raw41975step2Labels permutation7 permutation5
    mixedMoment B raw41975step3 raw41975step3Labels = mixedMoment B raw41975step4 raw41975step4Labels := by
      have ha : raw41975step4 = raw41975step3 := by apply Matrix.ext; unfold raw41975step4 raw41975step3; decide +kernel
      have hl : raw41975step3Labels = labelEmbedding9 ∘ raw41975step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41975step3 raw41975step3Labels raw41975step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

theorem canonical41976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41976 raw41976Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw41976 raw41976Labels = mixedMoment B raw41976step0 raw41976step0Labels := by
      have hz : ∀ j, raw41976 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41976step0 = (fun i j => raw41976 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41976step0 raw41976; decide +kernel
      have hl : raw41976step0Labels = raw41976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41976 raw41976Labels permutation434 hz
    mixedMoment B raw41976step0 raw41976step0Labels = mixedMoment B raw41976step1 raw41976step1Labels := by
      have hz : ∀ j, raw41976step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41976step1 = (fun i j => raw41976step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41976step1 raw41976step0; decide +kernel
      have hl : raw41976step1Labels = raw41976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41976step0 raw41976step0Labels permutation80 hz
    mixedMoment B raw41976step1 raw41976step1Labels = mixedMoment B raw41976step2 raw41976step2Labels := by
      have ha : raw41976step2 = (fun i j => raw41976step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41976step2 raw41976step1; decide +kernel
      have hl : raw41976step2Labels = raw41976step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41976step1 raw41976step1Labels permutation8 permutation4
    mixedMoment B raw41976step2 raw41976step2Labels = mixedMoment B raw41976step3 raw41976step3Labels := by
      have ha : raw41976step3 = -raw41976step2 := by apply Matrix.ext; change ∀ i j, raw41976step3 i j = -(raw41976step2 i j); unfold raw41976step3 raw41976step2; decide +kernel
      have hl : raw41976step3Labels = raw41976step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41976step3 raw41976step3Labels = mixedMoment B raw41976step4 raw41976step4Labels := by
      have ha : raw41976step4 = raw41976step3 := by apply Matrix.ext; unfold raw41976step4 raw41976step3; decide +kernel
      have hl : raw41976step3Labels = labelEmbedding1 ∘ raw41976step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41976step3 raw41976step3Labels raw41976step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3112 node3112Labels := by rfl

theorem canonical41977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41977 raw41977Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw41977 raw41977Labels = mixedMoment B raw41977step0 raw41977step0Labels := by
      have hz : ∀ j, raw41977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41977step0 = (fun i j => raw41977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41977step0 raw41977; decide +kernel
      have hl : raw41977step0Labels = raw41977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41977 raw41977Labels permutation434 hz
    mixedMoment B raw41977step0 raw41977step0Labels = mixedMoment B raw41977step1 raw41977step1Labels := by
      have hz : ∀ j, raw41977step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41977step1 = (fun i j => raw41977step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41977step1 raw41977step0; decide +kernel
      have hl : raw41977step1Labels = raw41977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41977step0 raw41977step0Labels permutation80 hz
    mixedMoment B raw41977step1 raw41977step1Labels = mixedMoment B raw41977step2 raw41977step2Labels := by
      have ha : raw41977step2 = (fun i j => raw41977step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41977step2 raw41977step1; decide +kernel
      have hl : raw41977step2Labels = raw41977step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41977step1 raw41977step1Labels permutation8 permutation5
    mixedMoment B raw41977step2 raw41977step2Labels = mixedMoment B raw41977step3 raw41977step3Labels := by
      have ha : raw41977step3 = -raw41977step2 := by apply Matrix.ext; change ∀ i j, raw41977step3 i j = -(raw41977step2 i j); unfold raw41977step3 raw41977step2; decide +kernel
      have hl : raw41977step3Labels = raw41977step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41977step3 raw41977step3Labels = mixedMoment B raw41977step4 raw41977step4Labels := by
      have ha : raw41977step4 = raw41977step3 := by apply Matrix.ext; unfold raw41977step4 raw41977step3; decide +kernel
      have hl : raw41977step3Labels = labelEmbedding9 ∘ raw41977step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41977step3 raw41977step3Labels raw41977step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

theorem canonical41978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41978 raw41978Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw41978 raw41978Labels = mixedMoment B raw41978step0 raw41978step0Labels := by
      have hz : ∀ j, raw41978 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41978step0 = (fun i j => raw41978 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41978step0 raw41978; decide +kernel
      have hl : raw41978step0Labels = raw41978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41978 raw41978Labels permutation434 hz
    mixedMoment B raw41978step0 raw41978step0Labels = mixedMoment B raw41978step1 raw41978step1Labels := by
      have hz : ∀ j, raw41978step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41978step1 = (fun i j => raw41978step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41978step1 raw41978step0; decide +kernel
      have hl : raw41978step1Labels = raw41978step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41978step0 raw41978step0Labels permutation80 hz
    mixedMoment B raw41978step1 raw41978step1Labels = mixedMoment B raw41978step2 raw41978step2Labels := by
      have ha : raw41978step2 = (fun i j => raw41978step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41978step2 raw41978step1; decide +kernel
      have hl : raw41978step2Labels = raw41978step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41978step1 raw41978step1Labels permutation9 permutation4
    mixedMoment B raw41978step2 raw41978step2Labels = mixedMoment B raw41978step3 raw41978step3Labels := by
      have ha : raw41978step3 = -raw41978step2 := by apply Matrix.ext; change ∀ i j, raw41978step3 i j = -(raw41978step2 i j); unfold raw41978step3 raw41978step2; decide +kernel
      have hl : raw41978step3Labels = raw41978step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41978step3 raw41978step3Labels = mixedMoment B raw41978step4 raw41978step4Labels := by
      have ha : raw41978step4 = raw41978step3 := by apply Matrix.ext; unfold raw41978step4 raw41978step3; decide +kernel
      have hl : raw41978step3Labels = labelEmbedding1 ∘ raw41978step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41978step3 raw41978step3Labels raw41978step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3110 node3110Labels := by rfl

theorem canonical41979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41979 raw41979Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw41979 raw41979Labels = mixedMoment B raw41979step0 raw41979step0Labels := by
      have hz : ∀ j, raw41979 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41979step0 = (fun i j => raw41979 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41979step0 raw41979; decide +kernel
      have hl : raw41979step0Labels = raw41979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41979 raw41979Labels permutation434 hz
    mixedMoment B raw41979step0 raw41979step0Labels = mixedMoment B raw41979step1 raw41979step1Labels := by
      have hz : ∀ j, raw41979step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41979step1 = (fun i j => raw41979step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41979step1 raw41979step0; decide +kernel
      have hl : raw41979step1Labels = raw41979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41979step0 raw41979step0Labels permutation80 hz
    mixedMoment B raw41979step1 raw41979step1Labels = mixedMoment B raw41979step2 raw41979step2Labels := by
      have ha : raw41979step2 = (fun i j => raw41979step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41979step2 raw41979step1; decide +kernel
      have hl : raw41979step2Labels = raw41979step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41979step1 raw41979step1Labels permutation9 permutation5
    mixedMoment B raw41979step2 raw41979step2Labels = mixedMoment B raw41979step3 raw41979step3Labels := by
      have ha : raw41979step3 = -raw41979step2 := by apply Matrix.ext; change ∀ i j, raw41979step3 i j = -(raw41979step2 i j); unfold raw41979step3 raw41979step2; decide +kernel
      have hl : raw41979step3Labels = raw41979step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41979step3 raw41979step3Labels = mixedMoment B raw41979step4 raw41979step4Labels := by
      have ha : raw41979step4 = raw41979step3 := by apply Matrix.ext; unfold raw41979step4 raw41979step3; decide +kernel
      have hl : raw41979step3Labels = labelEmbedding9 ∘ raw41979step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41979step3 raw41979step3Labels raw41979step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical41980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41980 raw41980Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw41980 raw41980Labels = mixedMoment B raw41980step0 raw41980step0Labels := by
      have hz : ∀ j, raw41980 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41980step0 = (fun i j => raw41980 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41980step0 raw41980; decide +kernel
      have hl : raw41980step0Labels = raw41980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41980 raw41980Labels permutation434 hz
    mixedMoment B raw41980step0 raw41980step0Labels = mixedMoment B raw41980step1 raw41980step1Labels := by
      have hz : ∀ j, raw41980step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41980step1 = (fun i j => raw41980step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41980step1 raw41980step0; decide +kernel
      have hl : raw41980step1Labels = raw41980step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41980step0 raw41980step0Labels permutation80 hz
    mixedMoment B raw41980step1 raw41980step1Labels = mixedMoment B raw41980step2 raw41980step2Labels := by
      have ha : raw41980step2 = (fun i j => raw41980step1 (permutation23 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41980step2 raw41980step1; decide +kernel
      have hl : raw41980step2Labels = raw41980step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41980step1 raw41980step1Labels permutation23 permutation4
    mixedMoment B raw41980step2 raw41980step2Labels = mixedMoment B raw41980step3 raw41980step3Labels := by
      have ha : raw41980step3 = raw41980step2 := by apply Matrix.ext; unfold raw41980step3 raw41980step2; decide +kernel
      have hl : raw41980step2Labels = labelEmbedding1 ∘ raw41980step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41980step2 raw41980step2Labels raw41980step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2734 node2734Labels := by rfl

theorem canonical41981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41981 raw41981Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw41981 raw41981Labels = mixedMoment B raw41981step0 raw41981step0Labels := by
      have hz : ∀ j, raw41981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41981step0 = (fun i j => raw41981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41981step0 raw41981; decide +kernel
      have hl : raw41981step0Labels = raw41981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41981 raw41981Labels permutation434 hz
    mixedMoment B raw41981step0 raw41981step0Labels = mixedMoment B raw41981step1 raw41981step1Labels := by
      have hz : ∀ j, raw41981step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41981step1 = (fun i j => raw41981step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41981step1 raw41981step0; decide +kernel
      have hl : raw41981step1Labels = raw41981step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41981step0 raw41981step0Labels permutation80 hz
    mixedMoment B raw41981step1 raw41981step1Labels = mixedMoment B raw41981step2 raw41981step2Labels := by
      have ha : raw41981step2 = (fun i j => raw41981step1 (permutation23 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41981step2 raw41981step1; decide +kernel
      have hl : raw41981step2Labels = raw41981step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41981step1 raw41981step1Labels permutation23 permutation4
    mixedMoment B raw41981step2 raw41981step2Labels = mixedMoment B raw41981step3 raw41981step3Labels := by
      have ha : raw41981step3 = raw41981step2 := by apply Matrix.ext; unfold raw41981step3 raw41981step2; decide +kernel
      have hl : raw41981step2Labels = labelEmbedding10 ∘ raw41981step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41981step2 raw41981step2Labels raw41981step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5268 node5268Labels := by rfl

theorem canonical41982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41982 raw41982Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw41982 raw41982Labels = mixedMoment B raw41982step0 raw41982step0Labels := by
      have hz : ∀ j, raw41982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41982step0 = (fun i j => raw41982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41982step0 raw41982; decide +kernel
      have hl : raw41982step0Labels = raw41982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41982 raw41982Labels permutation346 hz
    mixedMoment B raw41982step0 raw41982step0Labels = mixedMoment B raw41982step1 raw41982step1Labels := by
      have ha : raw41982step1 = (fun i j => raw41982step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41982step1 raw41982step0; decide +kernel
      have hl : raw41982step1Labels = raw41982step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41982step0 raw41982step0Labels permutation44 permutation4
    mixedMoment B raw41982step1 raw41982step1Labels = mixedMoment B raw41982step2 raw41982step2Labels := by
      have ha : raw41982step2 = -raw41982step1 := by apply Matrix.ext; change ∀ i j, raw41982step2 i j = -(raw41982step1 i j); unfold raw41982step2 raw41982step1; decide +kernel
      have hl : raw41982step2Labels = raw41982step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41982step2 raw41982step2Labels = mixedMoment B raw41982step3 raw41982step3Labels := by
      have ha : raw41982step3 = raw41982step2 := by apply Matrix.ext; unfold raw41982step3 raw41982step2; decide +kernel
      have hl : raw41982step2Labels = labelEmbedding1 ∘ raw41982step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41982step2 raw41982step2Labels raw41982step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3089 node3089Labels := by rfl

theorem canonical41983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41983 raw41983Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw41983 raw41983Labels = mixedMoment B raw41983step0 raw41983step0Labels := by
      have hz : ∀ j, raw41983 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41983step0 = (fun i j => raw41983 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41983step0 raw41983; decide +kernel
      have hl : raw41983step0Labels = raw41983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41983 raw41983Labels permutation346 hz
    mixedMoment B raw41983step0 raw41983step0Labels = mixedMoment B raw41983step1 raw41983step1Labels := by
      have ha : raw41983step1 = (fun i j => raw41983step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41983step1 raw41983step0; decide +kernel
      have hl : raw41983step1Labels = raw41983step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41983step0 raw41983step0Labels permutation34 permutation5
    mixedMoment B raw41983step1 raw41983step1Labels = mixedMoment B raw41983step2 raw41983step2Labels := by
      have ha : raw41983step2 = -raw41983step1 := by apply Matrix.ext; change ∀ i j, raw41983step2 i j = -(raw41983step1 i j); unfold raw41983step2 raw41983step1; decide +kernel
      have hl : raw41983step2Labels = raw41983step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41983step2 raw41983step2Labels = mixedMoment B raw41983step3 raw41983step3Labels := by
      have ha : raw41983step3 = raw41983step2 := by apply Matrix.ext; unfold raw41983step3 raw41983step2; decide +kernel
      have hl : raw41983step2Labels = labelEmbedding9 ∘ raw41983step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41983step2 raw41983step2Labels raw41983step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2304) =
      Integer.Sparse.eval keyMomentRow2304 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2304).leftCharge (GramAssembly.key 2304).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1720) := by
    have ha : gramCharges (GramAssembly.key 2304).leftCharge (GramAssembly.key 2304).rightCharge = raw41920 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41920Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41920 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2304).leftCharge (GramAssembly.key 2304).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4367) := by
    have ha : gramCharges (GramAssembly.key 2304).leftCharge (GramAssembly.key 2304).rightCharge = raw41921 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41921Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41921 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2304).leftCharge (GramAssembly.key 2304).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2304).leftCharge (GramAssembly.key 2304).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2304, Integer.Sparse.eval] <;> ring

theorem keyMoment2305 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2305) =
      Integer.Sparse.eval keyMomentRow2305 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2305).leftCharge (GramAssembly.key 2305).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1723) := by
    have ha : gramCharges (GramAssembly.key 2305).leftCharge (GramAssembly.key 2305).rightCharge = raw41922 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41922Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41922 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2305).leftCharge (GramAssembly.key 2305).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4440) := by
    have ha : gramCharges (GramAssembly.key 2305).leftCharge (GramAssembly.key 2305).rightCharge = raw41923 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41923Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41923 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2305).leftCharge (GramAssembly.key 2305).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2305).leftCharge (GramAssembly.key 2305).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2305, Integer.Sparse.eval] <;> ring

theorem keyMoment2306 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2306) =
      Integer.Sparse.eval keyMomentRow2306 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2306).leftCharge (GramAssembly.key 2306).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1721) := by
    have ha : gramCharges (GramAssembly.key 2306).leftCharge (GramAssembly.key 2306).rightCharge = raw41924 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41924Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41924 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2306).leftCharge (GramAssembly.key 2306).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4369) := by
    have ha : gramCharges (GramAssembly.key 2306).leftCharge (GramAssembly.key 2306).rightCharge = raw41925 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41925Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41925 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2306).leftCharge (GramAssembly.key 2306).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2306).leftCharge (GramAssembly.key 2306).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2306, Integer.Sparse.eval] <;> ring

theorem keyMoment2307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2307) =
      Integer.Sparse.eval keyMomentRow2307 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2307).leftCharge (GramAssembly.key 2307).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1670) := by
    have ha : gramCharges (GramAssembly.key 2307).leftCharge (GramAssembly.key 2307).rightCharge = raw41926 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41926Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41926 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2307).leftCharge (GramAssembly.key 2307).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4327) := by
    have ha : gramCharges (GramAssembly.key 2307).leftCharge (GramAssembly.key 2307).rightCharge = raw41927 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41927Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41927 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2307).leftCharge (GramAssembly.key 2307).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2307).leftCharge (GramAssembly.key 2307).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2307, Integer.Sparse.eval] <;> ring

theorem keyMoment2308 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2308) =
      Integer.Sparse.eval keyMomentRow2308 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2308).leftCharge (GramAssembly.key 2308).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1757) := by
    have ha : gramCharges (GramAssembly.key 2308).leftCharge (GramAssembly.key 2308).rightCharge = raw41928 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41928Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41928 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2308).leftCharge (GramAssembly.key 2308).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4481) := by
    have ha : gramCharges (GramAssembly.key 2308).leftCharge (GramAssembly.key 2308).rightCharge = raw41929 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41929Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41929 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2308).leftCharge (GramAssembly.key 2308).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2308).leftCharge (GramAssembly.key 2308).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2308, Integer.Sparse.eval] <;> ring

theorem keyMoment2309 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2309) =
      Integer.Sparse.eval keyMomentRow2309 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2309).leftCharge (GramAssembly.key 2309).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1540) := by
    have ha : gramCharges (GramAssembly.key 2309).leftCharge (GramAssembly.key 2309).rightCharge = raw41930 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41930Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41930 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2309).leftCharge (GramAssembly.key 2309).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4189) := by
    have ha : gramCharges (GramAssembly.key 2309).leftCharge (GramAssembly.key 2309).rightCharge = raw41931 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41931Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41931 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2309).leftCharge (GramAssembly.key 2309).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2309).leftCharge (GramAssembly.key 2309).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2309, Integer.Sparse.eval] <;> ring

theorem keyMoment2310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2310) =
      Integer.Sparse.eval keyMomentRow2310 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2310).leftCharge (GramAssembly.key 2310).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1532) := by
    have ha : gramCharges (GramAssembly.key 2310).leftCharge (GramAssembly.key 2310).rightCharge = raw41932 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41932Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41932 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2310).leftCharge (GramAssembly.key 2310).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4159) := by
    have ha : gramCharges (GramAssembly.key 2310).leftCharge (GramAssembly.key 2310).rightCharge = raw41933 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41933Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41933 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2310).leftCharge (GramAssembly.key 2310).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2310).leftCharge (GramAssembly.key 2310).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2310, Integer.Sparse.eval] <;> ring

theorem keyMoment2311 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2311) =
      Integer.Sparse.eval keyMomentRow2311 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2311).leftCharge (GramAssembly.key 2311).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1695) := by
    have ha : gramCharges (GramAssembly.key 2311).leftCharge (GramAssembly.key 2311).rightCharge = raw41934 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41934Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41934 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2311).leftCharge (GramAssembly.key 2311).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4358) := by
    have ha : gramCharges (GramAssembly.key 2311).leftCharge (GramAssembly.key 2311).rightCharge = raw41935 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41935Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41935 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2311).leftCharge (GramAssembly.key 2311).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2311).leftCharge (GramAssembly.key 2311).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2311, Integer.Sparse.eval] <;> ring

theorem keyMoment2312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2312) =
      Integer.Sparse.eval keyMomentRow2312 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2312).leftCharge (GramAssembly.key 2312).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1749) := by
    have ha : gramCharges (GramAssembly.key 2312).leftCharge (GramAssembly.key 2312).rightCharge = raw41936 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41936Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41936 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2312).leftCharge (GramAssembly.key 2312).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4445) := by
    have ha : gramCharges (GramAssembly.key 2312).leftCharge (GramAssembly.key 2312).rightCharge = raw41937 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41937Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41937 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2312).leftCharge (GramAssembly.key 2312).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2312).leftCharge (GramAssembly.key 2312).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2312, Integer.Sparse.eval] <;> ring

theorem keyMoment2313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2313) =
      Integer.Sparse.eval keyMomentRow2313 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2313).leftCharge (GramAssembly.key 2313).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1748) := by
    have ha : gramCharges (GramAssembly.key 2313).leftCharge (GramAssembly.key 2313).rightCharge = raw41938 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41938Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41938 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2313).leftCharge (GramAssembly.key 2313).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4374) := by
    have ha : gramCharges (GramAssembly.key 2313).leftCharge (GramAssembly.key 2313).rightCharge = raw41939 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41939Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41939 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2313).leftCharge (GramAssembly.key 2313).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2313).leftCharge (GramAssembly.key 2313).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2313, Integer.Sparse.eval] <;> ring

theorem keyMoment2314 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2314) =
      Integer.Sparse.eval keyMomentRow2314 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2314).leftCharge (GramAssembly.key 2314).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1688) := by
    have ha : gramCharges (GramAssembly.key 2314).leftCharge (GramAssembly.key 2314).rightCharge = raw41940 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41940Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41940 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2314).leftCharge (GramAssembly.key 2314).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4333) := by
    have ha : gramCharges (GramAssembly.key 2314).leftCharge (GramAssembly.key 2314).rightCharge = raw41941 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41941Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41941 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2314).leftCharge (GramAssembly.key 2314).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2314).leftCharge (GramAssembly.key 2314).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2314, Integer.Sparse.eval] <;> ring

theorem keyMoment2315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2315) =
      Integer.Sparse.eval keyMomentRow2315 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2315).leftCharge (GramAssembly.key 2315).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1689) := by
    have ha : gramCharges (GramAssembly.key 2315).leftCharge (GramAssembly.key 2315).rightCharge = raw41942 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41942Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41942 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2315).leftCharge (GramAssembly.key 2315).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4335) := by
    have ha : gramCharges (GramAssembly.key 2315).leftCharge (GramAssembly.key 2315).rightCharge = raw41943 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41943Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41943 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2315).leftCharge (GramAssembly.key 2315).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2315).leftCharge (GramAssembly.key 2315).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2315, Integer.Sparse.eval] <;> ring

theorem keyMoment2316 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2316) =
      Integer.Sparse.eval keyMomentRow2316 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2316).leftCharge (GramAssembly.key 2316).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1529) := by
    have ha : gramCharges (GramAssembly.key 2316).leftCharge (GramAssembly.key 2316).rightCharge = raw41944 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41944Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41944 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2316).leftCharge (GramAssembly.key 2316).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4162) := by
    have ha : gramCharges (GramAssembly.key 2316).leftCharge (GramAssembly.key 2316).rightCharge = raw41945 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41945Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41945 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2316).leftCharge (GramAssembly.key 2316).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2316).leftCharge (GramAssembly.key 2316).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2316, Integer.Sparse.eval] <;> ring

theorem keyMoment2317 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2317) =
      Integer.Sparse.eval keyMomentRow2317 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2317).leftCharge (GramAssembly.key 2317).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1528) := by
    have ha : gramCharges (GramAssembly.key 2317).leftCharge (GramAssembly.key 2317).rightCharge = raw41946 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41946Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41946 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2317).leftCharge (GramAssembly.key 2317).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4157) := by
    have ha : gramCharges (GramAssembly.key 2317).leftCharge (GramAssembly.key 2317).rightCharge = raw41947 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41947Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41947 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2317).leftCharge (GramAssembly.key 2317).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2317).leftCharge (GramAssembly.key 2317).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2317, Integer.Sparse.eval] <;> ring

theorem keyMoment2318 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2318) =
      Integer.Sparse.eval keyMomentRow2318 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2318).leftCharge (GramAssembly.key 2318).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1511) := by
    have ha : gramCharges (GramAssembly.key 2318).leftCharge (GramAssembly.key 2318).rightCharge = raw41948 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41948Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41948 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2318).leftCharge (GramAssembly.key 2318).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4154) := by
    have ha : gramCharges (GramAssembly.key 2318).leftCharge (GramAssembly.key 2318).rightCharge = raw41949 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41949Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41949 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2318).leftCharge (GramAssembly.key 2318).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2318).leftCharge (GramAssembly.key 2318).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2318, Integer.Sparse.eval] <;> ring

theorem keyMoment2319 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2319) =
      Integer.Sparse.eval keyMomentRow2319 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2319).leftCharge (GramAssembly.key 2319).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1510) := by
    have ha : gramCharges (GramAssembly.key 2319).leftCharge (GramAssembly.key 2319).rightCharge = raw41950 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41950Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41950 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2319).leftCharge (GramAssembly.key 2319).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4152) := by
    have ha : gramCharges (GramAssembly.key 2319).leftCharge (GramAssembly.key 2319).rightCharge = raw41951 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41951Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41951 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2319).leftCharge (GramAssembly.key 2319).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2319).leftCharge (GramAssembly.key 2319).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2319, Integer.Sparse.eval] <;> ring

theorem keyMoment2320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2320) =
      Integer.Sparse.eval keyMomentRow2320 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2320).leftCharge (GramAssembly.key 2320).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1523) := by
    have ha : gramCharges (GramAssembly.key 2320).leftCharge (GramAssembly.key 2320).rightCharge = raw41952 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41952Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41952 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2320).leftCharge (GramAssembly.key 2320).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4160) := by
    have ha : gramCharges (GramAssembly.key 2320).leftCharge (GramAssembly.key 2320).rightCharge = raw41953 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41953Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41953 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2320).leftCharge (GramAssembly.key 2320).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2320).leftCharge (GramAssembly.key 2320).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2320, Integer.Sparse.eval] <;> ring

theorem keyMoment2321 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2321) =
      Integer.Sparse.eval keyMomentRow2321 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2321).leftCharge (GramAssembly.key 2321).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1522) := by
    have ha : gramCharges (GramAssembly.key 2321).leftCharge (GramAssembly.key 2321).rightCharge = raw41954 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41954Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41954 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2321).leftCharge (GramAssembly.key 2321).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4158) := by
    have ha : gramCharges (GramAssembly.key 2321).leftCharge (GramAssembly.key 2321).rightCharge = raw41955 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41955Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41955 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2321).leftCharge (GramAssembly.key 2321).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2321).leftCharge (GramAssembly.key 2321).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2321, Integer.Sparse.eval] <;> ring

theorem keyMoment2322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2322) =
      Integer.Sparse.eval keyMomentRow2322 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2322).leftCharge (GramAssembly.key 2322).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1501) := by
    have ha : gramCharges (GramAssembly.key 2322).leftCharge (GramAssembly.key 2322).rightCharge = raw41956 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41956Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41956 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2322).leftCharge (GramAssembly.key 2322).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4149) := by
    have ha : gramCharges (GramAssembly.key 2322).leftCharge (GramAssembly.key 2322).rightCharge = raw41957 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41957Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41957 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2322).leftCharge (GramAssembly.key 2322).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2322).leftCharge (GramAssembly.key 2322).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2322, Integer.Sparse.eval] <;> ring

theorem keyMoment2323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2323) =
      Integer.Sparse.eval keyMomentRow2323 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2323).leftCharge (GramAssembly.key 2323).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1505) := by
    have ha : gramCharges (GramAssembly.key 2323).leftCharge (GramAssembly.key 2323).rightCharge = raw41958 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41958Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41958 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2323).leftCharge (GramAssembly.key 2323).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4151) := by
    have ha : gramCharges (GramAssembly.key 2323).leftCharge (GramAssembly.key 2323).rightCharge = raw41959 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41959Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41959 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2323).leftCharge (GramAssembly.key 2323).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2323).leftCharge (GramAssembly.key 2323).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2323, Integer.Sparse.eval] <;> ring

theorem keyMoment2324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2324) =
      Integer.Sparse.eval keyMomentRow2324 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2324).leftCharge (GramAssembly.key 2324).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1504) := by
    have ha : gramCharges (GramAssembly.key 2324).leftCharge (GramAssembly.key 2324).rightCharge = raw41960 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41960Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41960 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2324).leftCharge (GramAssembly.key 2324).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4150) := by
    have ha : gramCharges (GramAssembly.key 2324).leftCharge (GramAssembly.key 2324).rightCharge = raw41961 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41961Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41961 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2324).leftCharge (GramAssembly.key 2324).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2324).leftCharge (GramAssembly.key 2324).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2324, Integer.Sparse.eval] <;> ring

theorem keyMoment2325 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2325) =
      Integer.Sparse.eval keyMomentRow2325 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2325).leftCharge (GramAssembly.key 2325).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1516) := by
    have ha : gramCharges (GramAssembly.key 2325).leftCharge (GramAssembly.key 2325).rightCharge = raw41962 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41962Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41962 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2325).leftCharge (GramAssembly.key 2325).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4156) := by
    have ha : gramCharges (GramAssembly.key 2325).leftCharge (GramAssembly.key 2325).rightCharge = raw41963 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41963Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41963 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2325).leftCharge (GramAssembly.key 2325).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2325).leftCharge (GramAssembly.key 2325).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2325, Integer.Sparse.eval] <;> ring

theorem keyMoment2326 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2326) =
      Integer.Sparse.eval keyMomentRow2326 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2326).leftCharge (GramAssembly.key 2326).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1514) := by
    have ha : gramCharges (GramAssembly.key 2326).leftCharge (GramAssembly.key 2326).rightCharge = raw41964 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41964Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41964 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2326).leftCharge (GramAssembly.key 2326).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4153) := by
    have ha : gramCharges (GramAssembly.key 2326).leftCharge (GramAssembly.key 2326).rightCharge = raw41965 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41965Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41965 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2326).leftCharge (GramAssembly.key 2326).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2326).leftCharge (GramAssembly.key 2326).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2326, Integer.Sparse.eval] <;> ring

theorem keyMoment2327 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2327) =
      Integer.Sparse.eval keyMomentRow2327 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2327).leftCharge (GramAssembly.key 2327).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1515) := by
    have ha : gramCharges (GramAssembly.key 2327).leftCharge (GramAssembly.key 2327).rightCharge = raw41966 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41966Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41966 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2327).leftCharge (GramAssembly.key 2327).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4155) := by
    have ha : gramCharges (GramAssembly.key 2327).leftCharge (GramAssembly.key 2327).rightCharge = raw41967 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41967Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41967 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2327).leftCharge (GramAssembly.key 2327).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2327).leftCharge (GramAssembly.key 2327).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2327, Integer.Sparse.eval] <;> ring

theorem keyMoment2328 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2328) =
      Integer.Sparse.eval keyMomentRow2328 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2328).leftCharge (GramAssembly.key 2328).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1534) := by
    have ha : gramCharges (GramAssembly.key 2328).leftCharge (GramAssembly.key 2328).rightCharge = raw41968 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41968Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41968 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2328).leftCharge (GramAssembly.key 2328).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4163) := by
    have ha : gramCharges (GramAssembly.key 2328).leftCharge (GramAssembly.key 2328).rightCharge = raw41969 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41969Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41969 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2328).leftCharge (GramAssembly.key 2328).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2328).leftCharge (GramAssembly.key 2328).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2328, Integer.Sparse.eval] <;> ring

theorem keyMoment2329 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2329) =
      Integer.Sparse.eval keyMomentRow2329 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2329).leftCharge (GramAssembly.key 2329).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1532) := by
    have ha : gramCharges (GramAssembly.key 2329).leftCharge (GramAssembly.key 2329).rightCharge = raw41970 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41970Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41970 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2329).leftCharge (GramAssembly.key 2329).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4159) := by
    have ha : gramCharges (GramAssembly.key 2329).leftCharge (GramAssembly.key 2329).rightCharge = raw41971 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41971Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41971 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2329).leftCharge (GramAssembly.key 2329).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2329).leftCharge (GramAssembly.key 2329).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2329, Integer.Sparse.eval] <;> ring

theorem keyMoment2330 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2330) =
      Integer.Sparse.eval keyMomentRow2330 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2330).leftCharge (GramAssembly.key 2330).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1533) := by
    have ha : gramCharges (GramAssembly.key 2330).leftCharge (GramAssembly.key 2330).rightCharge = raw41972 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41972Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41972 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2330).leftCharge (GramAssembly.key 2330).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4161) := by
    have ha : gramCharges (GramAssembly.key 2330).leftCharge (GramAssembly.key 2330).rightCharge = raw41973 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41973Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41973 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2330).leftCharge (GramAssembly.key 2330).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2330).leftCharge (GramAssembly.key 2330).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2330, Integer.Sparse.eval] <;> ring

theorem keyMoment2331 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2331) =
      Integer.Sparse.eval keyMomentRow2331 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2331).leftCharge (GramAssembly.key 2331).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3114) := by
    have ha : gramCharges (GramAssembly.key 2331).leftCharge (GramAssembly.key 2331).rightCharge = raw41974 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41974Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41974 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2331).leftCharge (GramAssembly.key 2331).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4897) := by
    have ha : gramCharges (GramAssembly.key 2331).leftCharge (GramAssembly.key 2331).rightCharge = raw41975 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41975Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41975 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2331).leftCharge (GramAssembly.key 2331).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2331).leftCharge (GramAssembly.key 2331).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2331, Integer.Sparse.eval] <;> ring

theorem keyMoment2332 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2332) =
      Integer.Sparse.eval keyMomentRow2332 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2332).leftCharge (GramAssembly.key 2332).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3112) := by
    have ha : gramCharges (GramAssembly.key 2332).leftCharge (GramAssembly.key 2332).rightCharge = raw41976 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41976Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41976 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2332).leftCharge (GramAssembly.key 2332).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5274) := by
    have ha : gramCharges (GramAssembly.key 2332).leftCharge (GramAssembly.key 2332).rightCharge = raw41977 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41977Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41977 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2332).leftCharge (GramAssembly.key 2332).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2332).leftCharge (GramAssembly.key 2332).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2332, Integer.Sparse.eval] <;> ring

theorem keyMoment2333 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2333) =
      Integer.Sparse.eval keyMomentRow2333 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2333).leftCharge (GramAssembly.key 2333).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3110) := by
    have ha : gramCharges (GramAssembly.key 2333).leftCharge (GramAssembly.key 2333).rightCharge = raw41978 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41978Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41978 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2333).leftCharge (GramAssembly.key 2333).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5275) := by
    have ha : gramCharges (GramAssembly.key 2333).leftCharge (GramAssembly.key 2333).rightCharge = raw41979 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41979Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41979 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2333).leftCharge (GramAssembly.key 2333).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2333).leftCharge (GramAssembly.key 2333).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2333, Integer.Sparse.eval] <;> ring

theorem keyMoment2334 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2334) =
      Integer.Sparse.eval keyMomentRow2334 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2334).leftCharge (GramAssembly.key 2334).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2734) := by
    have ha : gramCharges (GramAssembly.key 2334).leftCharge (GramAssembly.key 2334).rightCharge = raw41980 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41980Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41980 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2334).leftCharge (GramAssembly.key 2334).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5268) := by
    have ha : gramCharges (GramAssembly.key 2334).leftCharge (GramAssembly.key 2334).rightCharge = raw41981 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41981Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41981 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2334).leftCharge (GramAssembly.key 2334).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2334).leftCharge (GramAssembly.key 2334).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2334, Integer.Sparse.eval] <;> ring

theorem keyMoment2335 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2335) =
      Integer.Sparse.eval keyMomentRow2335 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2335).leftCharge (GramAssembly.key 2335).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3089) := by
    have ha : gramCharges (GramAssembly.key 2335).leftCharge (GramAssembly.key 2335).rightCharge = raw41982 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41982Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41982 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2335).leftCharge (GramAssembly.key 2335).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5258) := by
    have ha : gramCharges (GramAssembly.key 2335).leftCharge (GramAssembly.key 2335).rightCharge = raw41983 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41983Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41983 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2335).leftCharge (GramAssembly.key 2335).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2335).leftCharge (GramAssembly.key 2335).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2335, Integer.Sparse.eval] <;> ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2304 : keyMomentRows (2304 : Fin 2886) =
    keyMomentRow2304 := by decide +kernel

theorem keyMomentRowsAt2305 : keyMomentRows (2305 : Fin 2886) =
    keyMomentRow2305 := by decide +kernel

theorem keyMomentRowsAt2306 : keyMomentRows (2306 : Fin 2886) =
    keyMomentRow2306 := by decide +kernel

theorem keyMomentRowsAt2307 : keyMomentRows (2307 : Fin 2886) =
    keyMomentRow2307 := by decide +kernel

theorem keyMomentRowsAt2308 : keyMomentRows (2308 : Fin 2886) =
    keyMomentRow2308 := by decide +kernel

theorem keyMomentRowsAt2309 : keyMomentRows (2309 : Fin 2886) =
    keyMomentRow2309 := by decide +kernel

theorem keyMomentRowsAt2310 : keyMomentRows (2310 : Fin 2886) =
    keyMomentRow2310 := by decide +kernel

theorem keyMomentRowsAt2311 : keyMomentRows (2311 : Fin 2886) =
    keyMomentRow2311 := by decide +kernel

theorem keyMomentRowsAt2312 : keyMomentRows (2312 : Fin 2886) =
    keyMomentRow2312 := by decide +kernel

theorem keyMomentRowsAt2313 : keyMomentRows (2313 : Fin 2886) =
    keyMomentRow2313 := by decide +kernel

theorem keyMomentRowsAt2314 : keyMomentRows (2314 : Fin 2886) =
    keyMomentRow2314 := by decide +kernel

theorem keyMomentRowsAt2315 : keyMomentRows (2315 : Fin 2886) =
    keyMomentRow2315 := by decide +kernel

theorem keyMomentRowsAt2316 : keyMomentRows (2316 : Fin 2886) =
    keyMomentRow2316 := by decide +kernel

theorem keyMomentRowsAt2317 : keyMomentRows (2317 : Fin 2886) =
    keyMomentRow2317 := by decide +kernel

theorem keyMomentRowsAt2318 : keyMomentRows (2318 : Fin 2886) =
    keyMomentRow2318 := by decide +kernel

theorem keyMomentRowsAt2319 : keyMomentRows (2319 : Fin 2886) =
    keyMomentRow2319 := by decide +kernel

theorem keyMomentRowsAt2320 : keyMomentRows (2320 : Fin 2886) =
    keyMomentRow2320 := by decide +kernel

theorem keyMomentRowsAt2321 : keyMomentRows (2321 : Fin 2886) =
    keyMomentRow2321 := by decide +kernel

theorem keyMomentRowsAt2322 : keyMomentRows (2322 : Fin 2886) =
    keyMomentRow2322 := by decide +kernel

theorem keyMomentRowsAt2323 : keyMomentRows (2323 : Fin 2886) =
    keyMomentRow2323 := by decide +kernel

theorem keyMomentRowsAt2324 : keyMomentRows (2324 : Fin 2886) =
    keyMomentRow2324 := by decide +kernel

theorem keyMomentRowsAt2325 : keyMomentRows (2325 : Fin 2886) =
    keyMomentRow2325 := by decide +kernel

theorem keyMomentRowsAt2326 : keyMomentRows (2326 : Fin 2886) =
    keyMomentRow2326 := by decide +kernel

theorem keyMomentRowsAt2327 : keyMomentRows (2327 : Fin 2886) =
    keyMomentRow2327 := by decide +kernel

theorem keyMomentRowsAt2328 : keyMomentRows (2328 : Fin 2886) =
    keyMomentRow2328 := by decide +kernel

theorem keyMomentRowsAt2329 : keyMomentRows (2329 : Fin 2886) =
    keyMomentRow2329 := by decide +kernel

theorem keyMomentRowsAt2330 : keyMomentRows (2330 : Fin 2886) =
    keyMomentRow2330 := by decide +kernel

theorem keyMomentRowsAt2331 : keyMomentRows (2331 : Fin 2886) =
    keyMomentRow2331 := by decide +kernel

theorem keyMomentRowsAt2332 : keyMomentRows (2332 : Fin 2886) =
    keyMomentRow2332 := by decide +kernel

theorem keyMomentRowsAt2333 : keyMomentRows (2333 : Fin 2886) =
    keyMomentRow2333 := by decide +kernel

theorem keyMomentRowsAt2334 : keyMomentRows (2334 : Fin 2886) =
    keyMomentRow2334 := by decide +kernel

theorem keyMomentRowsAt2335 : keyMomentRows (2335 : Fin 2886) =
    keyMomentRow2335 := by decide +kernel

theorem keyMomentChunkSound72_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 72) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2304 ∨ k.val = 2305 ∨ k.val = 2306 ∨ k.val = 2307 ∨ k.val = 2308 ∨ k.val = 2309 ∨ k.val = 2310 ∨ k.val = 2311 ∨ k.val = 2312 ∨ k.val = 2313 ∨ k.val = 2314 ∨ k.val = 2315 ∨ k.val = 2316 ∨ k.val = 2317 ∨ k.val = 2318 ∨ k.val = 2319 ∨ k.val = 2320 ∨ k.val = 2321 ∨ k.val = 2322 ∨ k.val = 2323 ∨ k.val = 2324 ∨ k.val = 2325 ∨ k.val = 2326 ∨ k.val = 2327 ∨ k.val = 2328 ∨ k.val = 2329 ∨ k.val = 2330 ∨ k.val = 2331 ∨ k.val = 2332 ∨ k.val = 2333 ∨ k.val = 2334 ∨ k.val = 2335 := by omega
  rcases heq with h2304 | h2305 | h2306 | h2307 | h2308 | h2309 | h2310 | h2311 | h2312 | h2313 | h2314 | h2315 | h2316 | h2317 | h2318 | h2319 | h2320 | h2321 | h2322 | h2323 | h2324 | h2325 | h2326 | h2327 | h2328 | h2329 | h2330 | h2331 | h2332 | h2333 | h2334 | h2335
  · have he : k = (2304 : Fin 2886) := Fin.ext h2304
    subst k
    rw [keyMomentRowsAt2304]
    exact keyMoment2304 B hB
  · have he : k = (2305 : Fin 2886) := Fin.ext h2305
    subst k
    rw [keyMomentRowsAt2305]
    exact keyMoment2305 B hB
  · have he : k = (2306 : Fin 2886) := Fin.ext h2306
    subst k
    rw [keyMomentRowsAt2306]
    exact keyMoment2306 B hB
  · have he : k = (2307 : Fin 2886) := Fin.ext h2307
    subst k
    rw [keyMomentRowsAt2307]
    exact keyMoment2307 B hB
  · have he : k = (2308 : Fin 2886) := Fin.ext h2308
    subst k
    rw [keyMomentRowsAt2308]
    exact keyMoment2308 B hB
  · have he : k = (2309 : Fin 2886) := Fin.ext h2309
    subst k
    rw [keyMomentRowsAt2309]
    exact keyMoment2309 B hB
  · have he : k = (2310 : Fin 2886) := Fin.ext h2310
    subst k
    rw [keyMomentRowsAt2310]
    exact keyMoment2310 B hB
  · have he : k = (2311 : Fin 2886) := Fin.ext h2311
    subst k
    rw [keyMomentRowsAt2311]
    exact keyMoment2311 B hB
  · have he : k = (2312 : Fin 2886) := Fin.ext h2312
    subst k
    rw [keyMomentRowsAt2312]
    exact keyMoment2312 B hB
  · have he : k = (2313 : Fin 2886) := Fin.ext h2313
    subst k
    rw [keyMomentRowsAt2313]
    exact keyMoment2313 B hB
  · have he : k = (2314 : Fin 2886) := Fin.ext h2314
    subst k
    rw [keyMomentRowsAt2314]
    exact keyMoment2314 B hB
  · have he : k = (2315 : Fin 2886) := Fin.ext h2315
    subst k
    rw [keyMomentRowsAt2315]
    exact keyMoment2315 B hB
  · have he : k = (2316 : Fin 2886) := Fin.ext h2316
    subst k
    rw [keyMomentRowsAt2316]
    exact keyMoment2316 B hB
  · have he : k = (2317 : Fin 2886) := Fin.ext h2317
    subst k
    rw [keyMomentRowsAt2317]
    exact keyMoment2317 B hB
  · have he : k = (2318 : Fin 2886) := Fin.ext h2318
    subst k
    rw [keyMomentRowsAt2318]
    exact keyMoment2318 B hB
  · have he : k = (2319 : Fin 2886) := Fin.ext h2319
    subst k
    rw [keyMomentRowsAt2319]
    exact keyMoment2319 B hB
  · have he : k = (2320 : Fin 2886) := Fin.ext h2320
    subst k
    rw [keyMomentRowsAt2320]
    exact keyMoment2320 B hB
  · have he : k = (2321 : Fin 2886) := Fin.ext h2321
    subst k
    rw [keyMomentRowsAt2321]
    exact keyMoment2321 B hB
  · have he : k = (2322 : Fin 2886) := Fin.ext h2322
    subst k
    rw [keyMomentRowsAt2322]
    exact keyMoment2322 B hB
  · have he : k = (2323 : Fin 2886) := Fin.ext h2323
    subst k
    rw [keyMomentRowsAt2323]
    exact keyMoment2323 B hB
  · have he : k = (2324 : Fin 2886) := Fin.ext h2324
    subst k
    rw [keyMomentRowsAt2324]
    exact keyMoment2324 B hB
  · have he : k = (2325 : Fin 2886) := Fin.ext h2325
    subst k
    rw [keyMomentRowsAt2325]
    exact keyMoment2325 B hB
  · have he : k = (2326 : Fin 2886) := Fin.ext h2326
    subst k
    rw [keyMomentRowsAt2326]
    exact keyMoment2326 B hB
  · have he : k = (2327 : Fin 2886) := Fin.ext h2327
    subst k
    rw [keyMomentRowsAt2327]
    exact keyMoment2327 B hB
  · have he : k = (2328 : Fin 2886) := Fin.ext h2328
    subst k
    rw [keyMomentRowsAt2328]
    exact keyMoment2328 B hB
  · have he : k = (2329 : Fin 2886) := Fin.ext h2329
    subst k
    rw [keyMomentRowsAt2329]
    exact keyMoment2329 B hB
  · have he : k = (2330 : Fin 2886) := Fin.ext h2330
    subst k
    rw [keyMomentRowsAt2330]
    exact keyMoment2330 B hB
  · have he : k = (2331 : Fin 2886) := Fin.ext h2331
    subst k
    rw [keyMomentRowsAt2331]
    exact keyMoment2331 B hB
  · have he : k = (2332 : Fin 2886) := Fin.ext h2332
    subst k
    rw [keyMomentRowsAt2332]
    exact keyMoment2332 B hB
  · have he : k = (2333 : Fin 2886) := Fin.ext h2333
    subst k
    rw [keyMomentRowsAt2333]
    exact keyMoment2333 B hB
  · have he : k = (2334 : Fin 2886) := Fin.ext h2334
    subst k
    rw [keyMomentRowsAt2334]
    exact keyMoment2334 B hB
  · have he : k = (2335 : Fin 2886) := Fin.ext h2335
    subst k
    rw [keyMomentRowsAt2335]
    exact keyMoment2335 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound72_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound72_e_oai
