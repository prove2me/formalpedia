-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound87_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:06:28.959898+00:00
-- url     : https://prove2.me/submissions/d4eb0b6b-79a3-4bc0-88f9-c92db325fc12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E114
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical335
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical42880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42880 raw42880Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw42880 raw42880Labels = mixedMoment B raw42880step0 raw42880step0Labels := by
      have ha : raw42880step0 = (fun i j => raw42880 (permutation251 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42880step0 raw42880; decide +kernel
      have hl : raw42880step0Labels = raw42880Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42880 raw42880Labels permutation251 permutation4
    mixedMoment B raw42880step0 raw42880step0Labels = mixedMoment B raw42880step1 raw42880step1Labels := by
      have ha : raw42880step1 = -raw42880step0 := by apply Matrix.ext; change ∀ i j, raw42880step1 i j = -(raw42880step0 i j); unfold raw42880step1 raw42880step0; decide +kernel
      have hl : raw42880step1Labels = raw42880step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42880step1 raw42880step1Labels = mixedMoment B raw42880step2 raw42880step2Labels := by
      have ha : raw42880step2 = raw42880step1 := by apply Matrix.ext; unfold raw42880step2 raw42880step1; decide +kernel
      have hl : raw42880step1Labels = labelEmbedding1 ∘ raw42880step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42880step1 raw42880step1Labels raw42880step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical42881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42881 raw42881Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw42881 raw42881Labels = mixedMoment B raw42881step0 raw42881step0Labels := by
      have ha : raw42881step0 = (fun i j => raw42881 (permutation251 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42881step0 raw42881; decide +kernel
      have hl : raw42881step0Labels = raw42881Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42881 raw42881Labels permutation251 permutation4
    mixedMoment B raw42881step0 raw42881step0Labels = mixedMoment B raw42881step1 raw42881step1Labels := by
      have ha : raw42881step1 = -raw42881step0 := by apply Matrix.ext; change ∀ i j, raw42881step1 i j = -(raw42881step0 i j); unfold raw42881step1 raw42881step0; decide +kernel
      have hl : raw42881step1Labels = raw42881step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42881step1 raw42881step1Labels = mixedMoment B raw42881step2 raw42881step2Labels := by
      have ha : raw42881step2 = raw42881step1 := by apply Matrix.ext; unfold raw42881step2 raw42881step1; decide +kernel
      have hl : raw42881step1Labels = labelEmbedding10 ∘ raw42881step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42881step1 raw42881step1Labels raw42881step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical42882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42882 raw42882Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw42882 raw42882Labels = mixedMoment B raw42882step0 raw42882step0Labels := by
      have hz : ∀ j, raw42882 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42882step0 = (fun i j => raw42882 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42882step0 raw42882; decide +kernel
      have hl : raw42882step0Labels = raw42882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42882 raw42882Labels permutation434 hz
    mixedMoment B raw42882step0 raw42882step0Labels = mixedMoment B raw42882step1 raw42882step1Labels := by
      have ha : raw42882step1 = (fun i j => raw42882step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42882step1 raw42882step0; decide +kernel
      have hl : raw42882step1Labels = raw42882step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42882step0 raw42882step0Labels permutation51 permutation4
    mixedMoment B raw42882step1 raw42882step1Labels = mixedMoment B raw42882step2 raw42882step2Labels := by
      have ha : raw42882step2 = -raw42882step1 := by apply Matrix.ext; change ∀ i j, raw42882step2 i j = -(raw42882step1 i j); unfold raw42882step2 raw42882step1; decide +kernel
      have hl : raw42882step2Labels = raw42882step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42882step2 raw42882step2Labels = mixedMoment B raw42882step3 raw42882step3Labels := by
      have ha : raw42882step3 = raw42882step2 := by apply Matrix.ext; unfold raw42882step3 raw42882step2; decide +kernel
      have hl : raw42882step2Labels = labelEmbedding1 ∘ raw42882step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42882step2 raw42882step2Labels raw42882step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

theorem canonical42883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42883 raw42883Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw42883 raw42883Labels = mixedMoment B raw42883step0 raw42883step0Labels := by
      have hz : ∀ j, raw42883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42883step0 = (fun i j => raw42883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42883step0 raw42883; decide +kernel
      have hl : raw42883step0Labels = raw42883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42883 raw42883Labels permutation434 hz
    mixedMoment B raw42883step0 raw42883step0Labels = mixedMoment B raw42883step1 raw42883step1Labels := by
      have ha : raw42883step1 = (fun i j => raw42883step0 (permutation89 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42883step1 raw42883step0; decide +kernel
      have hl : raw42883step1Labels = raw42883step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42883step0 raw42883step0Labels permutation89 permutation6
    mixedMoment B raw42883step1 raw42883step1Labels = mixedMoment B raw42883step2 raw42883step2Labels := by
      have ha : raw42883step2 = -raw42883step1 := by apply Matrix.ext; change ∀ i j, raw42883step2 i j = -(raw42883step1 i j); unfold raw42883step2 raw42883step1; decide +kernel
      have hl : raw42883step2Labels = raw42883step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5140 node5140Labels := by rfl

theorem canonical42884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42884 raw42884Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw42884 raw42884Labels = mixedMoment B raw42884step0 raw42884step0Labels := by
      have hz : ∀ j, raw42884 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42884step0 = (fun i j => raw42884 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42884step0 raw42884; decide +kernel
      have hl : raw42884step0Labels = raw42884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42884 raw42884Labels permutation434 hz
    mixedMoment B raw42884step0 raw42884step0Labels = mixedMoment B raw42884step1 raw42884step1Labels := by
      have ha : raw42884step1 = (fun i j => raw42884step0 (permutation54 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42884step1 raw42884step0; decide +kernel
      have hl : raw42884step1Labels = raw42884step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42884step0 raw42884step0Labels permutation54 permutation4
    mixedMoment B raw42884step1 raw42884step1Labels = mixedMoment B raw42884step2 raw42884step2Labels := by
      have ha : raw42884step2 = -raw42884step1 := by apply Matrix.ext; change ∀ i j, raw42884step2 i j = -(raw42884step1 i j); unfold raw42884step2 raw42884step1; decide +kernel
      have hl : raw42884step2Labels = raw42884step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42884step2 raw42884step2Labels = mixedMoment B raw42884step3 raw42884step3Labels := by
      have ha : raw42884step3 = raw42884step2 := by apply Matrix.ext; unfold raw42884step3 raw42884step2; decide +kernel
      have hl : raw42884step2Labels = labelEmbedding1 ∘ raw42884step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42884step2 raw42884step2Labels raw42884step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2682 node2682Labels := by rfl

theorem canonical42885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42885 raw42885Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw42885 raw42885Labels = mixedMoment B raw42885step0 raw42885step0Labels := by
      have hz : ∀ j, raw42885 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42885step0 = (fun i j => raw42885 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42885step0 raw42885; decide +kernel
      have hl : raw42885step0Labels = raw42885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42885 raw42885Labels permutation434 hz
    mixedMoment B raw42885step0 raw42885step0Labels = mixedMoment B raw42885step1 raw42885step1Labels := by
      have ha : raw42885step1 = (fun i j => raw42885step0 (permutation54 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42885step1 raw42885step0; decide +kernel
      have hl : raw42885step1Labels = raw42885step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42885step0 raw42885step0Labels permutation54 permutation4
    mixedMoment B raw42885step1 raw42885step1Labels = mixedMoment B raw42885step2 raw42885step2Labels := by
      have ha : raw42885step2 = -raw42885step1 := by apply Matrix.ext; change ∀ i j, raw42885step2 i j = -(raw42885step1 i j); unfold raw42885step2 raw42885step1; decide +kernel
      have hl : raw42885step2Labels = raw42885step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42885step2 raw42885step2Labels = mixedMoment B raw42885step3 raw42885step3Labels := by
      have ha : raw42885step3 = raw42885step2 := by apply Matrix.ext; unfold raw42885step3 raw42885step2; decide +kernel
      have hl : raw42885step2Labels = labelEmbedding10 ∘ raw42885step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42885step2 raw42885step2Labels raw42885step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

theorem canonical42886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42886 raw42886Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw42886 raw42886Labels = mixedMoment B raw42886step0 raw42886step0Labels := by
      have hz : ∀ j, raw42886 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42886step0 = (fun i j => raw42886 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42886step0 raw42886; decide +kernel
      have hl : raw42886step0Labels = raw42886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42886 raw42886Labels permutation520 hz
    mixedMoment B raw42886step0 raw42886step0Labels = mixedMoment B raw42886step1 raw42886step1Labels := by
      have hz : ∀ j, raw42886step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42886step1 = (fun i j => raw42886step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42886step1 raw42886step0; decide +kernel
      have hl : raw42886step1Labels = raw42886step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42886step0 raw42886step0Labels permutation104 hz
    mixedMoment B raw42886step1 raw42886step1Labels = mixedMoment B raw42886step2 raw42886step2Labels := by
      have ha : raw42886step2 = (fun i j => raw42886step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42886step2 raw42886step1; decide +kernel
      have hl : raw42886step2Labels = raw42886step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42886step1 raw42886step1Labels permutation31 permutation4
    mixedMoment B raw42886step2 raw42886step2Labels = mixedMoment B raw42886step3 raw42886step3Labels := by
      have ha : raw42886step3 = raw42886step2 := by apply Matrix.ext; unfold raw42886step3 raw42886step2; decide +kernel
      have hl : raw42886step2Labels = labelEmbedding1 ∘ raw42886step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42886step2 raw42886step2Labels raw42886step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3229 node3229Labels := by rfl

theorem canonical42887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42887 raw42887Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw42887 raw42887Labels = mixedMoment B raw42887step0 raw42887step0Labels := by
      have hz : ∀ j, raw42887 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42887step0 = (fun i j => raw42887 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42887step0 raw42887; decide +kernel
      have hl : raw42887step0Labels = raw42887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42887 raw42887Labels permutation520 hz
    mixedMoment B raw42887step0 raw42887step0Labels = mixedMoment B raw42887step1 raw42887step1Labels := by
      have hz : ∀ j, raw42887step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42887step1 = (fun i j => raw42887step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42887step1 raw42887step0; decide +kernel
      have hl : raw42887step1Labels = raw42887step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42887step0 raw42887step0Labels permutation104 hz
    mixedMoment B raw42887step1 raw42887step1Labels = mixedMoment B raw42887step2 raw42887step2Labels := by
      have ha : raw42887step2 = (fun i j => raw42887step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42887step2 raw42887step1; decide +kernel
      have hl : raw42887step2Labels = raw42887step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42887step1 raw42887step1Labels permutation31 permutation5
    mixedMoment B raw42887step2 raw42887step2Labels = mixedMoment B raw42887step3 raw42887step3Labels := by
      have ha : raw42887step3 = raw42887step2 := by apply Matrix.ext; unfold raw42887step3 raw42887step2; decide +kernel
      have hl : raw42887step2Labels = labelEmbedding9 ∘ raw42887step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42887step2 raw42887step2Labels raw42887step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical42888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42888 raw42888Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw42888 raw42888Labels = mixedMoment B raw42888step0 raw42888step0Labels := by
      have hz : ∀ j, raw42888 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42888step0 = (fun i j => raw42888 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42888step0 raw42888; decide +kernel
      have hl : raw42888step0Labels = raw42888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42888 raw42888Labels permutation434 hz
    mixedMoment B raw42888step0 raw42888step0Labels = mixedMoment B raw42888step1 raw42888step1Labels := by
      have ha : raw42888step1 = (fun i j => raw42888step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42888step1 raw42888step0; decide +kernel
      have hl : raw42888step1Labels = raw42888step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42888step0 raw42888step0Labels permutation145 permutation4
    mixedMoment B raw42888step1 raw42888step1Labels = mixedMoment B raw42888step2 raw42888step2Labels := by
      have ha : raw42888step2 = raw42888step1 := by apply Matrix.ext; unfold raw42888step2 raw42888step1; decide +kernel
      have hl : raw42888step1Labels = labelEmbedding1 ∘ raw42888step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42888step1 raw42888step1Labels raw42888step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3088 node3088Labels := by rfl

theorem canonical42889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42889 raw42889Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw42889 raw42889Labels = mixedMoment B raw42889step0 raw42889step0Labels := by
      have hz : ∀ j, raw42889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42889step0 = (fun i j => raw42889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42889step0 raw42889; decide +kernel
      have hl : raw42889step0Labels = raw42889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42889 raw42889Labels permutation434 hz
    mixedMoment B raw42889step0 raw42889step0Labels = mixedMoment B raw42889step1 raw42889step1Labels := by
      have ha : raw42889step1 = (fun i j => raw42889step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42889step1 raw42889step0; decide +kernel
      have hl : raw42889step1Labels = raw42889step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42889step0 raw42889step0Labels permutation151 permutation5
    mixedMoment B raw42889step1 raw42889step1Labels = mixedMoment B raw42889step2 raw42889step2Labels := by
      have ha : raw42889step2 = raw42889step1 := by apply Matrix.ext; unfold raw42889step2 raw42889step1; decide +kernel
      have hl : raw42889step1Labels = labelEmbedding9 ∘ raw42889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42889step1 raw42889step1Labels raw42889step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical42890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42890 raw42890Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw42890 raw42890Labels = mixedMoment B raw42890step0 raw42890step0Labels := by
      have hz : ∀ j, raw42890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42890step0 = (fun i j => raw42890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42890step0 raw42890; decide +kernel
      have hl : raw42890step0Labels = raw42890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42890 raw42890Labels permutation434 hz
    mixedMoment B raw42890step0 raw42890step0Labels = mixedMoment B raw42890step1 raw42890step1Labels := by
      have ha : raw42890step1 = (fun i j => raw42890step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42890step1 raw42890step0; decide +kernel
      have hl : raw42890step1Labels = raw42890step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42890step0 raw42890step0Labels permutation32 permutation4
    mixedMoment B raw42890step1 raw42890step1Labels = mixedMoment B raw42890step2 raw42890step2Labels := by
      have ha : raw42890step2 = -raw42890step1 := by apply Matrix.ext; change ∀ i j, raw42890step2 i j = -(raw42890step1 i j); unfold raw42890step2 raw42890step1; decide +kernel
      have hl : raw42890step2Labels = raw42890step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42890step2 raw42890step2Labels = mixedMoment B raw42890step3 raw42890step3Labels := by
      have ha : raw42890step3 = raw42890step2 := by apply Matrix.ext; unfold raw42890step3 raw42890step2; decide +kernel
      have hl : raw42890step2Labels = labelEmbedding1 ∘ raw42890step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42890step2 raw42890step2Labels raw42890step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3996 node3996Labels := by rfl

theorem canonical42891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42891 raw42891Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw42891 raw42891Labels = mixedMoment B raw42891step0 raw42891step0Labels := by
      have hz : ∀ j, raw42891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42891step0 = (fun i j => raw42891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42891step0 raw42891; decide +kernel
      have hl : raw42891step0Labels = raw42891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42891 raw42891Labels permutation434 hz
    mixedMoment B raw42891step0 raw42891step0Labels = mixedMoment B raw42891step1 raw42891step1Labels := by
      have ha : raw42891step1 = (fun i j => raw42891step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42891step1 raw42891step0; decide +kernel
      have hl : raw42891step1Labels = raw42891step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42891step0 raw42891step0Labels permutation151 permutation5
    mixedMoment B raw42891step1 raw42891step1Labels = mixedMoment B raw42891step2 raw42891step2Labels := by
      have ha : raw42891step2 = raw42891step1 := by apply Matrix.ext; unfold raw42891step2 raw42891step1; decide +kernel
      have hl : raw42891step1Labels = labelEmbedding9 ∘ raw42891step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42891step1 raw42891step1Labels raw42891step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical42892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42892 raw42892Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw42892 raw42892Labels = mixedMoment B raw42892step0 raw42892step0Labels := by
      have hz : ∀ j, raw42892 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42892step0 = (fun i j => raw42892 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42892step0 raw42892; decide +kernel
      have hl : raw42892step0Labels = raw42892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42892 raw42892Labels permutation434 hz
    mixedMoment B raw42892step0 raw42892step0Labels = mixedMoment B raw42892step1 raw42892step1Labels := by
      have ha : raw42892step1 = (fun i j => raw42892step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42892step1 raw42892step0; decide +kernel
      have hl : raw42892step1Labels = raw42892step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42892step0 raw42892step0Labels permutation33 permutation4
    mixedMoment B raw42892step1 raw42892step1Labels = mixedMoment B raw42892step2 raw42892step2Labels := by
      have ha : raw42892step2 = -raw42892step1 := by apply Matrix.ext; change ∀ i j, raw42892step2 i j = -(raw42892step1 i j); unfold raw42892step2 raw42892step1; decide +kernel
      have hl : raw42892step2Labels = raw42892step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42892step2 raw42892step2Labels = mixedMoment B raw42892step3 raw42892step3Labels := by
      have ha : raw42892step3 = raw42892step2 := by apply Matrix.ext; unfold raw42892step3 raw42892step2; decide +kernel
      have hl : raw42892step2Labels = labelEmbedding1 ∘ raw42892step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42892step2 raw42892step2Labels raw42892step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3995 node3995Labels := by rfl

theorem canonical42893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42893 raw42893Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw42893 raw42893Labels = mixedMoment B raw42893step0 raw42893step0Labels := by
      have hz : ∀ j, raw42893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42893step0 = (fun i j => raw42893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42893step0 raw42893; decide +kernel
      have hl : raw42893step0Labels = raw42893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42893 raw42893Labels permutation434 hz
    mixedMoment B raw42893step0 raw42893step0Labels = mixedMoment B raw42893step1 raw42893step1Labels := by
      have ha : raw42893step1 = (fun i j => raw42893step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42893step1 raw42893step0; decide +kernel
      have hl : raw42893step1Labels = raw42893step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42893step0 raw42893step0Labels permutation127 permutation5
    mixedMoment B raw42893step1 raw42893step1Labels = mixedMoment B raw42893step2 raw42893step2Labels := by
      have ha : raw42893step2 = raw42893step1 := by apply Matrix.ext; unfold raw42893step2 raw42893step1; decide +kernel
      have hl : raw42893step1Labels = labelEmbedding9 ∘ raw42893step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42893step1 raw42893step1Labels raw42893step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical42894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42894 raw42894Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw42894 raw42894Labels = mixedMoment B raw42894step0 raw42894step0Labels := by
      have ha : raw42894step0 = (fun i j => raw42894 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42894step0 raw42894; decide +kernel
      have hl : raw42894step0Labels = raw42894Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42894 raw42894Labels permutation164 permutation4
    mixedMoment B raw42894step0 raw42894step0Labels = mixedMoment B raw42894step1 raw42894step1Labels := by
      have ha : raw42894step1 = -raw42894step0 := by apply Matrix.ext; change ∀ i j, raw42894step1 i j = -(raw42894step0 i j); unfold raw42894step1 raw42894step0; decide +kernel
      have hl : raw42894step1Labels = raw42894step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42894step1 raw42894step1Labels = mixedMoment B raw42894step2 raw42894step2Labels := by
      have ha : raw42894step2 = raw42894step1 := by apply Matrix.ext; unfold raw42894step2 raw42894step1; decide +kernel
      have hl : raw42894step1Labels = labelEmbedding1 ∘ raw42894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42894step1 raw42894step1Labels raw42894step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3990 node3990Labels := by rfl

theorem canonical42895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42895 raw42895Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw42895 raw42895Labels = mixedMoment B raw42895step0 raw42895step0Labels := by
      have ha : raw42895step0 = (fun i j => raw42895 (permutation664 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42895step0 raw42895; decide +kernel
      have hl : raw42895step0Labels = raw42895Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42895 raw42895Labels permutation664 permutation5
    mixedMoment B raw42895step0 raw42895step0Labels = mixedMoment B raw42895step1 raw42895step1Labels := by
      have ha : raw42895step1 = raw42895step0 := by apply Matrix.ext; unfold raw42895step1 raw42895step0; decide +kernel
      have hl : raw42895step0Labels = labelEmbedding9 ∘ raw42895step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42895step0 raw42895step0Labels raw42895step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical42896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42896 raw42896Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw42896 raw42896Labels = mixedMoment B raw42896step0 raw42896step0Labels := by
      have ha : raw42896step0 = (fun i j => raw42896 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42896step0 raw42896; decide +kernel
      have hl : raw42896step0Labels = raw42896Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42896 raw42896Labels permutation683 permutation2
    mixedMoment B raw42896step0 raw42896step0Labels = mixedMoment B raw42896step1 raw42896step1Labels := by
      have ha : raw42896step1 = -raw42896step0 := by apply Matrix.ext; change ∀ i j, raw42896step1 i j = -(raw42896step0 i j); unfold raw42896step1 raw42896step0; decide +kernel
      have hl : raw42896step1Labels = raw42896step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42896step1 raw42896step1Labels = mixedMoment B raw42896step2 raw42896step2Labels := by
      have ha : raw42896step2 = raw42896step1 := by apply Matrix.ext; unfold raw42896step2 raw42896step1; decide +kernel
      have hl : raw42896step1Labels = labelEmbedding1 ∘ raw42896step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42896step1 raw42896step1Labels raw42896step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3994 node3994Labels := by rfl

theorem canonical42897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42897 raw42897Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw42897 raw42897Labels = mixedMoment B raw42897step0 raw42897step0Labels := by
      have ha : raw42897step0 = (fun i j => raw42897 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42897step0 raw42897; decide +kernel
      have hl : raw42897step0Labels = raw42897Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42897 raw42897Labels permutation688 permutation3
    mixedMoment B raw42897step0 raw42897step0Labels = mixedMoment B raw42897step1 raw42897step1Labels := by
      have ha : raw42897step1 = -raw42897step0 := by apply Matrix.ext; change ∀ i j, raw42897step1 i j = -(raw42897step0 i j); unfold raw42897step1 raw42897step0; decide +kernel
      have hl : raw42897step1Labels = raw42897step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42897step1 raw42897step1Labels = mixedMoment B raw42897step2 raw42897step2Labels := by
      have ha : raw42897step2 = raw42897step1 := by apply Matrix.ext; unfold raw42897step2 raw42897step1; decide +kernel
      have hl : raw42897step1Labels = labelEmbedding7 ∘ raw42897step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42897step1 raw42897step1Labels raw42897step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical42898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42898 raw42898Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw42898 raw42898Labels = mixedMoment B raw42898step0 raw42898step0Labels := by
      have ha : raw42898step0 = (fun i j => raw42898 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42898step0 raw42898; decide +kernel
      have hl : raw42898step0Labels = raw42898Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42898 raw42898Labels permutation683 permutation2
    mixedMoment B raw42898step0 raw42898step0Labels = mixedMoment B raw42898step1 raw42898step1Labels := by
      have ha : raw42898step1 = -raw42898step0 := by apply Matrix.ext; change ∀ i j, raw42898step1 i j = -(raw42898step0 i j); unfold raw42898step1 raw42898step0; decide +kernel
      have hl : raw42898step1Labels = raw42898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42898step1 raw42898step1Labels = mixedMoment B raw42898step2 raw42898step2Labels := by
      have ha : raw42898step2 = raw42898step1 := by apply Matrix.ext; unfold raw42898step2 raw42898step1; decide +kernel
      have hl : raw42898step1Labels = labelEmbedding1 ∘ raw42898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42898step1 raw42898step1Labels raw42898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical42899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42899 raw42899Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw42899 raw42899Labels = mixedMoment B raw42899step0 raw42899step0Labels := by
      have ha : raw42899step0 = (fun i j => raw42899 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42899step0 raw42899; decide +kernel
      have hl : raw42899step0Labels = raw42899Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42899 raw42899Labels permutation683 permutation2
    mixedMoment B raw42899step0 raw42899step0Labels = mixedMoment B raw42899step1 raw42899step1Labels := by
      have ha : raw42899step1 = -raw42899step0 := by apply Matrix.ext; change ∀ i j, raw42899step1 i j = -(raw42899step0 i j); unfold raw42899step1 raw42899step0; decide +kernel
      have hl : raw42899step1Labels = raw42899step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42899step1 raw42899step1Labels = mixedMoment B raw42899step2 raw42899step2Labels := by
      have ha : raw42899step2 = raw42899step1 := by apply Matrix.ext; unfold raw42899step2 raw42899step1; decide +kernel
      have hl : raw42899step1Labels = labelEmbedding8 ∘ raw42899step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42899step1 raw42899step1Labels raw42899step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical42900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42900 raw42900Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw42900 raw42900Labels = mixedMoment B raw42900step0 raw42900step0Labels := by
      have ha : raw42900step0 = (fun i j => raw42900 (permutation498 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42900step0 raw42900; decide +kernel
      have hl : raw42900step0Labels = raw42900Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42900 raw42900Labels permutation498 permutation4
    mixedMoment B raw42900step0 raw42900step0Labels = mixedMoment B raw42900step1 raw42900step1Labels := by
      have ha : raw42900step1 = raw42900step0 := by apply Matrix.ext; unfold raw42900step1 raw42900step0; decide +kernel
      have hl : raw42900step0Labels = labelEmbedding1 ∘ raw42900step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42900step0 raw42900step0Labels raw42900step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical42901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42901 raw42901Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42901 raw42901Labels = mixedMoment B raw42901step0 raw42901step0Labels := by
      have ha : raw42901step0 = (fun i j => raw42901 (permutation477 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42901step0 raw42901; decide +kernel
      have hl : raw42901step0Labels = raw42901Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42901 raw42901Labels permutation477 permutation6
    mixedMoment B raw42901step0 raw42901step0Labels = mixedMoment B raw42901step1 raw42901step1Labels := by
      have ha : raw42901step1 = -raw42901step0 := by apply Matrix.ext; change ∀ i j, raw42901step1 i j = -(raw42901step0 i j); unfold raw42901step1 raw42901step0; decide +kernel
      have hl : raw42901step1Labels = raw42901step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical42902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42902 raw42902Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw42902 raw42902Labels = mixedMoment B raw42902step0 raw42902step0Labels := by
      have hz : ∀ j, raw42902 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42902step0 = (fun i j => raw42902 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42902step0 raw42902; decide +kernel
      have hl : raw42902step0Labels = raw42902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42902 raw42902Labels permutation434 hz
    mixedMoment B raw42902step0 raw42902step0Labels = mixedMoment B raw42902step1 raw42902step1Labels := by
      have ha : raw42902step1 = (fun i j => raw42902step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42902step1 raw42902step0; decide +kernel
      have hl : raw42902step1Labels = raw42902step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42902step0 raw42902step0Labels permutation34 permutation4
    mixedMoment B raw42902step1 raw42902step1Labels = mixedMoment B raw42902step2 raw42902step2Labels := by
      have ha : raw42902step2 = -raw42902step1 := by apply Matrix.ext; change ∀ i j, raw42902step2 i j = -(raw42902step1 i j); unfold raw42902step2 raw42902step1; decide +kernel
      have hl : raw42902step2Labels = raw42902step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42902step2 raw42902step2Labels = mixedMoment B raw42902step3 raw42902step3Labels := by
      have ha : raw42902step3 = raw42902step2 := by apply Matrix.ext; unfold raw42902step3 raw42902step2; decide +kernel
      have hl : raw42902step2Labels = labelEmbedding1 ∘ raw42902step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42902step2 raw42902step2Labels raw42902step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

theorem canonical42903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42903 raw42903Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw42903 raw42903Labels = mixedMoment B raw42903step0 raw42903step0Labels := by
      have hz : ∀ j, raw42903 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42903step0 = (fun i j => raw42903 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42903step0 raw42903; decide +kernel
      have hl : raw42903step0Labels = raw42903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42903 raw42903Labels permutation434 hz
    mixedMoment B raw42903step0 raw42903step0Labels = mixedMoment B raw42903step1 raw42903step1Labels := by
      have ha : raw42903step1 = (fun i j => raw42903step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42903step1 raw42903step0; decide +kernel
      have hl : raw42903step1Labels = raw42903step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42903step0 raw42903step0Labels permutation151 permutation3
    mixedMoment B raw42903step1 raw42903step1Labels = mixedMoment B raw42903step2 raw42903step2Labels := by
      have ha : raw42903step2 = -raw42903step1 := by apply Matrix.ext; change ∀ i j, raw42903step2 i j = -(raw42903step1 i j); unfold raw42903step2 raw42903step1; decide +kernel
      have hl : raw42903step2Labels = raw42903step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42903step2 raw42903step2Labels = mixedMoment B raw42903step3 raw42903step3Labels := by
      have ha : raw42903step3 = raw42903step2 := by apply Matrix.ext; unfold raw42903step3 raw42903step2; decide +kernel
      have hl : raw42903step2Labels = labelEmbedding7 ∘ raw42903step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42903step2 raw42903step2Labels raw42903step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical42904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42904 raw42904Labels = mixedMoment B node3997 node3997Labels := by
  calc
    mixedMoment B raw42904 raw42904Labels = mixedMoment B raw42904step0 raw42904step0Labels := by
      have hz : ∀ j, raw42904 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42904step0 = (fun i j => raw42904 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42904step0 raw42904; decide +kernel
      have hl : raw42904step0Labels = raw42904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42904 raw42904Labels permutation434 hz
    mixedMoment B raw42904step0 raw42904step0Labels = mixedMoment B raw42904step1 raw42904step1Labels := by
      have ha : raw42904step1 = (fun i j => raw42904step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42904step1 raw42904step0; decide +kernel
      have hl : raw42904step1Labels = raw42904step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42904step0 raw42904step0Labels permutation146 permutation2
    mixedMoment B raw42904step1 raw42904step1Labels = mixedMoment B raw42904step2 raw42904step2Labels := by
      have ha : raw42904step2 = -raw42904step1 := by apply Matrix.ext; change ∀ i j, raw42904step2 i j = -(raw42904step1 i j); unfold raw42904step2 raw42904step1; decide +kernel
      have hl : raw42904step2Labels = raw42904step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42904step2 raw42904step2Labels = mixedMoment B raw42904step3 raw42904step3Labels := by
      have ha : raw42904step3 = raw42904step2 := by apply Matrix.ext; unfold raw42904step3 raw42904step2; decide +kernel
      have hl : raw42904step2Labels = labelEmbedding1 ∘ raw42904step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42904step2 raw42904step2Labels raw42904step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3997 node3997Labels := by rfl

theorem canonical42905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42905 raw42905Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw42905 raw42905Labels = mixedMoment B raw42905step0 raw42905step0Labels := by
      have hz : ∀ j, raw42905 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42905step0 = (fun i j => raw42905 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42905step0 raw42905; decide +kernel
      have hl : raw42905step0Labels = raw42905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42905 raw42905Labels permutation434 hz
    mixedMoment B raw42905step0 raw42905step0Labels = mixedMoment B raw42905step1 raw42905step1Labels := by
      have ha : raw42905step1 = (fun i j => raw42905step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42905step1 raw42905step0; decide +kernel
      have hl : raw42905step1Labels = raw42905step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42905step0 raw42905step0Labels permutation151 permutation3
    mixedMoment B raw42905step1 raw42905step1Labels = mixedMoment B raw42905step2 raw42905step2Labels := by
      have ha : raw42905step2 = -raw42905step1 := by apply Matrix.ext; change ∀ i j, raw42905step2 i j = -(raw42905step1 i j); unfold raw42905step2 raw42905step1; decide +kernel
      have hl : raw42905step2Labels = raw42905step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42905step2 raw42905step2Labels = mixedMoment B raw42905step3 raw42905step3Labels := by
      have ha : raw42905step3 = raw42905step2 := by apply Matrix.ext; unfold raw42905step3 raw42905step2; decide +kernel
      have hl : raw42905step2Labels = labelEmbedding7 ∘ raw42905step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42905step2 raw42905step2Labels raw42905step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical42906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42906 raw42906Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw42906 raw42906Labels = mixedMoment B raw42906step0 raw42906step0Labels := by
      have ha : raw42906step0 = (fun i j => raw42906 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42906step0 raw42906; decide +kernel
      have hl : raw42906step0Labels = raw42906Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42906 raw42906Labels permutation683 permutation2
    mixedMoment B raw42906step0 raw42906step0Labels = mixedMoment B raw42906step1 raw42906step1Labels := by
      have ha : raw42906step1 = -raw42906step0 := by apply Matrix.ext; change ∀ i j, raw42906step1 i j = -(raw42906step0 i j); unfold raw42906step1 raw42906step0; decide +kernel
      have hl : raw42906step1Labels = raw42906step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42906step1 raw42906step1Labels = mixedMoment B raw42906step2 raw42906step2Labels := by
      have ha : raw42906step2 = raw42906step1 := by apply Matrix.ext; unfold raw42906step2 raw42906step1; decide +kernel
      have hl : raw42906step1Labels = labelEmbedding1 ∘ raw42906step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42906step1 raw42906step1Labels raw42906step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

theorem canonical42907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42907 raw42907Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42907 raw42907Labels = mixedMoment B raw42907step0 raw42907step0Labels := by
      have ha : raw42907step0 = (fun i j => raw42907 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42907step0 raw42907; decide +kernel
      have hl : raw42907step0Labels = raw42907Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42907 raw42907Labels permutation683 permutation2
    mixedMoment B raw42907step0 raw42907step0Labels = mixedMoment B raw42907step1 raw42907step1Labels := by
      have ha : raw42907step1 = -raw42907step0 := by apply Matrix.ext; change ∀ i j, raw42907step1 i j = -(raw42907step0 i j); unfold raw42907step1 raw42907step0; decide +kernel
      have hl : raw42907step1Labels = raw42907step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42907step1 raw42907step1Labels = mixedMoment B raw42907step2 raw42907step2Labels := by
      have ha : raw42907step2 = raw42907step1 := by apply Matrix.ext; unfold raw42907step2 raw42907step1; decide +kernel
      have hl : raw42907step1Labels = labelEmbedding8 ∘ raw42907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42907step1 raw42907step1Labels raw42907step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical42908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42908 raw42908Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw42908 raw42908Labels = mixedMoment B raw42908step0 raw42908step0Labels := by
      have hz : ∀ j, raw42908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42908step0 = (fun i j => raw42908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42908step0 raw42908; decide +kernel
      have hl : raw42908step0Labels = raw42908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42908 raw42908Labels permutation434 hz
    mixedMoment B raw42908step0 raw42908step0Labels = mixedMoment B raw42908step1 raw42908step1Labels := by
      have ha : raw42908step1 = (fun i j => raw42908step0 (permutation97 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42908step1 raw42908step0; decide +kernel
      have hl : raw42908step1Labels = raw42908step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42908step0 raw42908step0Labels permutation97 permutation4
    mixedMoment B raw42908step1 raw42908step1Labels = mixedMoment B raw42908step2 raw42908step2Labels := by
      have ha : raw42908step2 = raw42908step1 := by apply Matrix.ext; unfold raw42908step2 raw42908step1; decide +kernel
      have hl : raw42908step1Labels = labelEmbedding1 ∘ raw42908step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42908step1 raw42908step1Labels raw42908step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

theorem canonical42909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42909 raw42909Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw42909 raw42909Labels = mixedMoment B raw42909step0 raw42909step0Labels := by
      have hz : ∀ j, raw42909 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42909step0 = (fun i j => raw42909 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42909step0 raw42909; decide +kernel
      have hl : raw42909step0Labels = raw42909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42909 raw42909Labels permutation434 hz
    mixedMoment B raw42909step0 raw42909step0Labels = mixedMoment B raw42909step1 raw42909step1Labels := by
      have ha : raw42909step1 = (fun i j => raw42909step0 (permutation94 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42909step1 raw42909step0; decide +kernel
      have hl : raw42909step1Labels = raw42909step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42909step0 raw42909step0Labels permutation94 permutation6
    mixedMoment B raw42909step1 raw42909step1Labels = mixedMoment B raw42909step2 raw42909step2Labels := by
      have ha : raw42909step2 = -raw42909step1 := by apply Matrix.ext; change ∀ i j, raw42909step2 i j = -(raw42909step1 i j); unfold raw42909step2 raw42909step1; decide +kernel
      have hl : raw42909step2Labels = raw42909step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5260 node5260Labels := by rfl

theorem canonical42910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42910 raw42910Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw42910 raw42910Labels = mixedMoment B raw42910step0 raw42910step0Labels := by
      have hz : ∀ j, raw42910 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42910step0 = (fun i j => raw42910 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42910step0 raw42910; decide +kernel
      have hl : raw42910step0Labels = raw42910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42910 raw42910Labels permutation520 hz
    mixedMoment B raw42910step0 raw42910step0Labels = mixedMoment B raw42910step1 raw42910step1Labels := by
      have ha : raw42910step1 = (fun i j => raw42910step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42910step1 raw42910step0; decide +kernel
      have hl : raw42910step1Labels = raw42910step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42910step0 raw42910step0Labels permutation137 permutation4
    mixedMoment B raw42910step1 raw42910step1Labels = mixedMoment B raw42910step2 raw42910step2Labels := by
      have ha : raw42910step2 = raw42910step1 := by apply Matrix.ext; unfold raw42910step2 raw42910step1; decide +kernel
      have hl : raw42910step1Labels = labelEmbedding1 ∘ raw42910step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42910step1 raw42910step1Labels raw42910step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

theorem canonical42911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42911 raw42911Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw42911 raw42911Labels = mixedMoment B raw42911step0 raw42911step0Labels := by
      have hz : ∀ j, raw42911 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42911step0 = (fun i j => raw42911 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42911step0 raw42911; decide +kernel
      have hl : raw42911step0Labels = raw42911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42911 raw42911Labels permutation520 hz
    mixedMoment B raw42911step0 raw42911step0Labels = mixedMoment B raw42911step1 raw42911step1Labels := by
      have ha : raw42911step1 = (fun i j => raw42911step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42911step1 raw42911step0; decide +kernel
      have hl : raw42911step1Labels = raw42911step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42911step0 raw42911step0Labels permutation137 permutation5
    mixedMoment B raw42911step1 raw42911step1Labels = mixedMoment B raw42911step2 raw42911step2Labels := by
      have ha : raw42911step2 = raw42911step1 := by apply Matrix.ext; unfold raw42911step2 raw42911step1; decide +kernel
      have hl : raw42911step1Labels = labelEmbedding9 ∘ raw42911step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42911step1 raw42911step1Labels raw42911step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical42912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42912 raw42912Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw42912 raw42912Labels = mixedMoment B raw42912step0 raw42912step0Labels := by
      have ha : raw42912step0 = (fun i j => raw42912 (permutation611 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42912step0 raw42912; decide +kernel
      have hl : raw42912step0Labels = raw42912Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42912 raw42912Labels permutation611 permutation4
    mixedMoment B raw42912step0 raw42912step0Labels = mixedMoment B raw42912step1 raw42912step1Labels := by
      have ha : raw42912step1 = raw42912step0 := by apply Matrix.ext; unfold raw42912step1 raw42912step0; decide +kernel
      have hl : raw42912step0Labels = labelEmbedding1 ∘ raw42912step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42912step0 raw42912step0Labels raw42912step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3065 node3065Labels := by rfl

theorem canonical42913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42913 raw42913Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw42913 raw42913Labels = mixedMoment B raw42913step0 raw42913step0Labels := by
      have ha : raw42913step0 = (fun i j => raw42913 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42913step0 raw42913; decide +kernel
      have hl : raw42913step0Labels = raw42913Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42913 raw42913Labels permutation674 permutation5
    mixedMoment B raw42913step0 raw42913step0Labels = mixedMoment B raw42913step1 raw42913step1Labels := by
      have ha : raw42913step1 = raw42913step0 := by apply Matrix.ext; unfold raw42913step1 raw42913step0; decide +kernel
      have hl : raw42913step0Labels = labelEmbedding9 ∘ raw42913step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42913step0 raw42913step0Labels raw42913step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5250 node5250Labels := by rfl

theorem canonical42914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42914 raw42914Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw42914 raw42914Labels = mixedMoment B raw42914step0 raw42914step0Labels := by
      have ha : raw42914step0 = (fun i j => raw42914 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42914step0 raw42914; decide +kernel
      have hl : raw42914step0Labels = raw42914Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42914 raw42914Labels permutation200 permutation4
    mixedMoment B raw42914step0 raw42914step0Labels = mixedMoment B raw42914step1 raw42914step1Labels := by
      have ha : raw42914step1 = -raw42914step0 := by apply Matrix.ext; change ∀ i j, raw42914step1 i j = -(raw42914step0 i j); unfold raw42914step1 raw42914step0; decide +kernel
      have hl : raw42914step1Labels = raw42914step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42914step1 raw42914step1Labels = mixedMoment B raw42914step2 raw42914step2Labels := by
      have ha : raw42914step2 = raw42914step1 := by apply Matrix.ext; unfold raw42914step2 raw42914step1; decide +kernel
      have hl : raw42914step1Labels = labelEmbedding1 ∘ raw42914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42914step1 raw42914step1Labels raw42914step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3977 node3977Labels := by rfl

theorem canonical42915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42915 raw42915Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw42915 raw42915Labels = mixedMoment B raw42915step0 raw42915step0Labels := by
      have ha : raw42915step0 = (fun i j => raw42915 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42915step0 raw42915; decide +kernel
      have hl : raw42915step0Labels = raw42915Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42915 raw42915Labels permutation674 permutation5
    mixedMoment B raw42915step0 raw42915step0Labels = mixedMoment B raw42915step1 raw42915step1Labels := by
      have ha : raw42915step1 = raw42915step0 := by apply Matrix.ext; unfold raw42915step1 raw42915step0; decide +kernel
      have hl : raw42915step0Labels = labelEmbedding9 ∘ raw42915step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42915step0 raw42915step0Labels raw42915step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical42916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42916 raw42916Labels = mixedMoment B node3976 node3976Labels := by
  calc
    mixedMoment B raw42916 raw42916Labels = mixedMoment B raw42916step0 raw42916step0Labels := by
      have ha : raw42916step0 = (fun i j => raw42916 (permutation201 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42916step0 raw42916; decide +kernel
      have hl : raw42916step0Labels = raw42916Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42916 raw42916Labels permutation201 permutation4
    mixedMoment B raw42916step0 raw42916step0Labels = mixedMoment B raw42916step1 raw42916step1Labels := by
      have ha : raw42916step1 = -raw42916step0 := by apply Matrix.ext; change ∀ i j, raw42916step1 i j = -(raw42916step0 i j); unfold raw42916step1 raw42916step0; decide +kernel
      have hl : raw42916step1Labels = raw42916step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42916step1 raw42916step1Labels = mixedMoment B raw42916step2 raw42916step2Labels := by
      have ha : raw42916step2 = raw42916step1 := by apply Matrix.ext; unfold raw42916step2 raw42916step1; decide +kernel
      have hl : raw42916step1Labels = labelEmbedding1 ∘ raw42916step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42916step1 raw42916step1Labels raw42916step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3976 node3976Labels := by rfl

theorem canonical42917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42917 raw42917Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw42917 raw42917Labels = mixedMoment B raw42917step0 raw42917step0Labels := by
      have ha : raw42917step0 = (fun i j => raw42917 (permutation577 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42917step0 raw42917; decide +kernel
      have hl : raw42917step0Labels = raw42917Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42917 raw42917Labels permutation577 permutation5
    mixedMoment B raw42917step0 raw42917step0Labels = mixedMoment B raw42917step1 raw42917step1Labels := by
      have ha : raw42917step1 = raw42917step0 := by apply Matrix.ext; unfold raw42917step1 raw42917step0; decide +kernel
      have hl : raw42917step0Labels = labelEmbedding9 ∘ raw42917step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42917step0 raw42917step0Labels raw42917step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5471 node5471Labels := by rfl

theorem canonical42918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42918 raw42918Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw42918 raw42918Labels = mixedMoment B raw42918step0 raw42918step0Labels := by
      have ha : raw42918step0 = (fun i j => raw42918 (permutation535 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42918step0 raw42918; decide +kernel
      have hl : raw42918step0Labels = raw42918Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42918 raw42918Labels permutation535 permutation4
    mixedMoment B raw42918step0 raw42918step0Labels = mixedMoment B raw42918step1 raw42918step1Labels := by
      have ha : raw42918step1 = raw42918step0 := by apply Matrix.ext; unfold raw42918step1 raw42918step0; decide +kernel
      have hl : raw42918step0Labels = labelEmbedding1 ∘ raw42918step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42918step0 raw42918step0Labels raw42918step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2698 node2698Labels := by rfl

theorem canonical42919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42919 raw42919Labels = mixedMoment B node5244 node5244Labels := by
  calc
    mixedMoment B raw42919 raw42919Labels = mixedMoment B raw42919step0 raw42919step0Labels := by
      have ha : raw42919step0 = (fun i j => raw42919 (permutation535 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42919step0 raw42919; decide +kernel
      have hl : raw42919step0Labels = raw42919Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42919 raw42919Labels permutation535 permutation4
    mixedMoment B raw42919step0 raw42919step0Labels = mixedMoment B raw42919step1 raw42919step1Labels := by
      have ha : raw42919step1 = raw42919step0 := by apply Matrix.ext; unfold raw42919step1 raw42919step0; decide +kernel
      have hl : raw42919step0Labels = labelEmbedding10 ∘ raw42919step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42919step0 raw42919step0Labels raw42919step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5244 node5244Labels := by rfl

theorem canonical42920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42920 raw42920Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw42920 raw42920Labels = mixedMoment B raw42920step0 raw42920step0Labels := by
      have hz : ∀ j, raw42920 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42920step0 = (fun i j => raw42920 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42920step0 raw42920; decide +kernel
      have hl : raw42920step0Labels = raw42920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42920 raw42920Labels permutation434 hz
    mixedMoment B raw42920step0 raw42920step0Labels = mixedMoment B raw42920step1 raw42920step1Labels := by
      have ha : raw42920step1 = (fun i j => raw42920step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42920step1 raw42920step0; decide +kernel
      have hl : raw42920step1Labels = raw42920step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42920step0 raw42920step0Labels permutation137 permutation4
    mixedMoment B raw42920step1 raw42920step1Labels = mixedMoment B raw42920step2 raw42920step2Labels := by
      have ha : raw42920step2 = raw42920step1 := by apply Matrix.ext; unfold raw42920step2 raw42920step1; decide +kernel
      have hl : raw42920step1Labels = labelEmbedding1 ∘ raw42920step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42920step1 raw42920step1Labels raw42920step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3078 node3078Labels := by rfl

theorem canonical42921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42921 raw42921Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw42921 raw42921Labels = mixedMoment B raw42921step0 raw42921step0Labels := by
      have hz : ∀ j, raw42921 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42921step0 = (fun i j => raw42921 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42921step0 raw42921; decide +kernel
      have hl : raw42921step0Labels = raw42921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42921 raw42921Labels permutation434 hz
    mixedMoment B raw42921step0 raw42921step0Labels = mixedMoment B raw42921step1 raw42921step1Labels := by
      have ha : raw42921step1 = (fun i j => raw42921step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42921step1 raw42921step0; decide +kernel
      have hl : raw42921step1Labels = raw42921step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42921step0 raw42921step0Labels permutation137 permutation5
    mixedMoment B raw42921step1 raw42921step1Labels = mixedMoment B raw42921step2 raw42921step2Labels := by
      have ha : raw42921step2 = raw42921step1 := by apply Matrix.ext; unfold raw42921step2 raw42921step1; decide +kernel
      have hl : raw42921step1Labels = labelEmbedding9 ∘ raw42921step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42921step1 raw42921step1Labels raw42921step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

theorem canonical42922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42922 raw42922Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw42922 raw42922Labels = mixedMoment B raw42922step0 raw42922step0Labels := by
      have hz : ∀ j, raw42922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42922step0 = (fun i j => raw42922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42922step0 raw42922; decide +kernel
      have hl : raw42922step0Labels = raw42922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42922 raw42922Labels permutation434 hz
    mixedMoment B raw42922step0 raw42922step0Labels = mixedMoment B raw42922step1 raw42922step1Labels := by
      have ha : raw42922step1 = (fun i j => raw42922step0 (permutation113 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42922step1 raw42922step0; decide +kernel
      have hl : raw42922step1Labels = raw42922step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42922step0 raw42922step0Labels permutation113 permutation4
    mixedMoment B raw42922step1 raw42922step1Labels = mixedMoment B raw42922step2 raw42922step2Labels := by
      have ha : raw42922step2 = raw42922step1 := by apply Matrix.ext; unfold raw42922step2 raw42922step1; decide +kernel
      have hl : raw42922step1Labels = labelEmbedding1 ∘ raw42922step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42922step1 raw42922step1Labels raw42922step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2706 node2706Labels := by rfl

theorem canonical42923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42923 raw42923Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw42923 raw42923Labels = mixedMoment B raw42923step0 raw42923step0Labels := by
      have hz : ∀ j, raw42923 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42923step0 = (fun i j => raw42923 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42923step0 raw42923; decide +kernel
      have hl : raw42923step0Labels = raw42923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42923 raw42923Labels permutation434 hz
    mixedMoment B raw42923step0 raw42923step0Labels = mixedMoment B raw42923step1 raw42923step1Labels := by
      have ha : raw42923step1 = (fun i j => raw42923step0 (permutation128 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42923step1 raw42923step0; decide +kernel
      have hl : raw42923step1Labels = raw42923step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42923step0 raw42923step0Labels permutation128 permutation7
    mixedMoment B raw42923step1 raw42923step1Labels = mixedMoment B raw42923step2 raw42923step2Labels := by
      have ha : raw42923step2 = raw42923step1 := by apply Matrix.ext; unfold raw42923step2 raw42923step1; decide +kernel
      have hl : raw42923step1Labels = labelEmbedding6 ∘ raw42923step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42923step1 raw42923step1Labels raw42923step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5205 node5205Labels := by rfl

theorem canonical42924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42924 raw42924Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw42924 raw42924Labels = mixedMoment B raw42924step0 raw42924step0Labels := by
      have ha : raw42924step0 = (fun i j => raw42924 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42924step0 raw42924; decide +kernel
      have hl : raw42924step0Labels = raw42924Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42924 raw42924Labels permutation224 permutation4
    mixedMoment B raw42924step0 raw42924step0Labels = mixedMoment B raw42924step1 raw42924step1Labels := by
      have ha : raw42924step1 = -raw42924step0 := by apply Matrix.ext; change ∀ i j, raw42924step1 i j = -(raw42924step0 i j); unfold raw42924step1 raw42924step0; decide +kernel
      have hl : raw42924step1Labels = raw42924step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42924step1 raw42924step1Labels = mixedMoment B raw42924step2 raw42924step2Labels := by
      have ha : raw42924step2 = raw42924step1 := by apply Matrix.ext; unfold raw42924step2 raw42924step1; decide +kernel
      have hl : raw42924step1Labels = labelEmbedding1 ∘ raw42924step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42924step1 raw42924step1Labels raw42924step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3954 node3954Labels := by rfl

theorem canonical42925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42925 raw42925Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42925 raw42925Labels = mixedMoment B raw42925step0 raw42925step0Labels := by
      have ha : raw42925step0 = (fun i j => raw42925 (permutation653 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42925step0 raw42925; decide +kernel
      have hl : raw42925step0Labels = raw42925Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42925 raw42925Labels permutation653 permutation5
    mixedMoment B raw42925step0 raw42925step0Labels = mixedMoment B raw42925step1 raw42925step1Labels := by
      have ha : raw42925step1 = raw42925step0 := by apply Matrix.ext; unfold raw42925step1 raw42925step0; decide +kernel
      have hl : raw42925step0Labels = labelEmbedding9 ∘ raw42925step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42925step0 raw42925step0Labels raw42925step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical42926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42926 raw42926Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw42926 raw42926Labels = mixedMoment B raw42926step0 raw42926step0Labels := by
      have ha : raw42926step0 = (fun i j => raw42926 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42926step0 raw42926; decide +kernel
      have hl : raw42926step0Labels = raw42926Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42926 raw42926Labels permutation683 permutation2
    mixedMoment B raw42926step0 raw42926step0Labels = mixedMoment B raw42926step1 raw42926step1Labels := by
      have ha : raw42926step1 = -raw42926step0 := by apply Matrix.ext; change ∀ i j, raw42926step1 i j = -(raw42926step0 i j); unfold raw42926step1 raw42926step0; decide +kernel
      have hl : raw42926step1Labels = raw42926step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42926step1 raw42926step1Labels = mixedMoment B raw42926step2 raw42926step2Labels := by
      have ha : raw42926step2 = raw42926step1 := by apply Matrix.ext; unfold raw42926step2 raw42926step1; decide +kernel
      have hl : raw42926step1Labels = labelEmbedding1 ∘ raw42926step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42926step1 raw42926step1Labels raw42926step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3569 node3569Labels := by rfl

theorem canonical42927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42927 raw42927Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw42927 raw42927Labels = mixedMoment B raw42927step0 raw42927step0Labels := by
      have ha : raw42927step0 = (fun i j => raw42927 (permutation601 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42927step0 raw42927; decide +kernel
      have hl : raw42927step0Labels = raw42927Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42927 raw42927Labels permutation601 permutation7
    mixedMoment B raw42927step0 raw42927step0Labels = mixedMoment B raw42927step1 raw42927step1Labels := by
      have ha : raw42927step1 = raw42927step0 := by apply Matrix.ext; unfold raw42927step1 raw42927step0; decide +kernel
      have hl : raw42927step0Labels = labelEmbedding6 ∘ raw42927step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42927step0 raw42927step0Labels raw42927step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

theorem canonical42928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42928 raw42928Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw42928 raw42928Labels = mixedMoment B raw42928step0 raw42928step0Labels := by
      have ha : raw42928step0 = (fun i j => raw42928 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42928step0 raw42928; decide +kernel
      have hl : raw42928step0Labels = raw42928Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42928 raw42928Labels permutation683 permutation2
    mixedMoment B raw42928step0 raw42928step0Labels = mixedMoment B raw42928step1 raw42928step1Labels := by
      have ha : raw42928step1 = -raw42928step0 := by apply Matrix.ext; change ∀ i j, raw42928step1 i j = -(raw42928step0 i j); unfold raw42928step1 raw42928step0; decide +kernel
      have hl : raw42928step1Labels = raw42928step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42928step1 raw42928step1Labels = mixedMoment B raw42928step2 raw42928step2Labels := by
      have ha : raw42928step2 = raw42928step1 := by apply Matrix.ext; unfold raw42928step2 raw42928step1; decide +kernel
      have hl : raw42928step1Labels = labelEmbedding1 ∘ raw42928step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42928step1 raw42928step1Labels raw42928step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

theorem canonical42929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42929 raw42929Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw42929 raw42929Labels = mixedMoment B raw42929step0 raw42929step0Labels := by
      have ha : raw42929step0 = (fun i j => raw42929 (permutation599 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42929step0 raw42929; decide +kernel
      have hl : raw42929step0Labels = raw42929Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42929 raw42929Labels permutation599 permutation7
    mixedMoment B raw42929step0 raw42929step0Labels = mixedMoment B raw42929step1 raw42929step1Labels := by
      have ha : raw42929step1 = raw42929step0 := by apply Matrix.ext; unfold raw42929step1 raw42929step0; decide +kernel
      have hl : raw42929step0Labels = labelEmbedding6 ∘ raw42929step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42929step0 raw42929step0Labels raw42929step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5187 node5187Labels := by rfl

theorem canonical42930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42930 raw42930Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw42930 raw42930Labels = mixedMoment B raw42930step0 raw42930step0Labels := by
      have ha : raw42930step0 = (fun i j => raw42930 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42930step0 raw42930; decide +kernel
      have hl : raw42930step0Labels = raw42930Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42930 raw42930Labels permutation212 permutation4
    mixedMoment B raw42930step0 raw42930step0Labels = mixedMoment B raw42930step1 raw42930step1Labels := by
      have ha : raw42930step1 = -raw42930step0 := by apply Matrix.ext; change ∀ i j, raw42930step1 i j = -(raw42930step0 i j); unfold raw42930step1 raw42930step0; decide +kernel
      have hl : raw42930step1Labels = raw42930step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42930step1 raw42930step1Labels = mixedMoment B raw42930step2 raw42930step2Labels := by
      have ha : raw42930step2 = raw42930step1 := by apply Matrix.ext; unfold raw42930step2 raw42930step1; decide +kernel
      have hl : raw42930step1Labels = labelEmbedding1 ∘ raw42930step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42930step1 raw42930step1Labels raw42930step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3972 node3972Labels := by rfl

theorem canonical42931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42931 raw42931Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42931 raw42931Labels = mixedMoment B raw42931step0 raw42931step0Labels := by
      have ha : raw42931step0 = (fun i j => raw42931 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42931step0 raw42931; decide +kernel
      have hl : raw42931step0Labels = raw42931Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42931 raw42931Labels permutation688 permutation3
    mixedMoment B raw42931step0 raw42931step0Labels = mixedMoment B raw42931step1 raw42931step1Labels := by
      have ha : raw42931step1 = -raw42931step0 := by apply Matrix.ext; change ∀ i j, raw42931step1 i j = -(raw42931step0 i j); unfold raw42931step1 raw42931step0; decide +kernel
      have hl : raw42931step1Labels = raw42931step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42931step1 raw42931step1Labels = mixedMoment B raw42931step2 raw42931step2Labels := by
      have ha : raw42931step2 = raw42931step1 := by apply Matrix.ext; unfold raw42931step2 raw42931step1; decide +kernel
      have hl : raw42931step1Labels = labelEmbedding7 ∘ raw42931step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42931step1 raw42931step1Labels raw42931step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical42932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42932 raw42932Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw42932 raw42932Labels = mixedMoment B raw42932step0 raw42932step0Labels := by
      have ha : raw42932step0 = (fun i j => raw42932 (permutation205 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42932step0 raw42932; decide +kernel
      have hl : raw42932step0Labels = raw42932Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42932 raw42932Labels permutation205 permutation4
    mixedMoment B raw42932step0 raw42932step0Labels = mixedMoment B raw42932step1 raw42932step1Labels := by
      have ha : raw42932step1 = -raw42932step0 := by apply Matrix.ext; change ∀ i j, raw42932step1 i j = -(raw42932step0 i j); unfold raw42932step1 raw42932step0; decide +kernel
      have hl : raw42932step1Labels = raw42932step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42932step1 raw42932step1Labels = mixedMoment B raw42932step2 raw42932step2Labels := by
      have ha : raw42932step2 = raw42932step1 := by apply Matrix.ext; unfold raw42932step2 raw42932step1; decide +kernel
      have hl : raw42932step1Labels = labelEmbedding1 ∘ raw42932step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42932step1 raw42932step1Labels raw42932step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

theorem canonical42933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42933 raw42933Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw42933 raw42933Labels = mixedMoment B raw42933step0 raw42933step0Labels := by
      have ha : raw42933step0 = (fun i j => raw42933 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42933step0 raw42933; decide +kernel
      have hl : raw42933step0Labels = raw42933Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42933 raw42933Labels permutation688 permutation3
    mixedMoment B raw42933step0 raw42933step0Labels = mixedMoment B raw42933step1 raw42933step1Labels := by
      have ha : raw42933step1 = -raw42933step0 := by apply Matrix.ext; change ∀ i j, raw42933step1 i j = -(raw42933step0 i j); unfold raw42933step1 raw42933step0; decide +kernel
      have hl : raw42933step1Labels = raw42933step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42933step1 raw42933step1Labels = mixedMoment B raw42933step2 raw42933step2Labels := by
      have ha : raw42933step2 = raw42933step1 := by apply Matrix.ext; unfold raw42933step2 raw42933step1; decide +kernel
      have hl : raw42933step1Labels = labelEmbedding7 ∘ raw42933step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42933step1 raw42933step1Labels raw42933step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

theorem canonical42934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42934 raw42934Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw42934 raw42934Labels = mixedMoment B raw42934step0 raw42934step0Labels := by
      have ha : raw42934step0 = (fun i j => raw42934 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42934step0 raw42934; decide +kernel
      have hl : raw42934step0Labels = raw42934Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42934 raw42934Labels permutation683 permutation2
    mixedMoment B raw42934step0 raw42934step0Labels = mixedMoment B raw42934step1 raw42934step1Labels := by
      have ha : raw42934step1 = -raw42934step0 := by apply Matrix.ext; change ∀ i j, raw42934step1 i j = -(raw42934step0 i j); unfold raw42934step1 raw42934step0; decide +kernel
      have hl : raw42934step1Labels = raw42934step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42934step1 raw42934step1Labels = mixedMoment B raw42934step2 raw42934step2Labels := by
      have ha : raw42934step2 = raw42934step1 := by apply Matrix.ext; unfold raw42934step2 raw42934step1; decide +kernel
      have hl : raw42934step1Labels = labelEmbedding1 ∘ raw42934step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42934step1 raw42934step1Labels raw42934step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3873 node3873Labels := by rfl

theorem canonical42935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42935 raw42935Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw42935 raw42935Labels = mixedMoment B raw42935step0 raw42935step0Labels := by
      have ha : raw42935step0 = (fun i j => raw42935 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42935step0 raw42935; decide +kernel
      have hl : raw42935step0Labels = raw42935Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42935 raw42935Labels permutation650 permutation7
    mixedMoment B raw42935step0 raw42935step0Labels = mixedMoment B raw42935step1 raw42935step1Labels := by
      have ha : raw42935step1 = raw42935step0 := by apply Matrix.ext; unfold raw42935step1 raw42935step0; decide +kernel
      have hl : raw42935step0Labels = labelEmbedding6 ∘ raw42935step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42935step0 raw42935step0Labels raw42935step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

theorem canonical42936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42936 raw42936Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw42936 raw42936Labels = mixedMoment B raw42936step0 raw42936step0Labels := by
      have hz : ∀ j, raw42936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42936step0 = (fun i j => raw42936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42936step0 raw42936; decide +kernel
      have hl : raw42936step0Labels = raw42936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42936 raw42936Labels permutation434 hz
    mixedMoment B raw42936step0 raw42936step0Labels = mixedMoment B raw42936step1 raw42936step1Labels := by
      have ha : raw42936step1 = (fun i j => raw42936step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42936step1 raw42936step0; decide +kernel
      have hl : raw42936step1Labels = raw42936step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42936step0 raw42936step0Labels permutation44 permutation4
    mixedMoment B raw42936step1 raw42936step1Labels = mixedMoment B raw42936step2 raw42936step2Labels := by
      have ha : raw42936step2 = -raw42936step1 := by apply Matrix.ext; change ∀ i j, raw42936step2 i j = -(raw42936step1 i j); unfold raw42936step2 raw42936step1; decide +kernel
      have hl : raw42936step2Labels = raw42936step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42936step2 raw42936step2Labels = mixedMoment B raw42936step3 raw42936step3Labels := by
      have ha : raw42936step3 = raw42936step2 := by apply Matrix.ext; unfold raw42936step3 raw42936step2; decide +kernel
      have hl : raw42936step2Labels = labelEmbedding1 ∘ raw42936step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42936step2 raw42936step2Labels raw42936step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

theorem canonical42937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42937 raw42937Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw42937 raw42937Labels = mixedMoment B raw42937step0 raw42937step0Labels := by
      have hz : ∀ j, raw42937 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42937step0 = (fun i j => raw42937 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42937step0 raw42937; decide +kernel
      have hl : raw42937step0Labels = raw42937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42937 raw42937Labels permutation434 hz
    mixedMoment B raw42937step0 raw42937step0Labels = mixedMoment B raw42937step1 raw42937step1Labels := by
      have ha : raw42937step1 = (fun i j => raw42937step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42937step1 raw42937step0; decide +kernel
      have hl : raw42937step1Labels = raw42937step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42937step0 raw42937step0Labels permutation143 permutation5
    mixedMoment B raw42937step1 raw42937step1Labels = mixedMoment B raw42937step2 raw42937step2Labels := by
      have ha : raw42937step2 = raw42937step1 := by apply Matrix.ext; unfold raw42937step2 raw42937step1; decide +kernel
      have hl : raw42937step1Labels = labelEmbedding9 ∘ raw42937step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42937step1 raw42937step1Labels raw42937step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

theorem canonical42938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42938 raw42938Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw42938 raw42938Labels = mixedMoment B raw42938step0 raw42938step0Labels := by
      have hz : ∀ j, raw42938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42938step0 = (fun i j => raw42938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42938step0 raw42938; decide +kernel
      have hl : raw42938step0Labels = raw42938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42938 raw42938Labels permutation434 hz
    mixedMoment B raw42938step0 raw42938step0Labels = mixedMoment B raw42938step1 raw42938step1Labels := by
      have ha : raw42938step1 = (fun i j => raw42938step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42938step1 raw42938step0; decide +kernel
      have hl : raw42938step1Labels = raw42938step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42938step0 raw42938step0Labels permutation146 permutation2
    mixedMoment B raw42938step1 raw42938step1Labels = mixedMoment B raw42938step2 raw42938step2Labels := by
      have ha : raw42938step2 = -raw42938step1 := by apply Matrix.ext; change ∀ i j, raw42938step2 i j = -(raw42938step1 i j); unfold raw42938step2 raw42938step1; decide +kernel
      have hl : raw42938step2Labels = raw42938step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42938step2 raw42938step2Labels = mixedMoment B raw42938step3 raw42938step3Labels := by
      have ha : raw42938step3 = raw42938step2 := by apply Matrix.ext; unfold raw42938step3 raw42938step2; decide +kernel
      have hl : raw42938step2Labels = labelEmbedding1 ∘ raw42938step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42938step2 raw42938step2Labels raw42938step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

theorem canonical42939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42939 raw42939Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw42939 raw42939Labels = mixedMoment B raw42939step0 raw42939step0Labels := by
      have hz : ∀ j, raw42939 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42939step0 = (fun i j => raw42939 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42939step0 raw42939; decide +kernel
      have hl : raw42939step0Labels = raw42939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42939 raw42939Labels permutation434 hz
    mixedMoment B raw42939step0 raw42939step0Labels = mixedMoment B raw42939step1 raw42939step1Labels := by
      have ha : raw42939step1 = (fun i j => raw42939step0 (permutation132 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42939step1 raw42939step0; decide +kernel
      have hl : raw42939step1Labels = raw42939step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42939step0 raw42939step0Labels permutation132 permutation7
    mixedMoment B raw42939step1 raw42939step1Labels = mixedMoment B raw42939step2 raw42939step2Labels := by
      have ha : raw42939step2 = raw42939step1 := by apply Matrix.ext; unfold raw42939step2 raw42939step1; decide +kernel
      have hl : raw42939step1Labels = labelEmbedding6 ∘ raw42939step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42939step1 raw42939step1Labels raw42939step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

theorem canonical42940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42940 raw42940Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw42940 raw42940Labels = mixedMoment B raw42940step0 raw42940step0Labels := by
      have ha : raw42940step0 = (fun i j => raw42940 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42940step0 raw42940; decide +kernel
      have hl : raw42940step0Labels = raw42940Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42940 raw42940Labels permutation683 permutation2
    mixedMoment B raw42940step0 raw42940step0Labels = mixedMoment B raw42940step1 raw42940step1Labels := by
      have ha : raw42940step1 = -raw42940step0 := by apply Matrix.ext; change ∀ i j, raw42940step1 i j = -(raw42940step0 i j); unfold raw42940step1 raw42940step0; decide +kernel
      have hl : raw42940step1Labels = raw42940step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42940step1 raw42940step1Labels = mixedMoment B raw42940step2 raw42940step2Labels := by
      have ha : raw42940step2 = raw42940step1 := by apply Matrix.ext; unfold raw42940step2 raw42940step1; decide +kernel
      have hl : raw42940step1Labels = labelEmbedding1 ∘ raw42940step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42940step1 raw42940step1Labels raw42940step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

theorem canonical42941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42941 raw42941Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw42941 raw42941Labels = mixedMoment B raw42941step0 raw42941step0Labels := by
      have ha : raw42941step0 = (fun i j => raw42941 (permutation601 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42941step0 raw42941; decide +kernel
      have hl : raw42941step0Labels = raw42941Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42941 raw42941Labels permutation601 permutation7
    mixedMoment B raw42941step0 raw42941step0Labels = mixedMoment B raw42941step1 raw42941step1Labels := by
      have ha : raw42941step1 = raw42941step0 := by apply Matrix.ext; unfold raw42941step1 raw42941step0; decide +kernel
      have hl : raw42941step0Labels = labelEmbedding6 ∘ raw42941step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42941step0 raw42941step0Labels raw42941step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

theorem canonical42942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42942 raw42942Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw42942 raw42942Labels = mixedMoment B raw42942step0 raw42942step0Labels := by
      have ha : raw42942step0 = (fun i j => raw42942 (permutation406 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42942step0 raw42942; decide +kernel
      have hl : raw42942step0Labels = raw42942Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42942 raw42942Labels permutation406 permutation4
    mixedMoment B raw42942step0 raw42942step0Labels = mixedMoment B raw42942step1 raw42942step1Labels := by
      have ha : raw42942step1 = raw42942step0 := by apply Matrix.ext; unfold raw42942step1 raw42942step0; decide +kernel
      have hl : raw42942step0Labels = labelEmbedding1 ∘ raw42942step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42942step0 raw42942step0Labels raw42942step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

theorem canonical42943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42943 raw42943Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw42943 raw42943Labels = mixedMoment B raw42943step0 raw42943step0Labels := by
      have ha : raw42943step0 = (fun i j => raw42943 (permutation377 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42943step0 raw42943; decide +kernel
      have hl : raw42943step0Labels = raw42943Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42943 raw42943Labels permutation377 permutation6
    mixedMoment B raw42943step0 raw42943step0Labels = mixedMoment B raw42943step1 raw42943step1Labels := by
      have ha : raw42943step1 = -raw42943step0 := by apply Matrix.ext; change ∀ i j, raw42943step1 i j = -(raw42943step0 i j); unfold raw42943step1 raw42943step0; decide +kernel
      have hl : raw42943step1Labels = raw42943step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5138 node5138Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2784 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2784) =
      Integer.Sparse.eval keyMomentRow2784 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2784).leftCharge (GramAssembly.key 2784).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2669) := by
    have ha : gramCharges (GramAssembly.key 2784).leftCharge (GramAssembly.key 2784).rightCharge = raw42880 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42880Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42880 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2784).leftCharge (GramAssembly.key 2784).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5226) := by
    have ha : gramCharges (GramAssembly.key 2784).leftCharge (GramAssembly.key 2784).rightCharge = raw42881 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42881Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42881 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2784).leftCharge (GramAssembly.key 2784).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2784).leftCharge (GramAssembly.key 2784).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2784, Integer.Sparse.eval]
  ring

theorem keyMoment2785 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2785) =
      Integer.Sparse.eval keyMomentRow2785 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2785).leftCharge (GramAssembly.key 2785).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2670) := by
    have ha : gramCharges (GramAssembly.key 2785).leftCharge (GramAssembly.key 2785).rightCharge = raw42882 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42882Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42882 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2785).leftCharge (GramAssembly.key 2785).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5140) := by
    have ha : gramCharges (GramAssembly.key 2785).leftCharge (GramAssembly.key 2785).rightCharge = raw42883 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42883Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42883 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2785).leftCharge (GramAssembly.key 2785).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2785).leftCharge (GramAssembly.key 2785).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2785, Integer.Sparse.eval]
  ring

theorem keyMoment2786 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2786) =
      Integer.Sparse.eval keyMomentRow2786 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2786).leftCharge (GramAssembly.key 2786).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2682) := by
    have ha : gramCharges (GramAssembly.key 2786).leftCharge (GramAssembly.key 2786).rightCharge = raw42884 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42884Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42884 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2786).leftCharge (GramAssembly.key 2786).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5236) := by
    have ha : gramCharges (GramAssembly.key 2786).leftCharge (GramAssembly.key 2786).rightCharge = raw42885 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42885Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42885 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2786).leftCharge (GramAssembly.key 2786).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2786).leftCharge (GramAssembly.key 2786).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2786, Integer.Sparse.eval]
  ring

theorem keyMoment2787 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2787) =
      Integer.Sparse.eval keyMomentRow2787 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2787).leftCharge (GramAssembly.key 2787).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3229) := by
    have ha : gramCharges (GramAssembly.key 2787).leftCharge (GramAssembly.key 2787).rightCharge = raw42886 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42886Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42886 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2787).leftCharge (GramAssembly.key 2787).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4895) := by
    have ha : gramCharges (GramAssembly.key 2787).leftCharge (GramAssembly.key 2787).rightCharge = raw42887 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42887Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42887 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2787).leftCharge (GramAssembly.key 2787).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2787).leftCharge (GramAssembly.key 2787).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2787, Integer.Sparse.eval]
  ring

theorem keyMoment2788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2788) =
      Integer.Sparse.eval keyMomentRow2788 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2788).leftCharge (GramAssembly.key 2788).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3088) := by
    have ha : gramCharges (GramAssembly.key 2788).leftCharge (GramAssembly.key 2788).rightCharge = raw42888 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42888Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42888 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2788).leftCharge (GramAssembly.key 2788).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5259) := by
    have ha : gramCharges (GramAssembly.key 2788).leftCharge (GramAssembly.key 2788).rightCharge = raw42889 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42889Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42889 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2788).leftCharge (GramAssembly.key 2788).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2788).leftCharge (GramAssembly.key 2788).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2788, Integer.Sparse.eval]
  ring

theorem keyMoment2789 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2789) =
      Integer.Sparse.eval keyMomentRow2789 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2789).leftCharge (GramAssembly.key 2789).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3996) := by
    have ha : gramCharges (GramAssembly.key 2789).leftCharge (GramAssembly.key 2789).rightCharge = raw42890 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42890Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42890 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2789).leftCharge (GramAssembly.key 2789).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5410) := by
    have ha : gramCharges (GramAssembly.key 2789).leftCharge (GramAssembly.key 2789).rightCharge = raw42891 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42891Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42891 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2789).leftCharge (GramAssembly.key 2789).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2789).leftCharge (GramAssembly.key 2789).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2789, Integer.Sparse.eval]
  ring

theorem keyMoment2790 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2790) =
      Integer.Sparse.eval keyMomentRow2790 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2790).leftCharge (GramAssembly.key 2790).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3995) := by
    have ha : gramCharges (GramAssembly.key 2790).leftCharge (GramAssembly.key 2790).rightCharge = raw42892 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42892Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42892 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2790).leftCharge (GramAssembly.key 2790).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5473) := by
    have ha : gramCharges (GramAssembly.key 2790).leftCharge (GramAssembly.key 2790).rightCharge = raw42893 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42893Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42893 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2790).leftCharge (GramAssembly.key 2790).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2790).leftCharge (GramAssembly.key 2790).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2790, Integer.Sparse.eval]
  ring

theorem keyMoment2791 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2791) =
      Integer.Sparse.eval keyMomentRow2791 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2791).leftCharge (GramAssembly.key 2791).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3990) := by
    have ha : gramCharges (GramAssembly.key 2791).leftCharge (GramAssembly.key 2791).rightCharge = raw42894 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42894Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42894 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2791).leftCharge (GramAssembly.key 2791).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5424) := by
    have ha : gramCharges (GramAssembly.key 2791).leftCharge (GramAssembly.key 2791).rightCharge = raw42895 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42895Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42895 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2791).leftCharge (GramAssembly.key 2791).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2791).leftCharge (GramAssembly.key 2791).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2791, Integer.Sparse.eval]
  ring

theorem keyMoment2792 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2792) =
      Integer.Sparse.eval keyMomentRow2792 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2792).leftCharge (GramAssembly.key 2792).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3994) := by
    have ha : gramCharges (GramAssembly.key 2792).leftCharge (GramAssembly.key 2792).rightCharge = raw42896 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42896Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42896 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2792).leftCharge (GramAssembly.key 2792).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5478) := by
    have ha : gramCharges (GramAssembly.key 2792).leftCharge (GramAssembly.key 2792).rightCharge = raw42897 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42897Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42897 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2792).leftCharge (GramAssembly.key 2792).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2792).leftCharge (GramAssembly.key 2792).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2792, Integer.Sparse.eval]
  ring

theorem keyMoment2793 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2793) =
      Integer.Sparse.eval keyMomentRow2793 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2793).leftCharge (GramAssembly.key 2793).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3880) := by
    have ha : gramCharges (GramAssembly.key 2793).leftCharge (GramAssembly.key 2793).rightCharge = raw42898 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42898Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42898 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2793).leftCharge (GramAssembly.key 2793).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5445) := by
    have ha : gramCharges (GramAssembly.key 2793).leftCharge (GramAssembly.key 2793).rightCharge = raw42899 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42899Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42899 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2793).leftCharge (GramAssembly.key 2793).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2793).leftCharge (GramAssembly.key 2793).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2793, Integer.Sparse.eval]
  ring

theorem keyMoment2794 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2794) =
      Integer.Sparse.eval keyMomentRow2794 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2794).leftCharge (GramAssembly.key 2794).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3840) := by
    have ha : gramCharges (GramAssembly.key 2794).leftCharge (GramAssembly.key 2794).rightCharge = raw42900 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42900Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42900 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2794).leftCharge (GramAssembly.key 2794).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2794).leftCharge (GramAssembly.key 2794).rightCharge = raw42901 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42901Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42901 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2794).leftCharge (GramAssembly.key 2794).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2794).leftCharge (GramAssembly.key 2794).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2794, Integer.Sparse.eval]
  ring

theorem keyMoment2795 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2795) =
      Integer.Sparse.eval keyMomentRow2795 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2795).leftCharge (GramAssembly.key 2795).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3993) := by
    have ha : gramCharges (GramAssembly.key 2795).leftCharge (GramAssembly.key 2795).rightCharge = raw42902 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42902Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42902 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2795).leftCharge (GramAssembly.key 2795).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5438) := by
    have ha : gramCharges (GramAssembly.key 2795).leftCharge (GramAssembly.key 2795).rightCharge = raw42903 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42903Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42903 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2795).leftCharge (GramAssembly.key 2795).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2795).leftCharge (GramAssembly.key 2795).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2795, Integer.Sparse.eval]
  ring

theorem keyMoment2796 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2796) =
      Integer.Sparse.eval keyMomentRow2796 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2796).leftCharge (GramAssembly.key 2796).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3997) := by
    have ha : gramCharges (GramAssembly.key 2796).leftCharge (GramAssembly.key 2796).rightCharge = raw42904 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42904Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42904 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2796).leftCharge (GramAssembly.key 2796).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5484) := by
    have ha : gramCharges (GramAssembly.key 2796).leftCharge (GramAssembly.key 2796).rightCharge = raw42905 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42905Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42905 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2796).leftCharge (GramAssembly.key 2796).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2796).leftCharge (GramAssembly.key 2796).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2796, Integer.Sparse.eval]
  ring

theorem keyMoment2797 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2797) =
      Integer.Sparse.eval keyMomentRow2797 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2797).leftCharge (GramAssembly.key 2797).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3848) := by
    have ha : gramCharges (GramAssembly.key 2797).leftCharge (GramAssembly.key 2797).rightCharge = raw42906 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42906Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42906 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2797).leftCharge (GramAssembly.key 2797).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2797).leftCharge (GramAssembly.key 2797).rightCharge = raw42907 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42907Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42907 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2797).leftCharge (GramAssembly.key 2797).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2797).leftCharge (GramAssembly.key 2797).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2797, Integer.Sparse.eval]
  ring

theorem keyMoment2798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2798) =
      Integer.Sparse.eval keyMomentRow2798 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2798).leftCharge (GramAssembly.key 2798).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3540) := by
    have ha : gramCharges (GramAssembly.key 2798).leftCharge (GramAssembly.key 2798).rightCharge = raw42908 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42908Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42908 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2798).leftCharge (GramAssembly.key 2798).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2798).leftCharge (GramAssembly.key 2798).rightCharge = raw42909 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42909Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42909 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2798).leftCharge (GramAssembly.key 2798).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2798).leftCharge (GramAssembly.key 2798).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2798, Integer.Sparse.eval]
  ring

theorem keyMoment2799 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2799) =
      Integer.Sparse.eval keyMomentRow2799 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2799).leftCharge (GramAssembly.key 2799).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3227) := by
    have ha : gramCharges (GramAssembly.key 2799).leftCharge (GramAssembly.key 2799).rightCharge = raw42910 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42910Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42910 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2799).leftCharge (GramAssembly.key 2799).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4888) := by
    have ha : gramCharges (GramAssembly.key 2799).leftCharge (GramAssembly.key 2799).rightCharge = raw42911 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42911Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42911 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2799).leftCharge (GramAssembly.key 2799).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2799).leftCharge (GramAssembly.key 2799).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2799, Integer.Sparse.eval]
  ring

theorem keyMoment2800 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2800) =
      Integer.Sparse.eval keyMomentRow2800 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2800).leftCharge (GramAssembly.key 2800).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3065) := by
    have ha : gramCharges (GramAssembly.key 2800).leftCharge (GramAssembly.key 2800).rightCharge = raw42912 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42912Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42912 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2800).leftCharge (GramAssembly.key 2800).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5250) := by
    have ha : gramCharges (GramAssembly.key 2800).leftCharge (GramAssembly.key 2800).rightCharge = raw42913 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42913Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42913 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2800).leftCharge (GramAssembly.key 2800).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2800).leftCharge (GramAssembly.key 2800).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2800, Integer.Sparse.eval]
  ring

theorem keyMoment2801 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2801) =
      Integer.Sparse.eval keyMomentRow2801 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2801).leftCharge (GramAssembly.key 2801).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3977) := by
    have ha : gramCharges (GramAssembly.key 2801).leftCharge (GramAssembly.key 2801).rightCharge = raw42914 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42914Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42914 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2801).leftCharge (GramAssembly.key 2801).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5405) := by
    have ha : gramCharges (GramAssembly.key 2801).leftCharge (GramAssembly.key 2801).rightCharge = raw42915 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42915Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42915 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2801).leftCharge (GramAssembly.key 2801).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2801).leftCharge (GramAssembly.key 2801).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2801, Integer.Sparse.eval]
  ring

theorem keyMoment2802 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2802) =
      Integer.Sparse.eval keyMomentRow2802 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2802).leftCharge (GramAssembly.key 2802).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3976) := by
    have ha : gramCharges (GramAssembly.key 2802).leftCharge (GramAssembly.key 2802).rightCharge = raw42916 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42916Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42916 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2802).leftCharge (GramAssembly.key 2802).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5471) := by
    have ha : gramCharges (GramAssembly.key 2802).leftCharge (GramAssembly.key 2802).rightCharge = raw42917 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42917Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42917 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2802).leftCharge (GramAssembly.key 2802).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2802).leftCharge (GramAssembly.key 2802).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2802, Integer.Sparse.eval]
  ring

theorem keyMoment2803 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2803) =
      Integer.Sparse.eval keyMomentRow2803 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2803).leftCharge (GramAssembly.key 2803).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2698) := by
    have ha : gramCharges (GramAssembly.key 2803).leftCharge (GramAssembly.key 2803).rightCharge = raw42918 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42918Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42918 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2803).leftCharge (GramAssembly.key 2803).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5244) := by
    have ha : gramCharges (GramAssembly.key 2803).leftCharge (GramAssembly.key 2803).rightCharge = raw42919 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42919Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42919 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2803).leftCharge (GramAssembly.key 2803).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2803).leftCharge (GramAssembly.key 2803).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2803, Integer.Sparse.eval]
  ring

theorem keyMoment2804 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2804) =
      Integer.Sparse.eval keyMomentRow2804 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2804).leftCharge (GramAssembly.key 2804).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3078) := by
    have ha : gramCharges (GramAssembly.key 2804).leftCharge (GramAssembly.key 2804).rightCharge = raw42920 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42920Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42920 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2804).leftCharge (GramAssembly.key 2804).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5282) := by
    have ha : gramCharges (GramAssembly.key 2804).leftCharge (GramAssembly.key 2804).rightCharge = raw42921 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42921Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42921 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2804).leftCharge (GramAssembly.key 2804).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2804).leftCharge (GramAssembly.key 2804).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2804, Integer.Sparse.eval]
  ring

theorem keyMoment2805 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2805) =
      Integer.Sparse.eval keyMomentRow2805 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2805).leftCharge (GramAssembly.key 2805).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2706) := by
    have ha : gramCharges (GramAssembly.key 2805).leftCharge (GramAssembly.key 2805).rightCharge = raw42922 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42922Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42922 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2805).leftCharge (GramAssembly.key 2805).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5205) := by
    have ha : gramCharges (GramAssembly.key 2805).leftCharge (GramAssembly.key 2805).rightCharge = raw42923 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42923Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42923 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2805).leftCharge (GramAssembly.key 2805).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2805).leftCharge (GramAssembly.key 2805).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2805, Integer.Sparse.eval]
  ring

theorem keyMoment2806 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2806) =
      Integer.Sparse.eval keyMomentRow2806 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2806).leftCharge (GramAssembly.key 2806).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3954) := by
    have ha : gramCharges (GramAssembly.key 2806).leftCharge (GramAssembly.key 2806).rightCharge = raw42924 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42924Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42924 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2806).leftCharge (GramAssembly.key 2806).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2806).leftCharge (GramAssembly.key 2806).rightCharge = raw42925 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42925Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42925 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2806).leftCharge (GramAssembly.key 2806).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2806).leftCharge (GramAssembly.key 2806).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2806, Integer.Sparse.eval]
  ring

theorem keyMoment2807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2807) =
      Integer.Sparse.eval keyMomentRow2807 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2807).leftCharge (GramAssembly.key 2807).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3569) := by
    have ha : gramCharges (GramAssembly.key 2807).leftCharge (GramAssembly.key 2807).rightCharge = raw42926 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42926Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42926 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2807).leftCharge (GramAssembly.key 2807).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5197) := by
    have ha : gramCharges (GramAssembly.key 2807).leftCharge (GramAssembly.key 2807).rightCharge = raw42927 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42927Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42927 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2807).leftCharge (GramAssembly.key 2807).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2807).leftCharge (GramAssembly.key 2807).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2807, Integer.Sparse.eval]
  ring

theorem keyMoment2808 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2808) =
      Integer.Sparse.eval keyMomentRow2808 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2808).leftCharge (GramAssembly.key 2808).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3537) := by
    have ha : gramCharges (GramAssembly.key 2808).leftCharge (GramAssembly.key 2808).rightCharge = raw42928 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42928Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42928 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2808).leftCharge (GramAssembly.key 2808).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5187) := by
    have ha : gramCharges (GramAssembly.key 2808).leftCharge (GramAssembly.key 2808).rightCharge = raw42929 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42929Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42929 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2808).leftCharge (GramAssembly.key 2808).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2808).leftCharge (GramAssembly.key 2808).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2808, Integer.Sparse.eval]
  ring

theorem keyMoment2809 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2809) =
      Integer.Sparse.eval keyMomentRow2809 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2809).leftCharge (GramAssembly.key 2809).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3972) := by
    have ha : gramCharges (GramAssembly.key 2809).leftCharge (GramAssembly.key 2809).rightCharge = raw42930 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42930Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42930 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2809).leftCharge (GramAssembly.key 2809).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2809).leftCharge (GramAssembly.key 2809).rightCharge = raw42931 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42931Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42931 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2809).leftCharge (GramAssembly.key 2809).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2809).leftCharge (GramAssembly.key 2809).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2809, Integer.Sparse.eval]
  ring

theorem keyMoment2810 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2810) =
      Integer.Sparse.eval keyMomentRow2810 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2810).leftCharge (GramAssembly.key 2810).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3978) := by
    have ha : gramCharges (GramAssembly.key 2810).leftCharge (GramAssembly.key 2810).rightCharge = raw42932 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42932Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42932 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2810).leftCharge (GramAssembly.key 2810).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5480) := by
    have ha : gramCharges (GramAssembly.key 2810).leftCharge (GramAssembly.key 2810).rightCharge = raw42933 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42933Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42933 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2810).leftCharge (GramAssembly.key 2810).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2810).leftCharge (GramAssembly.key 2810).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2810, Integer.Sparse.eval]
  ring

theorem keyMoment2811 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2811) =
      Integer.Sparse.eval keyMomentRow2811 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2811).leftCharge (GramAssembly.key 2811).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3873) := by
    have ha : gramCharges (GramAssembly.key 2811).leftCharge (GramAssembly.key 2811).rightCharge = raw42934 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42934Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42934 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2811).leftCharge (GramAssembly.key 2811).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5421) := by
    have ha : gramCharges (GramAssembly.key 2811).leftCharge (GramAssembly.key 2811).rightCharge = raw42935 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42935Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42935 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2811).leftCharge (GramAssembly.key 2811).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2811).leftCharge (GramAssembly.key 2811).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2811, Integer.Sparse.eval]
  ring

theorem keyMoment2812 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2812) =
      Integer.Sparse.eval keyMomentRow2812 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2812).leftCharge (GramAssembly.key 2812).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3959) := by
    have ha : gramCharges (GramAssembly.key 2812).leftCharge (GramAssembly.key 2812).rightCharge = raw42936 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42936Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42936 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2812).leftCharge (GramAssembly.key 2812).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5446) := by
    have ha : gramCharges (GramAssembly.key 2812).leftCharge (GramAssembly.key 2812).rightCharge = raw42937 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42937Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42937 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2812).leftCharge (GramAssembly.key 2812).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2812).leftCharge (GramAssembly.key 2812).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2812, Integer.Sparse.eval]
  ring

theorem keyMoment2813 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2813) =
      Integer.Sparse.eval keyMomentRow2813 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2813).leftCharge (GramAssembly.key 2813).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3578) := by
    have ha : gramCharges (GramAssembly.key 2813).leftCharge (GramAssembly.key 2813).rightCharge = raw42938 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42938Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42938 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2813).leftCharge (GramAssembly.key 2813).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5199) := by
    have ha : gramCharges (GramAssembly.key 2813).leftCharge (GramAssembly.key 2813).rightCharge = raw42939 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42939Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42939 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2813).leftCharge (GramAssembly.key 2813).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2813).leftCharge (GramAssembly.key 2813).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2813, Integer.Sparse.eval]
  ring

theorem keyMoment2814 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2814) =
      Integer.Sparse.eval keyMomentRow2814 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2814).leftCharge (GramAssembly.key 2814).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3529) := by
    have ha : gramCharges (GramAssembly.key 2814).leftCharge (GramAssembly.key 2814).rightCharge = raw42940 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42940Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42940 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2814).leftCharge (GramAssembly.key 2814).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5185) := by
    have ha : gramCharges (GramAssembly.key 2814).leftCharge (GramAssembly.key 2814).rightCharge = raw42941 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42941Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42941 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2814).leftCharge (GramAssembly.key 2814).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2814).leftCharge (GramAssembly.key 2814).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2814, Integer.Sparse.eval]
  ring

theorem keyMoment2815 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2815) =
      Integer.Sparse.eval keyMomentRow2815 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2815).leftCharge (GramAssembly.key 2815).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3517) := by
    have ha : gramCharges (GramAssembly.key 2815).leftCharge (GramAssembly.key 2815).rightCharge = raw42942 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42942Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42942 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2815).leftCharge (GramAssembly.key 2815).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5138) := by
    have ha : gramCharges (GramAssembly.key 2815).leftCharge (GramAssembly.key 2815).rightCharge = raw42943 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42943Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42943 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2815).leftCharge (GramAssembly.key 2815).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2815).leftCharge (GramAssembly.key 2815).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2815, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2784 : keyMomentRows (2784 : Fin 2886) =
    keyMomentRow2784 := by decide +kernel

theorem keyMomentRowsAt2785 : keyMomentRows (2785 : Fin 2886) =
    keyMomentRow2785 := by decide +kernel

theorem keyMomentRowsAt2786 : keyMomentRows (2786 : Fin 2886) =
    keyMomentRow2786 := by decide +kernel

theorem keyMomentRowsAt2787 : keyMomentRows (2787 : Fin 2886) =
    keyMomentRow2787 := by decide +kernel

theorem keyMomentRowsAt2788 : keyMomentRows (2788 : Fin 2886) =
    keyMomentRow2788 := by decide +kernel

theorem keyMomentRowsAt2789 : keyMomentRows (2789 : Fin 2886) =
    keyMomentRow2789 := by decide +kernel

theorem keyMomentRowsAt2790 : keyMomentRows (2790 : Fin 2886) =
    keyMomentRow2790 := by decide +kernel

theorem keyMomentRowsAt2791 : keyMomentRows (2791 : Fin 2886) =
    keyMomentRow2791 := by decide +kernel

theorem keyMomentRowsAt2792 : keyMomentRows (2792 : Fin 2886) =
    keyMomentRow2792 := by decide +kernel

theorem keyMomentRowsAt2793 : keyMomentRows (2793 : Fin 2886) =
    keyMomentRow2793 := by decide +kernel

theorem keyMomentRowsAt2794 : keyMomentRows (2794 : Fin 2886) =
    keyMomentRow2794 := by decide +kernel

theorem keyMomentRowsAt2795 : keyMomentRows (2795 : Fin 2886) =
    keyMomentRow2795 := by decide +kernel

theorem keyMomentRowsAt2796 : keyMomentRows (2796 : Fin 2886) =
    keyMomentRow2796 := by decide +kernel

theorem keyMomentRowsAt2797 : keyMomentRows (2797 : Fin 2886) =
    keyMomentRow2797 := by decide +kernel

theorem keyMomentRowsAt2798 : keyMomentRows (2798 : Fin 2886) =
    keyMomentRow2798 := by decide +kernel

theorem keyMomentRowsAt2799 : keyMomentRows (2799 : Fin 2886) =
    keyMomentRow2799 := by decide +kernel

theorem keyMomentRowsAt2800 : keyMomentRows (2800 : Fin 2886) =
    keyMomentRow2800 := by decide +kernel

theorem keyMomentRowsAt2801 : keyMomentRows (2801 : Fin 2886) =
    keyMomentRow2801 := by decide +kernel

theorem keyMomentRowsAt2802 : keyMomentRows (2802 : Fin 2886) =
    keyMomentRow2802 := by decide +kernel

theorem keyMomentRowsAt2803 : keyMomentRows (2803 : Fin 2886) =
    keyMomentRow2803 := by decide +kernel

theorem keyMomentRowsAt2804 : keyMomentRows (2804 : Fin 2886) =
    keyMomentRow2804 := by decide +kernel

theorem keyMomentRowsAt2805 : keyMomentRows (2805 : Fin 2886) =
    keyMomentRow2805 := by decide +kernel

theorem keyMomentRowsAt2806 : keyMomentRows (2806 : Fin 2886) =
    keyMomentRow2806 := by decide +kernel

theorem keyMomentRowsAt2807 : keyMomentRows (2807 : Fin 2886) =
    keyMomentRow2807 := by decide +kernel

theorem keyMomentRowsAt2808 : keyMomentRows (2808 : Fin 2886) =
    keyMomentRow2808 := by decide +kernel

theorem keyMomentRowsAt2809 : keyMomentRows (2809 : Fin 2886) =
    keyMomentRow2809 := by decide +kernel

theorem keyMomentRowsAt2810 : keyMomentRows (2810 : Fin 2886) =
    keyMomentRow2810 := by decide +kernel

theorem keyMomentRowsAt2811 : keyMomentRows (2811 : Fin 2886) =
    keyMomentRow2811 := by decide +kernel

theorem keyMomentRowsAt2812 : keyMomentRows (2812 : Fin 2886) =
    keyMomentRow2812 := by decide +kernel

theorem keyMomentRowsAt2813 : keyMomentRows (2813 : Fin 2886) =
    keyMomentRow2813 := by decide +kernel

theorem keyMomentRowsAt2814 : keyMomentRows (2814 : Fin 2886) =
    keyMomentRow2814 := by decide +kernel

theorem keyMomentRowsAt2815 : keyMomentRows (2815 : Fin 2886) =
    keyMomentRow2815 := by decide +kernel

theorem keyMomentChunkSound87_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 87) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2784 ∨ k.val = 2785 ∨ k.val = 2786 ∨ k.val = 2787 ∨ k.val = 2788 ∨ k.val = 2789 ∨ k.val = 2790 ∨ k.val = 2791 ∨ k.val = 2792 ∨ k.val = 2793 ∨ k.val = 2794 ∨ k.val = 2795 ∨ k.val = 2796 ∨ k.val = 2797 ∨ k.val = 2798 ∨ k.val = 2799 ∨ k.val = 2800 ∨ k.val = 2801 ∨ k.val = 2802 ∨ k.val = 2803 ∨ k.val = 2804 ∨ k.val = 2805 ∨ k.val = 2806 ∨ k.val = 2807 ∨ k.val = 2808 ∨ k.val = 2809 ∨ k.val = 2810 ∨ k.val = 2811 ∨ k.val = 2812 ∨ k.val = 2813 ∨ k.val = 2814 ∨ k.val = 2815 := by omega
  rcases heq with h2784 | h2785 | h2786 | h2787 | h2788 | h2789 | h2790 | h2791 | h2792 | h2793 | h2794 | h2795 | h2796 | h2797 | h2798 | h2799 | h2800 | h2801 | h2802 | h2803 | h2804 | h2805 | h2806 | h2807 | h2808 | h2809 | h2810 | h2811 | h2812 | h2813 | h2814 | h2815
  · have he : k = (2784 : Fin 2886) := Fin.ext h2784
    subst k
    rw [keyMomentRowsAt2784]
    exact keyMoment2784 B hB
  · have he : k = (2785 : Fin 2886) := Fin.ext h2785
    subst k
    rw [keyMomentRowsAt2785]
    exact keyMoment2785 B hB
  · have he : k = (2786 : Fin 2886) := Fin.ext h2786
    subst k
    rw [keyMomentRowsAt2786]
    exact keyMoment2786 B hB
  · have he : k = (2787 : Fin 2886) := Fin.ext h2787
    subst k
    rw [keyMomentRowsAt2787]
    exact keyMoment2787 B hB
  · have he : k = (2788 : Fin 2886) := Fin.ext h2788
    subst k
    rw [keyMomentRowsAt2788]
    exact keyMoment2788 B hB
  · have he : k = (2789 : Fin 2886) := Fin.ext h2789
    subst k
    rw [keyMomentRowsAt2789]
    exact keyMoment2789 B hB
  · have he : k = (2790 : Fin 2886) := Fin.ext h2790
    subst k
    rw [keyMomentRowsAt2790]
    exact keyMoment2790 B hB
  · have he : k = (2791 : Fin 2886) := Fin.ext h2791
    subst k
    rw [keyMomentRowsAt2791]
    exact keyMoment2791 B hB
  · have he : k = (2792 : Fin 2886) := Fin.ext h2792
    subst k
    rw [keyMomentRowsAt2792]
    exact keyMoment2792 B hB
  · have he : k = (2793 : Fin 2886) := Fin.ext h2793
    subst k
    rw [keyMomentRowsAt2793]
    exact keyMoment2793 B hB
  · have he : k = (2794 : Fin 2886) := Fin.ext h2794
    subst k
    rw [keyMomentRowsAt2794]
    exact keyMoment2794 B hB
  · have he : k = (2795 : Fin 2886) := Fin.ext h2795
    subst k
    rw [keyMomentRowsAt2795]
    exact keyMoment2795 B hB
  · have he : k = (2796 : Fin 2886) := Fin.ext h2796
    subst k
    rw [keyMomentRowsAt2796]
    exact keyMoment2796 B hB
  · have he : k = (2797 : Fin 2886) := Fin.ext h2797
    subst k
    rw [keyMomentRowsAt2797]
    exact keyMoment2797 B hB
  · have he : k = (2798 : Fin 2886) := Fin.ext h2798
    subst k
    rw [keyMomentRowsAt2798]
    exact keyMoment2798 B hB
  · have he : k = (2799 : Fin 2886) := Fin.ext h2799
    subst k
    rw [keyMomentRowsAt2799]
    exact keyMoment2799 B hB
  · have he : k = (2800 : Fin 2886) := Fin.ext h2800
    subst k
    rw [keyMomentRowsAt2800]
    exact keyMoment2800 B hB
  · have he : k = (2801 : Fin 2886) := Fin.ext h2801
    subst k
    rw [keyMomentRowsAt2801]
    exact keyMoment2801 B hB
  · have he : k = (2802 : Fin 2886) := Fin.ext h2802
    subst k
    rw [keyMomentRowsAt2802]
    exact keyMoment2802 B hB
  · have he : k = (2803 : Fin 2886) := Fin.ext h2803
    subst k
    rw [keyMomentRowsAt2803]
    exact keyMoment2803 B hB
  · have he : k = (2804 : Fin 2886) := Fin.ext h2804
    subst k
    rw [keyMomentRowsAt2804]
    exact keyMoment2804 B hB
  · have he : k = (2805 : Fin 2886) := Fin.ext h2805
    subst k
    rw [keyMomentRowsAt2805]
    exact keyMoment2805 B hB
  · have he : k = (2806 : Fin 2886) := Fin.ext h2806
    subst k
    rw [keyMomentRowsAt2806]
    exact keyMoment2806 B hB
  · have he : k = (2807 : Fin 2886) := Fin.ext h2807
    subst k
    rw [keyMomentRowsAt2807]
    exact keyMoment2807 B hB
  · have he : k = (2808 : Fin 2886) := Fin.ext h2808
    subst k
    rw [keyMomentRowsAt2808]
    exact keyMoment2808 B hB
  · have he : k = (2809 : Fin 2886) := Fin.ext h2809
    subst k
    rw [keyMomentRowsAt2809]
    exact keyMoment2809 B hB
  · have he : k = (2810 : Fin 2886) := Fin.ext h2810
    subst k
    rw [keyMomentRowsAt2810]
    exact keyMoment2810 B hB
  · have he : k = (2811 : Fin 2886) := Fin.ext h2811
    subst k
    rw [keyMomentRowsAt2811]
    exact keyMoment2811 B hB
  · have he : k = (2812 : Fin 2886) := Fin.ext h2812
    subst k
    rw [keyMomentRowsAt2812]
    exact keyMoment2812 B hB
  · have he : k = (2813 : Fin 2886) := Fin.ext h2813
    subst k
    rw [keyMomentRowsAt2813]
    exact keyMoment2813 B hB
  · have he : k = (2814 : Fin 2886) := Fin.ext h2814
    subst k
    rw [keyMomentRowsAt2814]
    exact keyMoment2814 B hB
  · have he : k = (2815 : Fin 2886) := Fin.ext h2815
    subst k
    rw [keyMomentRowsAt2815]
    exact keyMoment2815 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound87_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound87_e_oai
