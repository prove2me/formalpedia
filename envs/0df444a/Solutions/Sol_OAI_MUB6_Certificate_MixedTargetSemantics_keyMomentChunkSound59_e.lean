-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound59_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:58:41.390145+00:00
-- url     : https://prove2.me/submissions/aed27a71-bbbf-4c94-93aa-3be85e421a46

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

theorem canonical41301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41301 raw41301Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw41301 raw41301Labels = mixedMoment B raw41301step0 raw41301step0Labels := by
      have hz : ∀ j, raw41301 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41301step0 = (fun i j => raw41301 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41301step0 raw41301; decide +kernel
      have hl : raw41301step0Labels = raw41301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41301 raw41301Labels permutation346 hz
    mixedMoment B raw41301step0 raw41301step0Labels = mixedMoment B raw41301step1 raw41301step1Labels := by
      have ha : raw41301step1 = (fun i j => raw41301step0 (permutation66 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41301step1 raw41301step0; decide +kernel
      have hl : raw41301step1Labels = raw41301step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41301step0 raw41301step0Labels permutation66 permutation6
    mixedMoment B raw41301step1 raw41301step1Labels = mixedMoment B raw41301step2 raw41301step2Labels := by
      have ha : raw41301step2 = -raw41301step1 := by apply Matrix.ext; change ∀ i j, raw41301step2 i j = -(raw41301step1 i j); unfold raw41301step2 raw41301step1; decide +kernel
      have hl : raw41301step2Labels = raw41301step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2512 node2512Labels := by rfl

theorem canonical41302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41302 raw41302Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw41302 raw41302Labels = mixedMoment B raw41302step0 raw41302step0Labels := by
      have hz : ∀ j, raw41302 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41302step0 = (fun i j => raw41302 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41302step0 raw41302; decide +kernel
      have hl : raw41302step0Labels = raw41302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41302 raw41302Labels permutation520 hz
    mixedMoment B raw41302step0 raw41302step0Labels = mixedMoment B raw41302step1 raw41302step1Labels := by
      have hz : ∀ j, raw41302step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41302step1 = (fun i j => raw41302step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41302step1 raw41302step0; decide +kernel
      have hl : raw41302step1Labels = raw41302step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41302step0 raw41302step0Labels permutation104 hz
    mixedMoment B raw41302step1 raw41302step1Labels = mixedMoment B raw41302step2 raw41302step2Labels := by
      have ha : raw41302step2 = (fun i j => raw41302step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41302step2 raw41302step1; decide +kernel
      have hl : raw41302step2Labels = raw41302step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41302step1 raw41302step1Labels permutation16 permutation6
    mixedMoment B raw41302step2 raw41302step2Labels = mixedMoment B raw41302step3 raw41302step3Labels := by
      have ha : raw41302step3 = -raw41302step2 := by apply Matrix.ext; change ∀ i j, raw41302step3 i j = -(raw41302step2 i j); unfold raw41302step3 raw41302step2; decide +kernel
      have hl : raw41302step3Labels = raw41302step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1087 node1087Labels := by rfl

theorem canonical41303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41303 raw41303Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw41303 raw41303Labels = mixedMoment B raw41303step0 raw41303step0Labels := by
      have hz : ∀ j, raw41303 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41303step0 = (fun i j => raw41303 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41303step0 raw41303; decide +kernel
      have hl : raw41303step0Labels = raw41303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41303 raw41303Labels permutation520 hz
    mixedMoment B raw41303step0 raw41303step0Labels = mixedMoment B raw41303step1 raw41303step1Labels := by
      have hz : ∀ j, raw41303step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41303step1 = (fun i j => raw41303step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41303step1 raw41303step0; decide +kernel
      have hl : raw41303step1Labels = raw41303step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41303step0 raw41303step0Labels permutation104 hz
    mixedMoment B raw41303step1 raw41303step1Labels = mixedMoment B raw41303step2 raw41303step2Labels := by
      have hz : ∀ j, raw41303step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41303step2 = (fun i j => raw41303step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41303step2 raw41303step1; decide +kernel
      have hl : raw41303step2Labels = raw41303step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41303step1 raw41303step1Labels permutation20 hz
    mixedMoment B raw41303step2 raw41303step2Labels = mixedMoment B raw41303step3 raw41303step3Labels := by
      have ha : raw41303step3 = (fun i j => raw41303step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41303step3 raw41303step2; decide +kernel
      have hl : raw41303step3Labels = raw41303step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41303step2 raw41303step2Labels permutation4 permutation6
    mixedMoment B raw41303step3 raw41303step3Labels = mixedMoment B raw41303step4 raw41303step4Labels := by
      have ha : raw41303step4 = -raw41303step3 := by apply Matrix.ext; change ∀ i j, raw41303step4 i j = -(raw41303step3 i j); unfold raw41303step4 raw41303step3; decide +kernel
      have hl : raw41303step4Labels = raw41303step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1091 node1091Labels := by rfl

theorem canonical41304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41304 raw41304Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw41304 raw41304Labels = mixedMoment B raw41304step0 raw41304step0Labels := by
      have hz : ∀ j, raw41304 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41304step0 = (fun i j => raw41304 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41304step0 raw41304; decide +kernel
      have hl : raw41304step0Labels = raw41304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41304 raw41304Labels permutation520 hz
    mixedMoment B raw41304step0 raw41304step0Labels = mixedMoment B raw41304step1 raw41304step1Labels := by
      have hz : ∀ j, raw41304step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41304step1 = (fun i j => raw41304step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41304step1 raw41304step0; decide +kernel
      have hl : raw41304step1Labels = raw41304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41304step0 raw41304step0Labels permutation104 hz
    mixedMoment B raw41304step1 raw41304step1Labels = mixedMoment B raw41304step2 raw41304step2Labels := by
      have hz : ∀ i, raw41304step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw41304step2 = (fun i j => raw41304step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw41304step2 raw41304step1; decide +kernel
      have hl : raw41304step2Labels = (fun j => raw41304step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw41304step1 raw41304step1Labels permutation6 hz
    mixedMoment B raw41304step2 raw41304step2Labels = mixedMoment B raw41304step3 raw41304step3Labels := by
      have ha : raw41304step3 = (fun i j => raw41304step2 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw41304step3 raw41304step2; decide +kernel
      have hl : raw41304step3Labels = raw41304step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41304step2 raw41304step2Labels permutation26 permutation0
    mixedMoment B raw41304step3 raw41304step3Labels = mixedMoment B raw41304step4 raw41304step4Labels := by
      have ha : raw41304step4 = -raw41304step3 := by apply Matrix.ext; change ∀ i j, raw41304step4 i j = -(raw41304step3 i j); unfold raw41304step4 raw41304step3; decide +kernel
      have hl : raw41304step4Labels = raw41304step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical41305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41305 raw41305Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw41305 raw41305Labels = mixedMoment B raw41305step0 raw41305step0Labels := by
      have hz : ∀ j, raw41305 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41305step0 = (fun i j => raw41305 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41305step0 raw41305; decide +kernel
      have hl : raw41305step0Labels = raw41305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41305 raw41305Labels permutation434 hz
    mixedMoment B raw41305step0 raw41305step0Labels = mixedMoment B raw41305step1 raw41305step1Labels := by
      have ha : raw41305step1 = (fun i j => raw41305step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41305step1 raw41305step0; decide +kernel
      have hl : raw41305step1Labels = raw41305step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41305step0 raw41305step0Labels permutation146 permutation3
    mixedMoment B raw41305step1 raw41305step1Labels = mixedMoment B raw41305step2 raw41305step2Labels := by
      have ha : raw41305step2 = -raw41305step1 := by apply Matrix.ext; change ∀ i j, raw41305step2 i j = -(raw41305step1 i j); unfold raw41305step2 raw41305step1; decide +kernel
      have hl : raw41305step2Labels = raw41305step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2741 node2741Labels := by rfl

theorem canonical41306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41306 raw41306Labels = mixedMoment B node3962 node3962Labels := by
  calc
    mixedMoment B raw41306 raw41306Labels = mixedMoment B raw41306step0 raw41306step0Labels := by
      have hz : ∀ j, raw41306 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41306step0 = (fun i j => raw41306 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41306step0 raw41306; decide +kernel
      have hl : raw41306step0Labels = raw41306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41306 raw41306Labels permutation434 hz
    mixedMoment B raw41306step0 raw41306step0Labels = mixedMoment B raw41306step1 raw41306step1Labels := by
      have ha : raw41306step1 = (fun i j => raw41306step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41306step1 raw41306step0; decide +kernel
      have hl : raw41306step1Labels = raw41306step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41306step0 raw41306step0Labels permutation146 permutation3
    mixedMoment B raw41306step1 raw41306step1Labels = mixedMoment B raw41306step2 raw41306step2Labels := by
      have ha : raw41306step2 = -raw41306step1 := by apply Matrix.ext; change ∀ i j, raw41306step2 i j = -(raw41306step1 i j); unfold raw41306step2 raw41306step1; decide +kernel
      have hl : raw41306step2Labels = raw41306step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3962 node3962Labels := by rfl

theorem canonical41307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41307 raw41307Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw41307 raw41307Labels = mixedMoment B raw41307step0 raw41307step0Labels := by
      have hz : ∀ j, raw41307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41307step0 = (fun i j => raw41307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41307step0 raw41307; decide +kernel
      have hl : raw41307step0Labels = raw41307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41307 raw41307Labels permutation434 hz
    mixedMoment B raw41307step0 raw41307step0Labels = mixedMoment B raw41307step1 raw41307step1Labels := by
      have ha : raw41307step1 = (fun i j => raw41307step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41307step1 raw41307step0; decide +kernel
      have hl : raw41307step1Labels = raw41307step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41307step0 raw41307step0Labels permutation104 permutation6
    mixedMoment B raw41307step1 raw41307step1Labels = mixedMoment B raw41307step2 raw41307step2Labels := by
      have ha : raw41307step2 = -raw41307step1 := by apply Matrix.ext; change ∀ i j, raw41307step2 i j = -(raw41307step1 i j); unfold raw41307step2 raw41307step1; decide +kernel
      have hl : raw41307step2Labels = raw41307step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3619 node3619Labels := by rfl

theorem canonical41308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41308 raw41308Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw41308 raw41308Labels = mixedMoment B raw41308step0 raw41308step0Labels := by
      have ha : raw41308step0 = (fun i j => raw41308 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41308step0 raw41308; decide +kernel
      have hl : raw41308step0Labels = raw41308Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41308 raw41308Labels permutation683 permutation3
    mixedMoment B raw41308step0 raw41308step0Labels = mixedMoment B raw41308step1 raw41308step1Labels := by
      have ha : raw41308step1 = -raw41308step0 := by apply Matrix.ext; change ∀ i j, raw41308step1 i j = -(raw41308step0 i j); unfold raw41308step1 raw41308step0; decide +kernel
      have hl : raw41308step1Labels = raw41308step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4025 node4025Labels := by rfl

theorem canonical41309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41309 raw41309Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw41309 raw41309Labels = mixedMoment B raw41309step0 raw41309step0Labels := by
      have hz : ∀ j, raw41309 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41309step0 = (fun i j => raw41309 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41309step0 raw41309; decide +kernel
      have hl : raw41309step0Labels = raw41309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41309 raw41309Labels permutation520 hz
    mixedMoment B raw41309step0 raw41309step0Labels = mixedMoment B raw41309step1 raw41309step1Labels := by
      have ha : raw41309step1 = (fun i j => raw41309step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41309step1 raw41309step0; decide +kernel
      have hl : raw41309step1Labels = raw41309step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41309step0 raw41309step0Labels permutation150 permutation3
    mixedMoment B raw41309step1 raw41309step1Labels = mixedMoment B raw41309step2 raw41309step2Labels := by
      have ha : raw41309step2 = -raw41309step1 := by apply Matrix.ext; change ∀ i j, raw41309step2 i j = -(raw41309step1 i j); unfold raw41309step2 raw41309step1; decide +kernel
      have hl : raw41309step2Labels = raw41309step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical41310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41310 raw41310Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw41310 raw41310Labels = mixedMoment B raw41310step0 raw41310step0Labels := by
      have ha : raw41310step0 = (fun i j => raw41310 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41310step0 raw41310; decide +kernel
      have hl : raw41310step0Labels = raw41310Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41310 raw41310Labels permutation687 permutation3
    mixedMoment B raw41310step0 raw41310step0Labels = mixedMoment B raw41310step1 raw41310step1Labels := by
      have ha : raw41310step1 = -raw41310step0 := by apply Matrix.ext; change ∀ i j, raw41310step1 i j = -(raw41310step0 i j); unfold raw41310step1 raw41310step0; decide +kernel
      have hl : raw41310step1Labels = raw41310step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical41311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41311 raw41311Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw41311 raw41311Labels = mixedMoment B raw41311step0 raw41311step0Labels := by
      have ha : raw41311step0 = (fun i j => raw41311 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41311step0 raw41311; decide +kernel
      have hl : raw41311step0Labels = raw41311Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41311 raw41311Labels permutation687 permutation3
    mixedMoment B raw41311step0 raw41311step0Labels = mixedMoment B raw41311step1 raw41311step1Labels := by
      have ha : raw41311step1 = -raw41311step0 := by apply Matrix.ext; change ∀ i j, raw41311step1 i j = -(raw41311step0 i j); unfold raw41311step1 raw41311step0; decide +kernel
      have hl : raw41311step1Labels = raw41311step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical41312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41312 raw41312Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw41312 raw41312Labels = mixedMoment B raw41312step0 raw41312step0Labels := by
      have ha : raw41312step0 = (fun i j => raw41312 (permutation541 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41312step0 raw41312; decide +kernel
      have hl : raw41312step0Labels = raw41312Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41312 raw41312Labels permutation541 permutation6
    mixedMoment B raw41312step0 raw41312step0Labels = mixedMoment B raw41312step1 raw41312step1Labels := by
      have ha : raw41312step1 = -raw41312step0 := by apply Matrix.ext; change ∀ i j, raw41312step1 i j = -(raw41312step0 i j); unfold raw41312step1 raw41312step0; decide +kernel
      have hl : raw41312step1Labels = raw41312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3526 node3526Labels := by rfl

theorem canonical41313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41313 raw41313Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw41313 raw41313Labels = mixedMoment B raw41313step0 raw41313step0Labels := by
      have hz : ∀ j, raw41313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41313step0 = (fun i j => raw41313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41313step0 raw41313; decide +kernel
      have hl : raw41313step0Labels = raw41313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41313 raw41313Labels permutation434 hz
    mixedMoment B raw41313step0 raw41313step0Labels = mixedMoment B raw41313step1 raw41313step1Labels := by
      have ha : raw41313step1 = (fun i j => raw41313step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41313step1 raw41313step0; decide +kernel
      have hl : raw41313step1Labels = raw41313step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41313step0 raw41313step0Labels permutation128 permutation6
    _ = mixedMoment B node3075 node3075Labels := by rfl

theorem canonical41314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41314 raw41314Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw41314 raw41314Labels = mixedMoment B raw41314step0 raw41314step0Labels := by
      have ha : raw41314step0 = (fun i j => raw41314 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41314step0 raw41314; decide +kernel
      have hl : raw41314step0Labels = raw41314Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41314 raw41314Labels permutation590 permutation6
    _ = mixedMoment B node3074 node3074Labels := by rfl

theorem canonical41315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41315 raw41315Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw41315 raw41315Labels = mixedMoment B raw41315step0 raw41315step0Labels := by
      have hz : ∀ j, raw41315 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41315step0 = (fun i j => raw41315 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41315step0 raw41315; decide +kernel
      have hl : raw41315step0Labels = raw41315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41315 raw41315Labels permutation520 hz
    mixedMoment B raw41315step0 raw41315step0Labels = mixedMoment B raw41315step1 raw41315step1Labels := by
      have ha : raw41315step1 = (fun i j => raw41315step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41315step1 raw41315step0; decide +kernel
      have hl : raw41315step1Labels = raw41315step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41315step0 raw41315step0Labels permutation150 permutation3
    mixedMoment B raw41315step1 raw41315step1Labels = mixedMoment B raw41315step2 raw41315step2Labels := by
      have ha : raw41315step2 = -raw41315step1 := by apply Matrix.ext; change ∀ i j, raw41315step2 i j = -(raw41315step1 i j); unfold raw41315step2 raw41315step1; decide +kernel
      have hl : raw41315step2Labels = raw41315step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical41316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41316 raw41316Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw41316 raw41316Labels = mixedMoment B raw41316step0 raw41316step0Labels := by
      have ha : raw41316step0 = (fun i j => raw41316 (permutation399 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41316step0 raw41316; decide +kernel
      have hl : raw41316step0Labels = raw41316Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41316 raw41316Labels permutation399 permutation6
    mixedMoment B raw41316step0 raw41316step0Labels = mixedMoment B raw41316step1 raw41316step1Labels := by
      have ha : raw41316step1 = -raw41316step0 := by apply Matrix.ext; change ∀ i j, raw41316step1 i j = -(raw41316step0 i j); unfold raw41316step1 raw41316step0; decide +kernel
      have hl : raw41316step1Labels = raw41316step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3954 node3954Labels := by rfl

theorem canonical41317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41317 raw41317Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw41317 raw41317Labels = mixedMoment B raw41317step0 raw41317step0Labels := by
      have hz : ∀ j, raw41317 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41317step0 = (fun i j => raw41317 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41317step0 raw41317; decide +kernel
      have hl : raw41317step0Labels = raw41317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41317 raw41317Labels permutation434 hz
    mixedMoment B raw41317step0 raw41317step0Labels = mixedMoment B raw41317step1 raw41317step1Labels := by
      have ha : raw41317step1 = (fun i j => raw41317step0 (permutation129 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41317step1 raw41317step0; decide +kernel
      have hl : raw41317step1Labels = raw41317step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41317step0 raw41317step0Labels permutation129 permutation6
    _ = mixedMoment B node3078 node3078Labels := by rfl

theorem canonical41318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41318 raw41318Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw41318 raw41318Labels = mixedMoment B raw41318step0 raw41318step0Labels := by
      have hz : ∀ j, raw41318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41318step0 = (fun i j => raw41318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41318step0 raw41318; decide +kernel
      have hl : raw41318step0Labels = raw41318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41318 raw41318Labels permutation434 hz
    mixedMoment B raw41318step0 raw41318step0Labels = mixedMoment B raw41318step1 raw41318step1Labels := by
      have hz : ∀ j, raw41318step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41318step1 = (fun i j => raw41318step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41318step1 raw41318step0; decide +kernel
      have hl : raw41318step1Labels = raw41318step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41318step0 raw41318step0Labels permutation80 hz
    mixedMoment B raw41318step1 raw41318step1Labels = mixedMoment B raw41318step2 raw41318step2Labels := by
      have ha : raw41318step2 = (fun i j => raw41318step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41318step2 raw41318step1; decide +kernel
      have hl : raw41318step2Labels = raw41318step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41318step1 raw41318step1Labels permutation20 permutation6
    mixedMoment B raw41318step2 raw41318step2Labels = mixedMoment B raw41318step3 raw41318step3Labels := by
      have ha : raw41318step3 = -raw41318step2 := by apply Matrix.ext; change ∀ i j, raw41318step3 i j = -(raw41318step2 i j); unfold raw41318step3 raw41318step2; decide +kernel
      have hl : raw41318step3Labels = raw41318step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2247 node2247Labels := by rfl

theorem canonical41319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41319 raw41319Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw41319 raw41319Labels = mixedMoment B raw41319step0 raw41319step0Labels := by
      have hz : ∀ j, raw41319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41319step0 = (fun i j => raw41319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41319step0 raw41319; decide +kernel
      have hl : raw41319step0Labels = raw41319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41319 raw41319Labels permutation434 hz
    mixedMoment B raw41319step0 raw41319step0Labels = mixedMoment B raw41319step1 raw41319step1Labels := by
      have hz : ∀ j, raw41319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41319step1 = (fun i j => raw41319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41319step1 raw41319step0; decide +kernel
      have hl : raw41319step1Labels = raw41319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41319step0 raw41319step0Labels permutation80 hz
    mixedMoment B raw41319step1 raw41319step1Labels = mixedMoment B raw41319step2 raw41319step2Labels := by
      have ha : raw41319step2 = (fun i j => raw41319step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41319step2 raw41319step1; decide +kernel
      have hl : raw41319step2Labels = raw41319step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41319step1 raw41319step1Labels permutation26 permutation6
    mixedMoment B raw41319step2 raw41319step2Labels = mixedMoment B raw41319step3 raw41319step3Labels := by
      have ha : raw41319step3 = -raw41319step2 := by apply Matrix.ext; change ∀ i j, raw41319step3 i j = -(raw41319step2 i j); unfold raw41319step3 raw41319step2; decide +kernel
      have hl : raw41319step3Labels = raw41319step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3623 node3623Labels := by rfl

theorem canonical41320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41320 raw41320Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw41320 raw41320Labels = mixedMoment B raw41320step0 raw41320step0Labels := by
      have hz : ∀ j, raw41320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41320step0 = (fun i j => raw41320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41320step0 raw41320; decide +kernel
      have hl : raw41320step0Labels = raw41320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41320 raw41320Labels permutation346 hz
    mixedMoment B raw41320step0 raw41320step0Labels = mixedMoment B raw41320step1 raw41320step1Labels := by
      have ha : raw41320step1 = (fun i j => raw41320step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41320step1 raw41320step0; decide +kernel
      have hl : raw41320step1Labels = raw41320step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41320step0 raw41320step0Labels permutation128 permutation6
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical41321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41321 raw41321Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw41321 raw41321Labels = mixedMoment B raw41321step0 raw41321step0Labels := by
      have hz : ∀ j, raw41321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41321step0 = (fun i j => raw41321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41321step0 raw41321; decide +kernel
      have hl : raw41321step0Labels = raw41321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41321 raw41321Labels permutation346 hz
    mixedMoment B raw41321step0 raw41321step0Labels = mixedMoment B raw41321step1 raw41321step1Labels := by
      have ha : raw41321step1 = (fun i j => raw41321step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41321step1 raw41321step0; decide +kernel
      have hl : raw41321step1Labels = raw41321step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41321step0 raw41321step0Labels permutation104 permutation6
    _ = mixedMoment B node4010 node4010Labels := by rfl

theorem canonical41322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41322 raw41322Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw41322 raw41322Labels = mixedMoment B raw41322step0 raw41322step0Labels := by
      have hz : ∀ j, raw41322 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41322step0 = (fun i j => raw41322 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41322step0 raw41322; decide +kernel
      have hl : raw41322step0Labels = raw41322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41322 raw41322Labels permutation520 hz
    mixedMoment B raw41322step0 raw41322step0Labels = mixedMoment B raw41322step1 raw41322step1Labels := by
      have ha : raw41322step1 = (fun i j => raw41322step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41322step1 raw41322step0; decide +kernel
      have hl : raw41322step1Labels = raw41322step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41322step0 raw41322step0Labels permutation149 permutation3
    mixedMoment B raw41322step1 raw41322step1Labels = mixedMoment B raw41322step2 raw41322step2Labels := by
      have ha : raw41322step2 = -raw41322step1 := by apply Matrix.ext; change ∀ i j, raw41322step2 i j = -(raw41322step1 i j); unfold raw41322step2 raw41322step1; decide +kernel
      have hl : raw41322step2Labels = raw41322step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical41323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41323 raw41323Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw41323 raw41323Labels = mixedMoment B raw41323step0 raw41323step0Labels := by
      have ha : raw41323step0 = (fun i j => raw41323 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41323step0 raw41323; decide +kernel
      have hl : raw41323step0Labels = raw41323Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41323 raw41323Labels permutation686 permutation3
    mixedMoment B raw41323step0 raw41323step0Labels = mixedMoment B raw41323step1 raw41323step1Labels := by
      have ha : raw41323step1 = -raw41323step0 := by apply Matrix.ext; change ∀ i j, raw41323step1 i j = -(raw41323step0 i j); unfold raw41323step1 raw41323step0; decide +kernel
      have hl : raw41323step1Labels = raw41323step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2730 node2730Labels := by rfl

theorem canonical41324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41324 raw41324Labels = mixedMoment B node3043 node3043Labels := by
  calc
    mixedMoment B raw41324 raw41324Labels = mixedMoment B raw41324step0 raw41324step0Labels := by
      have ha : raw41324step0 = (fun i j => raw41324 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41324step0 raw41324; decide +kernel
      have hl : raw41324step0Labels = raw41324Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41324 raw41324Labels permutation686 permutation3
    mixedMoment B raw41324step0 raw41324step0Labels = mixedMoment B raw41324step1 raw41324step1Labels := by
      have ha : raw41324step1 = -raw41324step0 := by apply Matrix.ext; change ∀ i j, raw41324step1 i j = -(raw41324step0 i j); unfold raw41324step1 raw41324step0; decide +kernel
      have hl : raw41324step1Labels = raw41324step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3043 node3043Labels := by rfl

theorem canonical41325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41325 raw41325Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw41325 raw41325Labels = mixedMoment B raw41325step0 raw41325step0Labels := by
      have ha : raw41325step0 = (fun i j => raw41325 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41325step0 raw41325; decide +kernel
      have hl : raw41325step0Labels = raw41325Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41325 raw41325Labels permutation686 permutation3
    mixedMoment B raw41325step0 raw41325step0Labels = mixedMoment B raw41325step1 raw41325step1Labels := by
      have ha : raw41325step1 = -raw41325step0 := by apply Matrix.ext; change ∀ i j, raw41325step1 i j = -(raw41325step0 i j); unfold raw41325step1 raw41325step0; decide +kernel
      have hl : raw41325step1Labels = raw41325step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3812 node3812Labels := by rfl

theorem canonical41326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41326 raw41326Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw41326 raw41326Labels = mixedMoment B raw41326step0 raw41326step0Labels := by
      have ha : raw41326step0 = (fun i j => raw41326 (permutation505 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41326step0 raw41326; decide +kernel
      have hl : raw41326step0Labels = raw41326Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41326 raw41326Labels permutation505 permutation6
    _ = mixedMoment B node3874 node3874Labels := by rfl

theorem canonical41327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41327 raw41327Labels = mixedMoment B node3488 node3488Labels := by
  calc
    mixedMoment B raw41327 raw41327Labels = mixedMoment B raw41327step0 raw41327step0Labels := by
      have ha : raw41327step0 = (fun i j => raw41327 (permutation531 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41327step0 raw41327; decide +kernel
      have hl : raw41327step0Labels = raw41327Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41327 raw41327Labels permutation531 permutation6
    mixedMoment B raw41327step0 raw41327step0Labels = mixedMoment B raw41327step1 raw41327step1Labels := by
      have ha : raw41327step1 = -raw41327step0 := by apply Matrix.ext; change ∀ i j, raw41327step1 i j = -(raw41327step0 i j); unfold raw41327step1 raw41327step0; decide +kernel
      have hl : raw41327step1Labels = raw41327step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3488 node3488Labels := by rfl

theorem canonical41328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41328 raw41328Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw41328 raw41328Labels = mixedMoment B raw41328step0 raw41328step0Labels := by
      have ha : raw41328step0 = (fun i j => raw41328 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41328step0 raw41328; decide +kernel
      have hl : raw41328step0Labels = raw41328Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41328 raw41328Labels permutation662 permutation3
    mixedMoment B raw41328step0 raw41328step0Labels = mixedMoment B raw41328step1 raw41328step1Labels := by
      have ha : raw41328step1 = -raw41328step0 := by apply Matrix.ext; change ∀ i j, raw41328step1 i j = -(raw41328step0 i j); unfold raw41328step1 raw41328step0; decide +kernel
      have hl : raw41328step1Labels = raw41328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical41329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41329 raw41329Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw41329 raw41329Labels = mixedMoment B raw41329step0 raw41329step0Labels := by
      have ha : raw41329step0 = (fun i j => raw41329 (permutation647 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41329step0 raw41329; decide +kernel
      have hl : raw41329step0Labels = raw41329Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41329 raw41329Labels permutation647 permutation6
    _ = mixedMoment B node2923 node2923Labels := by rfl

theorem canonical41330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41330 raw41330Labels = mixedMoment B node1234 node1234Labels := by
  calc
    mixedMoment B raw41330 raw41330Labels = mixedMoment B raw41330step0 raw41330step0Labels := by
      have hz : ∀ j, raw41330 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41330step0 = (fun i j => raw41330 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41330step0 raw41330; decide +kernel
      have hl : raw41330step0Labels = raw41330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41330 raw41330Labels permutation434 hz
    mixedMoment B raw41330step0 raw41330step0Labels = mixedMoment B raw41330step1 raw41330step1Labels := by
      have ha : raw41330step1 = (fun i j => raw41330step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41330step1 raw41330step0; decide +kernel
      have hl : raw41330step1Labels = raw41330step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41330step0 raw41330step0Labels permutation128 permutation6
    _ = mixedMoment B node1234 node1234Labels := by rfl

theorem canonical41331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41331 raw41331Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw41331 raw41331Labels = mixedMoment B raw41331step0 raw41331step0Labels := by
      have ha : raw41331step0 = (fun i j => raw41331 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41331step0 raw41331; decide +kernel
      have hl : raw41331step0Labels = raw41331Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41331 raw41331Labels permutation590 permutation6
    _ = mixedMoment B node1233 node1233Labels := by rfl

theorem canonical41332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41332 raw41332Labels = mixedMoment B node1212 node1212Labels := by
  calc
    mixedMoment B raw41332 raw41332Labels = mixedMoment B raw41332step0 raw41332step0Labels := by
      have ha : raw41332step0 = (fun i j => raw41332 (permutation599 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41332step0 raw41332; decide +kernel
      have hl : raw41332step0Labels = raw41332Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41332 raw41332Labels permutation599 permutation6
    _ = mixedMoment B node1212 node1212Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1888) =
      Integer.Sparse.eval keyMomentRow1888 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1888).leftCharge (GramAssembly.key 1888).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2512) := by
    have ha : gramCharges (GramAssembly.key 1888).leftCharge (GramAssembly.key 1888).rightCharge = raw41301 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41301Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41301 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1888).leftCharge (GramAssembly.key 1888).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1888, Integer.Sparse.eval]

theorem keyMoment1889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1889) =
      Integer.Sparse.eval keyMomentRow1889 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1889).leftCharge (GramAssembly.key 1889).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1087) := by
    have ha : gramCharges (GramAssembly.key 1889).leftCharge (GramAssembly.key 1889).rightCharge = raw41302 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41302Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41302 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1889).leftCharge (GramAssembly.key 1889).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1889, Integer.Sparse.eval]

theorem keyMoment1890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1890) =
      Integer.Sparse.eval keyMomentRow1890 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1890).leftCharge (GramAssembly.key 1890).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1091) := by
    have ha : gramCharges (GramAssembly.key 1890).leftCharge (GramAssembly.key 1890).rightCharge = raw41303 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41303Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41303 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1890).leftCharge (GramAssembly.key 1890).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1890, Integer.Sparse.eval]

theorem keyMoment1891 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1891) =
      Integer.Sparse.eval keyMomentRow1891 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1891).leftCharge (GramAssembly.key 1891).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4083) := by
    have ha : gramCharges (GramAssembly.key 1891).leftCharge (GramAssembly.key 1891).rightCharge = raw41304 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41304Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41304 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1891).leftCharge (GramAssembly.key 1891).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1891, Integer.Sparse.eval]

theorem keyMoment1892 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1892) =
      Integer.Sparse.eval keyMomentRow1892 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1892).leftCharge (GramAssembly.key 1892).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2741) := by
    have ha : gramCharges (GramAssembly.key 1892).leftCharge (GramAssembly.key 1892).rightCharge = raw41305 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41305Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41305 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1892).leftCharge (GramAssembly.key 1892).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1892, Integer.Sparse.eval]

theorem keyMoment1893 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1893) =
      Integer.Sparse.eval keyMomentRow1893 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1893).leftCharge (GramAssembly.key 1893).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3962) := by
    have ha : gramCharges (GramAssembly.key 1893).leftCharge (GramAssembly.key 1893).rightCharge = raw41306 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41306Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41306 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1893).leftCharge (GramAssembly.key 1893).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1893, Integer.Sparse.eval]

theorem keyMoment1894 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1894) =
      Integer.Sparse.eval keyMomentRow1894 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1894).leftCharge (GramAssembly.key 1894).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3619) := by
    have ha : gramCharges (GramAssembly.key 1894).leftCharge (GramAssembly.key 1894).rightCharge = raw41307 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41307Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41307 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1894).leftCharge (GramAssembly.key 1894).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1894, Integer.Sparse.eval]

theorem keyMoment1895 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1895) =
      Integer.Sparse.eval keyMomentRow1895 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1895).leftCharge (GramAssembly.key 1895).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4025) := by
    have ha : gramCharges (GramAssembly.key 1895).leftCharge (GramAssembly.key 1895).rightCharge = raw41308 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41308Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41308 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1895).leftCharge (GramAssembly.key 1895).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1895, Integer.Sparse.eval]

theorem keyMoment1896 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1896) =
      Integer.Sparse.eval keyMomentRow1896 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1896).leftCharge (GramAssembly.key 1896).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2263) := by
    have ha : gramCharges (GramAssembly.key 1896).leftCharge (GramAssembly.key 1896).rightCharge = raw41309 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41309Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41309 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1896).leftCharge (GramAssembly.key 1896).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1896, Integer.Sparse.eval]

theorem keyMoment1897 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1897) =
      Integer.Sparse.eval keyMomentRow1897 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1897).leftCharge (GramAssembly.key 1897).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2721) := by
    have ha : gramCharges (GramAssembly.key 1897).leftCharge (GramAssembly.key 1897).rightCharge = raw41310 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41310Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41310 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1897).leftCharge (GramAssembly.key 1897).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1897, Integer.Sparse.eval]

theorem keyMoment1898 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1898) =
      Integer.Sparse.eval keyMomentRow1898 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1898).leftCharge (GramAssembly.key 1898).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3957) := by
    have ha : gramCharges (GramAssembly.key 1898).leftCharge (GramAssembly.key 1898).rightCharge = raw41311 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41311Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41311 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1898).leftCharge (GramAssembly.key 1898).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1898, Integer.Sparse.eval]

theorem keyMoment1899 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1899) =
      Integer.Sparse.eval keyMomentRow1899 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1899).leftCharge (GramAssembly.key 1899).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3526) := by
    have ha : gramCharges (GramAssembly.key 1899).leftCharge (GramAssembly.key 1899).rightCharge = raw41312 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41312Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41312 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1899).leftCharge (GramAssembly.key 1899).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1899, Integer.Sparse.eval]

theorem keyMoment1900 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1900) =
      Integer.Sparse.eval keyMomentRow1900 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1900).leftCharge (GramAssembly.key 1900).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3075) := by
    have ha : gramCharges (GramAssembly.key 1900).leftCharge (GramAssembly.key 1900).rightCharge = raw41313 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41313Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41313 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1900).leftCharge (GramAssembly.key 1900).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1900, Integer.Sparse.eval]

theorem keyMoment1901 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1901) =
      Integer.Sparse.eval keyMomentRow1901 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1901).leftCharge (GramAssembly.key 1901).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3074) := by
    have ha : gramCharges (GramAssembly.key 1901).leftCharge (GramAssembly.key 1901).rightCharge = raw41314 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41314Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41314 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1901).leftCharge (GramAssembly.key 1901).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1901, Integer.Sparse.eval]

theorem keyMoment1902 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1902) =
      Integer.Sparse.eval keyMomentRow1902 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1902).leftCharge (GramAssembly.key 1902).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2764) := by
    have ha : gramCharges (GramAssembly.key 1902).leftCharge (GramAssembly.key 1902).rightCharge = raw41315 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41315Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41315 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1902).leftCharge (GramAssembly.key 1902).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1902, Integer.Sparse.eval]

theorem keyMoment1903 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1903) =
      Integer.Sparse.eval keyMomentRow1903 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1903).leftCharge (GramAssembly.key 1903).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3954) := by
    have ha : gramCharges (GramAssembly.key 1903).leftCharge (GramAssembly.key 1903).rightCharge = raw41316 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41316Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41316 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1903).leftCharge (GramAssembly.key 1903).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1903, Integer.Sparse.eval]

theorem keyMoment1904 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1904) =
      Integer.Sparse.eval keyMomentRow1904 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1904).leftCharge (GramAssembly.key 1904).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3078) := by
    have ha : gramCharges (GramAssembly.key 1904).leftCharge (GramAssembly.key 1904).rightCharge = raw41317 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41317Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41317 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1904).leftCharge (GramAssembly.key 1904).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1904, Integer.Sparse.eval]

theorem keyMoment1905 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1905) =
      Integer.Sparse.eval keyMomentRow1905 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1905).leftCharge (GramAssembly.key 1905).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2247) := by
    have ha : gramCharges (GramAssembly.key 1905).leftCharge (GramAssembly.key 1905).rightCharge = raw41318 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41318Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41318 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1905).leftCharge (GramAssembly.key 1905).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1905, Integer.Sparse.eval]

theorem keyMoment1906 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1906) =
      Integer.Sparse.eval keyMomentRow1906 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1906).leftCharge (GramAssembly.key 1906).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3623) := by
    have ha : gramCharges (GramAssembly.key 1906).leftCharge (GramAssembly.key 1906).rightCharge = raw41319 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41319Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41319 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1906).leftCharge (GramAssembly.key 1906).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1906, Integer.Sparse.eval]

theorem keyMoment1907 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1907) =
      Integer.Sparse.eval keyMomentRow1907 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1907).leftCharge (GramAssembly.key 1907).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3077) := by
    have ha : gramCharges (GramAssembly.key 1907).leftCharge (GramAssembly.key 1907).rightCharge = raw41320 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41320Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41320 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1907).leftCharge (GramAssembly.key 1907).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1907, Integer.Sparse.eval]

theorem keyMoment1908 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1908) =
      Integer.Sparse.eval keyMomentRow1908 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1908).leftCharge (GramAssembly.key 1908).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4010) := by
    have ha : gramCharges (GramAssembly.key 1908).leftCharge (GramAssembly.key 1908).rightCharge = raw41321 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41321Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41321 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1908).leftCharge (GramAssembly.key 1908).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1908, Integer.Sparse.eval]

theorem keyMoment1909 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1909) =
      Integer.Sparse.eval keyMomentRow1909 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1909).leftCharge (GramAssembly.key 1909).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2277) := by
    have ha : gramCharges (GramAssembly.key 1909).leftCharge (GramAssembly.key 1909).rightCharge = raw41322 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41322Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41322 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1909).leftCharge (GramAssembly.key 1909).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1909, Integer.Sparse.eval]

theorem keyMoment1910 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1910) =
      Integer.Sparse.eval keyMomentRow1910 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1910).leftCharge (GramAssembly.key 1910).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2730) := by
    have ha : gramCharges (GramAssembly.key 1910).leftCharge (GramAssembly.key 1910).rightCharge = raw41323 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41323Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41323 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1910).leftCharge (GramAssembly.key 1910).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1910, Integer.Sparse.eval]

theorem keyMoment1911 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1911) =
      Integer.Sparse.eval keyMomentRow1911 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1911).leftCharge (GramAssembly.key 1911).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3043) := by
    have ha : gramCharges (GramAssembly.key 1911).leftCharge (GramAssembly.key 1911).rightCharge = raw41324 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41324Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41324 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1911).leftCharge (GramAssembly.key 1911).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1911, Integer.Sparse.eval]

theorem keyMoment1912 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1912) =
      Integer.Sparse.eval keyMomentRow1912 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1912).leftCharge (GramAssembly.key 1912).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3812) := by
    have ha : gramCharges (GramAssembly.key 1912).leftCharge (GramAssembly.key 1912).rightCharge = raw41325 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41325Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41325 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1912).leftCharge (GramAssembly.key 1912).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1912, Integer.Sparse.eval]

theorem keyMoment1913 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1913) =
      Integer.Sparse.eval keyMomentRow1913 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1913).leftCharge (GramAssembly.key 1913).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3874) := by
    have ha : gramCharges (GramAssembly.key 1913).leftCharge (GramAssembly.key 1913).rightCharge = raw41326 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41326Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41326 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1913).leftCharge (GramAssembly.key 1913).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1913, Integer.Sparse.eval]

theorem keyMoment1914 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1914) =
      Integer.Sparse.eval keyMomentRow1914 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1914).leftCharge (GramAssembly.key 1914).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3488) := by
    have ha : gramCharges (GramAssembly.key 1914).leftCharge (GramAssembly.key 1914).rightCharge = raw41327 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41327Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41327 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1914).leftCharge (GramAssembly.key 1914).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1914, Integer.Sparse.eval]

theorem keyMoment1915 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1915) =
      Integer.Sparse.eval keyMomentRow1915 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1915).leftCharge (GramAssembly.key 1915).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2243) := by
    have ha : gramCharges (GramAssembly.key 1915).leftCharge (GramAssembly.key 1915).rightCharge = raw41328 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41328Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41328 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1915).leftCharge (GramAssembly.key 1915).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1915, Integer.Sparse.eval]

theorem keyMoment1916 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1916) =
      Integer.Sparse.eval keyMomentRow1916 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1916).leftCharge (GramAssembly.key 1916).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2923) := by
    have ha : gramCharges (GramAssembly.key 1916).leftCharge (GramAssembly.key 1916).rightCharge = raw41329 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41329Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41329 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1916).leftCharge (GramAssembly.key 1916).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1916, Integer.Sparse.eval]

theorem keyMoment1917 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1917) =
      Integer.Sparse.eval keyMomentRow1917 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1917).leftCharge (GramAssembly.key 1917).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1234) := by
    have ha : gramCharges (GramAssembly.key 1917).leftCharge (GramAssembly.key 1917).rightCharge = raw41330 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41330Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41330 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1917).leftCharge (GramAssembly.key 1917).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1917, Integer.Sparse.eval]

theorem keyMoment1918 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1918) =
      Integer.Sparse.eval keyMomentRow1918 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1918).leftCharge (GramAssembly.key 1918).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1233) := by
    have ha : gramCharges (GramAssembly.key 1918).leftCharge (GramAssembly.key 1918).rightCharge = raw41331 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41331Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41331 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1918).leftCharge (GramAssembly.key 1918).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1918, Integer.Sparse.eval]

theorem keyMoment1919 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1919) =
      Integer.Sparse.eval keyMomentRow1919 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1919).leftCharge (GramAssembly.key 1919).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1212) := by
    have ha : gramCharges (GramAssembly.key 1919).leftCharge (GramAssembly.key 1919).rightCharge = raw41332 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41332Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41332 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1919).leftCharge (GramAssembly.key 1919).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1919, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1888 : keyMomentRows (1888 : Fin 2886) =
    keyMomentRow1888 := by decide +kernel

theorem keyMomentRowsAt1889 : keyMomentRows (1889 : Fin 2886) =
    keyMomentRow1889 := by decide +kernel

theorem keyMomentRowsAt1890 : keyMomentRows (1890 : Fin 2886) =
    keyMomentRow1890 := by decide +kernel

theorem keyMomentRowsAt1891 : keyMomentRows (1891 : Fin 2886) =
    keyMomentRow1891 := by decide +kernel

theorem keyMomentRowsAt1892 : keyMomentRows (1892 : Fin 2886) =
    keyMomentRow1892 := by decide +kernel

theorem keyMomentRowsAt1893 : keyMomentRows (1893 : Fin 2886) =
    keyMomentRow1893 := by decide +kernel

theorem keyMomentRowsAt1894 : keyMomentRows (1894 : Fin 2886) =
    keyMomentRow1894 := by decide +kernel

theorem keyMomentRowsAt1895 : keyMomentRows (1895 : Fin 2886) =
    keyMomentRow1895 := by decide +kernel

theorem keyMomentRowsAt1896 : keyMomentRows (1896 : Fin 2886) =
    keyMomentRow1896 := by decide +kernel

theorem keyMomentRowsAt1897 : keyMomentRows (1897 : Fin 2886) =
    keyMomentRow1897 := by decide +kernel

theorem keyMomentRowsAt1898 : keyMomentRows (1898 : Fin 2886) =
    keyMomentRow1898 := by decide +kernel

theorem keyMomentRowsAt1899 : keyMomentRows (1899 : Fin 2886) =
    keyMomentRow1899 := by decide +kernel

theorem keyMomentRowsAt1900 : keyMomentRows (1900 : Fin 2886) =
    keyMomentRow1900 := by decide +kernel

theorem keyMomentRowsAt1901 : keyMomentRows (1901 : Fin 2886) =
    keyMomentRow1901 := by decide +kernel

theorem keyMomentRowsAt1902 : keyMomentRows (1902 : Fin 2886) =
    keyMomentRow1902 := by decide +kernel

theorem keyMomentRowsAt1903 : keyMomentRows (1903 : Fin 2886) =
    keyMomentRow1903 := by decide +kernel

theorem keyMomentRowsAt1904 : keyMomentRows (1904 : Fin 2886) =
    keyMomentRow1904 := by decide +kernel

theorem keyMomentRowsAt1905 : keyMomentRows (1905 : Fin 2886) =
    keyMomentRow1905 := by decide +kernel

theorem keyMomentRowsAt1906 : keyMomentRows (1906 : Fin 2886) =
    keyMomentRow1906 := by decide +kernel

theorem keyMomentRowsAt1907 : keyMomentRows (1907 : Fin 2886) =
    keyMomentRow1907 := by decide +kernel

theorem keyMomentRowsAt1908 : keyMomentRows (1908 : Fin 2886) =
    keyMomentRow1908 := by decide +kernel

theorem keyMomentRowsAt1909 : keyMomentRows (1909 : Fin 2886) =
    keyMomentRow1909 := by decide +kernel

theorem keyMomentRowsAt1910 : keyMomentRows (1910 : Fin 2886) =
    keyMomentRow1910 := by decide +kernel

theorem keyMomentRowsAt1911 : keyMomentRows (1911 : Fin 2886) =
    keyMomentRow1911 := by decide +kernel

theorem keyMomentRowsAt1912 : keyMomentRows (1912 : Fin 2886) =
    keyMomentRow1912 := by decide +kernel

theorem keyMomentRowsAt1913 : keyMomentRows (1913 : Fin 2886) =
    keyMomentRow1913 := by decide +kernel

theorem keyMomentRowsAt1914 : keyMomentRows (1914 : Fin 2886) =
    keyMomentRow1914 := by decide +kernel

theorem keyMomentRowsAt1915 : keyMomentRows (1915 : Fin 2886) =
    keyMomentRow1915 := by decide +kernel

theorem keyMomentRowsAt1916 : keyMomentRows (1916 : Fin 2886) =
    keyMomentRow1916 := by decide +kernel

theorem keyMomentRowsAt1917 : keyMomentRows (1917 : Fin 2886) =
    keyMomentRow1917 := by decide +kernel

theorem keyMomentRowsAt1918 : keyMomentRows (1918 : Fin 2886) =
    keyMomentRow1918 := by decide +kernel

theorem keyMomentRowsAt1919 : keyMomentRows (1919 : Fin 2886) =
    keyMomentRow1919 := by decide +kernel

theorem keyMomentChunkSound59_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 59) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1888 ∨ k.val = 1889 ∨ k.val = 1890 ∨ k.val = 1891 ∨ k.val = 1892 ∨ k.val = 1893 ∨ k.val = 1894 ∨ k.val = 1895 ∨ k.val = 1896 ∨ k.val = 1897 ∨ k.val = 1898 ∨ k.val = 1899 ∨ k.val = 1900 ∨ k.val = 1901 ∨ k.val = 1902 ∨ k.val = 1903 ∨ k.val = 1904 ∨ k.val = 1905 ∨ k.val = 1906 ∨ k.val = 1907 ∨ k.val = 1908 ∨ k.val = 1909 ∨ k.val = 1910 ∨ k.val = 1911 ∨ k.val = 1912 ∨ k.val = 1913 ∨ k.val = 1914 ∨ k.val = 1915 ∨ k.val = 1916 ∨ k.val = 1917 ∨ k.val = 1918 ∨ k.val = 1919 := by omega
  rcases heq with h1888 | h1889 | h1890 | h1891 | h1892 | h1893 | h1894 | h1895 | h1896 | h1897 | h1898 | h1899 | h1900 | h1901 | h1902 | h1903 | h1904 | h1905 | h1906 | h1907 | h1908 | h1909 | h1910 | h1911 | h1912 | h1913 | h1914 | h1915 | h1916 | h1917 | h1918 | h1919
  · have he : k = (1888 : Fin 2886) := Fin.ext h1888
    subst k
    rw [keyMomentRowsAt1888]
    exact keyMoment1888 B hB
  · have he : k = (1889 : Fin 2886) := Fin.ext h1889
    subst k
    rw [keyMomentRowsAt1889]
    exact keyMoment1889 B hB
  · have he : k = (1890 : Fin 2886) := Fin.ext h1890
    subst k
    rw [keyMomentRowsAt1890]
    exact keyMoment1890 B hB
  · have he : k = (1891 : Fin 2886) := Fin.ext h1891
    subst k
    rw [keyMomentRowsAt1891]
    exact keyMoment1891 B hB
  · have he : k = (1892 : Fin 2886) := Fin.ext h1892
    subst k
    rw [keyMomentRowsAt1892]
    exact keyMoment1892 B hB
  · have he : k = (1893 : Fin 2886) := Fin.ext h1893
    subst k
    rw [keyMomentRowsAt1893]
    exact keyMoment1893 B hB
  · have he : k = (1894 : Fin 2886) := Fin.ext h1894
    subst k
    rw [keyMomentRowsAt1894]
    exact keyMoment1894 B hB
  · have he : k = (1895 : Fin 2886) := Fin.ext h1895
    subst k
    rw [keyMomentRowsAt1895]
    exact keyMoment1895 B hB
  · have he : k = (1896 : Fin 2886) := Fin.ext h1896
    subst k
    rw [keyMomentRowsAt1896]
    exact keyMoment1896 B hB
  · have he : k = (1897 : Fin 2886) := Fin.ext h1897
    subst k
    rw [keyMomentRowsAt1897]
    exact keyMoment1897 B hB
  · have he : k = (1898 : Fin 2886) := Fin.ext h1898
    subst k
    rw [keyMomentRowsAt1898]
    exact keyMoment1898 B hB
  · have he : k = (1899 : Fin 2886) := Fin.ext h1899
    subst k
    rw [keyMomentRowsAt1899]
    exact keyMoment1899 B hB
  · have he : k = (1900 : Fin 2886) := Fin.ext h1900
    subst k
    rw [keyMomentRowsAt1900]
    exact keyMoment1900 B hB
  · have he : k = (1901 : Fin 2886) := Fin.ext h1901
    subst k
    rw [keyMomentRowsAt1901]
    exact keyMoment1901 B hB
  · have he : k = (1902 : Fin 2886) := Fin.ext h1902
    subst k
    rw [keyMomentRowsAt1902]
    exact keyMoment1902 B hB
  · have he : k = (1903 : Fin 2886) := Fin.ext h1903
    subst k
    rw [keyMomentRowsAt1903]
    exact keyMoment1903 B hB
  · have he : k = (1904 : Fin 2886) := Fin.ext h1904
    subst k
    rw [keyMomentRowsAt1904]
    exact keyMoment1904 B hB
  · have he : k = (1905 : Fin 2886) := Fin.ext h1905
    subst k
    rw [keyMomentRowsAt1905]
    exact keyMoment1905 B hB
  · have he : k = (1906 : Fin 2886) := Fin.ext h1906
    subst k
    rw [keyMomentRowsAt1906]
    exact keyMoment1906 B hB
  · have he : k = (1907 : Fin 2886) := Fin.ext h1907
    subst k
    rw [keyMomentRowsAt1907]
    exact keyMoment1907 B hB
  · have he : k = (1908 : Fin 2886) := Fin.ext h1908
    subst k
    rw [keyMomentRowsAt1908]
    exact keyMoment1908 B hB
  · have he : k = (1909 : Fin 2886) := Fin.ext h1909
    subst k
    rw [keyMomentRowsAt1909]
    exact keyMoment1909 B hB
  · have he : k = (1910 : Fin 2886) := Fin.ext h1910
    subst k
    rw [keyMomentRowsAt1910]
    exact keyMoment1910 B hB
  · have he : k = (1911 : Fin 2886) := Fin.ext h1911
    subst k
    rw [keyMomentRowsAt1911]
    exact keyMoment1911 B hB
  · have he : k = (1912 : Fin 2886) := Fin.ext h1912
    subst k
    rw [keyMomentRowsAt1912]
    exact keyMoment1912 B hB
  · have he : k = (1913 : Fin 2886) := Fin.ext h1913
    subst k
    rw [keyMomentRowsAt1913]
    exact keyMoment1913 B hB
  · have he : k = (1914 : Fin 2886) := Fin.ext h1914
    subst k
    rw [keyMomentRowsAt1914]
    exact keyMoment1914 B hB
  · have he : k = (1915 : Fin 2886) := Fin.ext h1915
    subst k
    rw [keyMomentRowsAt1915]
    exact keyMoment1915 B hB
  · have he : k = (1916 : Fin 2886) := Fin.ext h1916
    subst k
    rw [keyMomentRowsAt1916]
    exact keyMoment1916 B hB
  · have he : k = (1917 : Fin 2886) := Fin.ext h1917
    subst k
    rw [keyMomentRowsAt1917]
    exact keyMoment1917 B hB
  · have he : k = (1918 : Fin 2886) := Fin.ext h1918
    subst k
    rw [keyMomentRowsAt1918]
    exact keyMoment1918 B hB
  · have he : k = (1919 : Fin 2886) := Fin.ext h1919
    subst k
    rw [keyMomentRowsAt1919]
    exact keyMoment1919 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound59_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound59_e_oai
