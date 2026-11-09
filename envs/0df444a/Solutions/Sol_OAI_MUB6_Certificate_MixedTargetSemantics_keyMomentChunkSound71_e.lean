-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound71_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:01:54.833734+00:00
-- url     : https://prove2.me/submissions/c5c74bbe-9a0a-450c-b437-1dd2a46632bc

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

theorem canonical41856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41856 raw41856Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw41856 raw41856Labels = mixedMoment B raw41856step0 raw41856step0Labels := by
      have hz : ∀ j, raw41856 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41856step0 = (fun i j => raw41856 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41856step0 raw41856; decide +kernel
      have hl : raw41856step0Labels = raw41856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41856 raw41856Labels permutation265 hz
    mixedMoment B raw41856step0 raw41856step0Labels = mixedMoment B raw41856step1 raw41856step1Labels := by
      have ha : raw41856step1 = (fun i j => raw41856step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41856step1 raw41856step0; decide +kernel
      have hl : raw41856step1Labels = raw41856step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41856step0 raw41856step0Labels permutation37 permutation2
    mixedMoment B raw41856step1 raw41856step1Labels = mixedMoment B raw41856step2 raw41856step2Labels := by
      have ha : raw41856step2 = raw41856step1 := by apply Matrix.ext; unfold raw41856step2 raw41856step1; decide +kernel
      have hl : raw41856step1Labels = labelEmbedding1 ∘ raw41856step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41856step1 raw41856step1Labels raw41856step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

theorem canonical41857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41857 raw41857Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw41857 raw41857Labels = mixedMoment B raw41857step0 raw41857step0Labels := by
      have hz : ∀ j, raw41857 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41857step0 = (fun i j => raw41857 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41857step0 raw41857; decide +kernel
      have hl : raw41857step0Labels = raw41857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41857 raw41857Labels permutation265 hz
    mixedMoment B raw41857step0 raw41857step0Labels = mixedMoment B raw41857step1 raw41857step1Labels := by
      have ha : raw41857step1 = (fun i j => raw41857step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41857step1 raw41857step0; decide +kernel
      have hl : raw41857step1Labels = raw41857step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41857step0 raw41857step0Labels permutation37 permutation7
    mixedMoment B raw41857step1 raw41857step1Labels = mixedMoment B raw41857step2 raw41857step2Labels := by
      have ha : raw41857step2 = -raw41857step1 := by apply Matrix.ext; change ∀ i j, raw41857step2 i j = -(raw41857step1 i j); unfold raw41857step2 raw41857step1; decide +kernel
      have hl : raw41857step2Labels = raw41857step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41857step2 raw41857step2Labels = mixedMoment B raw41857step3 raw41857step3Labels := by
      have ha : raw41857step3 = raw41857step2 := by apply Matrix.ext; unfold raw41857step3 raw41857step2; decide +kernel
      have hl : raw41857step2Labels = labelEmbedding6 ∘ raw41857step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41857step2 raw41857step2Labels raw41857step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4777 node4777Labels := by rfl

theorem canonical41858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41858 raw41858Labels = mixedMoment B node1685 node1685Labels := by
  calc
    mixedMoment B raw41858 raw41858Labels = mixedMoment B raw41858step0 raw41858step0Labels := by
      have hz : ∀ j, raw41858 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41858step0 = (fun i j => raw41858 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41858step0 raw41858; decide +kernel
      have hl : raw41858step0Labels = raw41858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41858 raw41858Labels permutation265 hz
    mixedMoment B raw41858step0 raw41858step0Labels = mixedMoment B raw41858step1 raw41858step1Labels := by
      have ha : raw41858step1 = (fun i j => raw41858step0 (permutation93 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41858step1 raw41858step0; decide +kernel
      have hl : raw41858step1Labels = raw41858step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41858step0 raw41858step0Labels permutation93 permutation4
    mixedMoment B raw41858step1 raw41858step1Labels = mixedMoment B raw41858step2 raw41858step2Labels := by
      have ha : raw41858step2 = -raw41858step1 := by apply Matrix.ext; change ∀ i j, raw41858step2 i j = -(raw41858step1 i j); unfold raw41858step2 raw41858step1; decide +kernel
      have hl : raw41858step2Labels = raw41858step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41858step2 raw41858step2Labels = mixedMoment B raw41858step3 raw41858step3Labels := by
      have ha : raw41858step3 = raw41858step2 := by apply Matrix.ext; unfold raw41858step3 raw41858step2; decide +kernel
      have hl : raw41858step2Labels = labelEmbedding1 ∘ raw41858step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41858step2 raw41858step2Labels raw41858step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1685 node1685Labels := by rfl

theorem canonical41859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41859 raw41859Labels = mixedMoment B node4336 node4336Labels := by
  calc
    mixedMoment B raw41859 raw41859Labels = mixedMoment B raw41859step0 raw41859step0Labels := by
      have hz : ∀ j, raw41859 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41859step0 = (fun i j => raw41859 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41859step0 raw41859; decide +kernel
      have hl : raw41859step0Labels = raw41859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41859 raw41859Labels permutation265 hz
    mixedMoment B raw41859step0 raw41859step0Labels = mixedMoment B raw41859step1 raw41859step1Labels := by
      have ha : raw41859step1 = (fun i j => raw41859step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41859step1 raw41859step0; decide +kernel
      have hl : raw41859step1Labels = raw41859step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41859step0 raw41859step0Labels permutation97 permutation6
    _ = mixedMoment B node4336 node4336Labels := by rfl

theorem canonical41860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41860 raw41860Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw41860 raw41860Labels = mixedMoment B raw41860step0 raw41860step0Labels := by
      have hz : ∀ j, raw41860 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41860step0 = (fun i j => raw41860 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41860step0 raw41860; decide +kernel
      have hl : raw41860step0Labels = raw41860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41860 raw41860Labels permutation265 hz
    mixedMoment B raw41860step0 raw41860step0Labels = mixedMoment B raw41860step1 raw41860step1Labels := by
      have ha : raw41860step1 = (fun i j => raw41860step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41860step1 raw41860step0; decide +kernel
      have hl : raw41860step1Labels = raw41860step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41860step0 raw41860step0Labels permutation37 permutation2
    mixedMoment B raw41860step1 raw41860step1Labels = mixedMoment B raw41860step2 raw41860step2Labels := by
      have ha : raw41860step2 = raw41860step1 := by apply Matrix.ext; unfold raw41860step2 raw41860step1; decide +kernel
      have hl : raw41860step1Labels = labelEmbedding1 ∘ raw41860step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41860step1 raw41860step1Labels raw41860step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2164 node2164Labels := by rfl

theorem canonical41861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41861 raw41861Labels = mixedMoment B node4670 node4670Labels := by
  calc
    mixedMoment B raw41861 raw41861Labels = mixedMoment B raw41861step0 raw41861step0Labels := by
      have hz : ∀ j, raw41861 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41861step0 = (fun i j => raw41861 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41861step0 raw41861; decide +kernel
      have hl : raw41861step0Labels = raw41861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41861 raw41861Labels permutation265 hz
    mixedMoment B raw41861step0 raw41861step0Labels = mixedMoment B raw41861step1 raw41861step1Labels := by
      have ha : raw41861step1 = (fun i j => raw41861step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41861step1 raw41861step0; decide +kernel
      have hl : raw41861step1Labels = raw41861step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41861step0 raw41861step0Labels permutation37 permutation7
    mixedMoment B raw41861step1 raw41861step1Labels = mixedMoment B raw41861step2 raw41861step2Labels := by
      have ha : raw41861step2 = -raw41861step1 := by apply Matrix.ext; change ∀ i j, raw41861step2 i j = -(raw41861step1 i j); unfold raw41861step2 raw41861step1; decide +kernel
      have hl : raw41861step2Labels = raw41861step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41861step2 raw41861step2Labels = mixedMoment B raw41861step3 raw41861step3Labels := by
      have ha : raw41861step3 = raw41861step2 := by apply Matrix.ext; unfold raw41861step3 raw41861step2; decide +kernel
      have hl : raw41861step2Labels = labelEmbedding6 ∘ raw41861step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41861step2 raw41861step2Labels raw41861step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4670 node4670Labels := by rfl

theorem canonical41862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41862 raw41862Labels = mixedMoment B node1684 node1684Labels := by
  calc
    mixedMoment B raw41862 raw41862Labels = mixedMoment B raw41862step0 raw41862step0Labels := by
      have ha : raw41862step0 = (fun i j => raw41862 (permutation487 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41862step0 raw41862; decide +kernel
      have hl : raw41862step0Labels = raw41862Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41862 raw41862Labels permutation487 permutation4
    mixedMoment B raw41862step0 raw41862step0Labels = mixedMoment B raw41862step1 raw41862step1Labels := by
      have ha : raw41862step1 = -raw41862step0 := by apply Matrix.ext; change ∀ i j, raw41862step1 i j = -(raw41862step0 i j); unfold raw41862step1 raw41862step0; decide +kernel
      have hl : raw41862step1Labels = raw41862step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41862step1 raw41862step1Labels = mixedMoment B raw41862step2 raw41862step2Labels := by
      have ha : raw41862step2 = raw41862step1 := by apply Matrix.ext; unfold raw41862step2 raw41862step1; decide +kernel
      have hl : raw41862step1Labels = labelEmbedding1 ∘ raw41862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41862step1 raw41862step1Labels raw41862step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1684 node1684Labels := by rfl

theorem canonical41863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41863 raw41863Labels = mixedMoment B node4331 node4331Labels := by
  calc
    mixedMoment B raw41863 raw41863Labels = mixedMoment B raw41863step0 raw41863step0Labels := by
      have ha : raw41863step0 = (fun i j => raw41863 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41863step0 raw41863; decide +kernel
      have hl : raw41863step0Labels = raw41863Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41863 raw41863Labels permutation502 permutation6
    _ = mixedMoment B node4331 node4331Labels := by rfl

theorem canonical41864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41864 raw41864Labels = mixedMoment B node2181 node2181Labels := by
  calc
    mixedMoment B raw41864 raw41864Labels = mixedMoment B raw41864step0 raw41864step0Labels := by
      have ha : raw41864step0 = (fun i j => raw41864 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41864step0 raw41864; decide +kernel
      have hl : raw41864step0Labels = raw41864Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41864 raw41864Labels permutation157 permutation2
    mixedMoment B raw41864step0 raw41864step0Labels = mixedMoment B raw41864step1 raw41864step1Labels := by
      have ha : raw41864step1 = raw41864step0 := by apply Matrix.ext; unfold raw41864step1 raw41864step0; decide +kernel
      have hl : raw41864step0Labels = labelEmbedding1 ∘ raw41864step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41864step0 raw41864step0Labels raw41864step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2181 node2181Labels := by rfl

theorem canonical41865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41865 raw41865Labels = mixedMoment B node4757 node4757Labels := by
  calc
    mixedMoment B raw41865 raw41865Labels = mixedMoment B raw41865step0 raw41865step0Labels := by
      have ha : raw41865step0 = (fun i j => raw41865 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41865step0 raw41865; decide +kernel
      have hl : raw41865step0Labels = raw41865Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41865 raw41865Labels permutation157 permutation7
    mixedMoment B raw41865step0 raw41865step0Labels = mixedMoment B raw41865step1 raw41865step1Labels := by
      have ha : raw41865step1 = -raw41865step0 := by apply Matrix.ext; change ∀ i j, raw41865step1 i j = -(raw41865step0 i j); unfold raw41865step1 raw41865step0; decide +kernel
      have hl : raw41865step1Labels = raw41865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41865step1 raw41865step1Labels = mixedMoment B raw41865step2 raw41865step2Labels := by
      have ha : raw41865step2 = raw41865step1 := by apply Matrix.ext; unfold raw41865step2 raw41865step1; decide +kernel
      have hl : raw41865step1Labels = labelEmbedding6 ∘ raw41865step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41865step1 raw41865step1Labels raw41865step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4757 node4757Labels := by rfl

theorem canonical41866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41866 raw41866Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw41866 raw41866Labels = mixedMoment B raw41866step0 raw41866step0Labels := by
      have hz : ∀ j, raw41866 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41866step0 = (fun i j => raw41866 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41866step0 raw41866; decide +kernel
      have hl : raw41866step0Labels = raw41866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41866 raw41866Labels permutation434 hz
    mixedMoment B raw41866step0 raw41866step0Labels = mixedMoment B raw41866step1 raw41866step1Labels := by
      have hz : ∀ j, raw41866step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41866step1 = (fun i j => raw41866step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41866step1 raw41866step0; decide +kernel
      have hl : raw41866step1Labels = raw41866step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41866step0 raw41866step0Labels permutation80 hz
    mixedMoment B raw41866step1 raw41866step1Labels = mixedMoment B raw41866step2 raw41866step2Labels := by
      have ha : raw41866step2 = raw41866step1 := by apply Matrix.ext; unfold raw41866step2 raw41866step1; decide +kernel
      have hl : raw41866step1Labels = labelEmbedding1 ∘ raw41866step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41866step1 raw41866step1Labels raw41866step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1746 node1746Labels := by rfl

theorem canonical41867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41867 raw41867Labels = mixedMoment B node4478 node4478Labels := by
  calc
    mixedMoment B raw41867 raw41867Labels = mixedMoment B raw41867step0 raw41867step0Labels := by
      have hz : ∀ j, raw41867 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41867step0 = (fun i j => raw41867 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41867step0 raw41867; decide +kernel
      have hl : raw41867step0Labels = raw41867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41867 raw41867Labels permutation434 hz
    mixedMoment B raw41867step0 raw41867step0Labels = mixedMoment B raw41867step1 raw41867step1Labels := by
      have hz : ∀ j, raw41867step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41867step1 = (fun i j => raw41867step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41867step1 raw41867step0; decide +kernel
      have hl : raw41867step1Labels = raw41867step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41867step0 raw41867step0Labels permutation80 hz
    mixedMoment B raw41867step1 raw41867step1Labels = mixedMoment B raw41867step2 raw41867step2Labels := by
      have ha : raw41867step2 = (fun i j => raw41867step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41867step2 raw41867step1; decide +kernel
      have hl : raw41867step2Labels = raw41867step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41867step1 raw41867step1Labels permutation13 permutation7
    mixedMoment B raw41867step2 raw41867step2Labels = mixedMoment B raw41867step3 raw41867step3Labels := by
      have ha : raw41867step3 = -raw41867step2 := by apply Matrix.ext; change ∀ i j, raw41867step3 i j = -(raw41867step2 i j); unfold raw41867step3 raw41867step2; decide +kernel
      have hl : raw41867step3Labels = raw41867step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41867step3 raw41867step3Labels = mixedMoment B raw41867step4 raw41867step4Labels := by
      have ha : raw41867step4 = raw41867step3 := by apply Matrix.ext; unfold raw41867step4 raw41867step3; decide +kernel
      have hl : raw41867step3Labels = labelEmbedding6 ∘ raw41867step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41867step3 raw41867step3Labels raw41867step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4478 node4478Labels := by rfl

theorem canonical41868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41868 raw41868Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw41868 raw41868Labels = mixedMoment B raw41868step0 raw41868step0Labels := by
      have hz : ∀ j, raw41868 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41868step0 = (fun i j => raw41868 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41868step0 raw41868; decide +kernel
      have hl : raw41868step0Labels = raw41868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41868 raw41868Labels permutation434 hz
    mixedMoment B raw41868step0 raw41868step0Labels = mixedMoment B raw41868step1 raw41868step1Labels := by
      have hz : ∀ j, raw41868step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41868step1 = (fun i j => raw41868step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41868step1 raw41868step0; decide +kernel
      have hl : raw41868step1Labels = raw41868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41868step0 raw41868step0Labels permutation80 hz
    mixedMoment B raw41868step1 raw41868step1Labels = mixedMoment B raw41868step2 raw41868step2Labels := by
      have ha : raw41868step2 = raw41868step1 := by apply Matrix.ext; unfold raw41868step2 raw41868step1; decide +kernel
      have hl : raw41868step1Labels = labelEmbedding1 ∘ raw41868step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41868step1 raw41868step1Labels raw41868step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1745 node1745Labels := by rfl

theorem canonical41869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41869 raw41869Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw41869 raw41869Labels = mixedMoment B raw41869step0 raw41869step0Labels := by
      have hz : ∀ j, raw41869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41869step0 = (fun i j => raw41869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41869step0 raw41869; decide +kernel
      have hl : raw41869step0Labels = raw41869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41869 raw41869Labels permutation434 hz
    mixedMoment B raw41869step0 raw41869step0Labels = mixedMoment B raw41869step1 raw41869step1Labels := by
      have hz : ∀ j, raw41869step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41869step1 = (fun i j => raw41869step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41869step1 raw41869step0; decide +kernel
      have hl : raw41869step1Labels = raw41869step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41869step0 raw41869step0Labels permutation80 hz
    mixedMoment B raw41869step1 raw41869step1Labels = mixedMoment B raw41869step2 raw41869step2Labels := by
      have ha : raw41869step2 = (fun i j => raw41869step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41869step2 raw41869step1; decide +kernel
      have hl : raw41869step2Labels = raw41869step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41869step1 raw41869step1Labels permutation11 permutation7
    mixedMoment B raw41869step2 raw41869step2Labels = mixedMoment B raw41869step3 raw41869step3Labels := by
      have ha : raw41869step3 = -raw41869step2 := by apply Matrix.ext; change ∀ i j, raw41869step3 i j = -(raw41869step2 i j); unfold raw41869step3 raw41869step2; decide +kernel
      have hl : raw41869step3Labels = raw41869step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41869step3 raw41869step3Labels = mixedMoment B raw41869step4 raw41869step4Labels := by
      have ha : raw41869step4 = raw41869step3 := by apply Matrix.ext; unfold raw41869step4 raw41869step3; decide +kernel
      have hl : raw41869step3Labels = labelEmbedding6 ∘ raw41869step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41869step3 raw41869step3Labels raw41869step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4464 node4464Labels := by rfl

theorem canonical41870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41870 raw41870Labels = mixedMoment B node1743 node1743Labels := by
  calc
    mixedMoment B raw41870 raw41870Labels = mixedMoment B raw41870step0 raw41870step0Labels := by
      have hz : ∀ j, raw41870 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41870step0 = (fun i j => raw41870 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41870step0 raw41870; decide +kernel
      have hl : raw41870step0Labels = raw41870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41870 raw41870Labels permutation434 hz
    mixedMoment B raw41870step0 raw41870step0Labels = mixedMoment B raw41870step1 raw41870step1Labels := by
      have hz : ∀ j, raw41870step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41870step1 = (fun i j => raw41870step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41870step1 raw41870step0; decide +kernel
      have hl : raw41870step1Labels = raw41870step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41870step0 raw41870step0Labels permutation80 hz
    mixedMoment B raw41870step1 raw41870step1Labels = mixedMoment B raw41870step2 raw41870step2Labels := by
      have ha : raw41870step2 = raw41870step1 := by apply Matrix.ext; unfold raw41870step2 raw41870step1; decide +kernel
      have hl : raw41870step1Labels = labelEmbedding1 ∘ raw41870step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41870step1 raw41870step1Labels raw41870step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1743 node1743Labels := by rfl

theorem canonical41871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41871 raw41871Labels = mixedMoment B node4375 node4375Labels := by
  calc
    mixedMoment B raw41871 raw41871Labels = mixedMoment B raw41871step0 raw41871step0Labels := by
      have hz : ∀ j, raw41871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41871step0 = (fun i j => raw41871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41871step0 raw41871; decide +kernel
      have hl : raw41871step0Labels = raw41871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41871 raw41871Labels permutation434 hz
    mixedMoment B raw41871step0 raw41871step0Labels = mixedMoment B raw41871step1 raw41871step1Labels := by
      have hz : ∀ j, raw41871step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41871step1 = (fun i j => raw41871step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41871step1 raw41871step0; decide +kernel
      have hl : raw41871step1Labels = raw41871step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41871step0 raw41871step0Labels permutation80 hz
    mixedMoment B raw41871step1 raw41871step1Labels = mixedMoment B raw41871step2 raw41871step2Labels := by
      have ha : raw41871step2 = (fun i j => raw41871step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41871step2 raw41871step1; decide +kernel
      have hl : raw41871step2Labels = raw41871step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41871step1 raw41871step1Labels permutation11 permutation7
    mixedMoment B raw41871step2 raw41871step2Labels = mixedMoment B raw41871step3 raw41871step3Labels := by
      have ha : raw41871step3 = -raw41871step2 := by apply Matrix.ext; change ∀ i j, raw41871step3 i j = -(raw41871step2 i j); unfold raw41871step3 raw41871step2; decide +kernel
      have hl : raw41871step3Labels = raw41871step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41871step3 raw41871step3Labels = mixedMoment B raw41871step4 raw41871step4Labels := by
      have ha : raw41871step4 = raw41871step3 := by apply Matrix.ext; unfold raw41871step4 raw41871step3; decide +kernel
      have hl : raw41871step3Labels = labelEmbedding6 ∘ raw41871step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41871step3 raw41871step3Labels raw41871step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4375 node4375Labels := by rfl

theorem canonical41872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41872 raw41872Labels = mixedMoment B node1685 node1685Labels := by
  calc
    mixedMoment B raw41872 raw41872Labels = mixedMoment B raw41872step0 raw41872step0Labels := by
      have hz : ∀ j, raw41872 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41872step0 = (fun i j => raw41872 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41872step0 raw41872; decide +kernel
      have hl : raw41872step0Labels = raw41872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41872 raw41872Labels permutation346 hz
    mixedMoment B raw41872step0 raw41872step0Labels = mixedMoment B raw41872step1 raw41872step1Labels := by
      have ha : raw41872step1 = (fun i j => raw41872step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41872step1 raw41872step0; decide +kernel
      have hl : raw41872step1Labels = raw41872step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41872step0 raw41872step0Labels permutation38 permutation2
    mixedMoment B raw41872step1 raw41872step1Labels = mixedMoment B raw41872step2 raw41872step2Labels := by
      have ha : raw41872step2 = raw41872step1 := by apply Matrix.ext; unfold raw41872step2 raw41872step1; decide +kernel
      have hl : raw41872step1Labels = labelEmbedding1 ∘ raw41872step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41872step1 raw41872step1Labels raw41872step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1685 node1685Labels := by rfl

theorem canonical41873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41873 raw41873Labels = mixedMoment B node4336 node4336Labels := by
  calc
    mixedMoment B raw41873 raw41873Labels = mixedMoment B raw41873step0 raw41873step0Labels := by
      have hz : ∀ j, raw41873 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41873step0 = (fun i j => raw41873 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41873step0 raw41873; decide +kernel
      have hl : raw41873step0Labels = raw41873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41873 raw41873Labels permutation346 hz
    mixedMoment B raw41873step0 raw41873step0Labels = mixedMoment B raw41873step1 raw41873step1Labels := by
      have ha : raw41873step1 = (fun i j => raw41873step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41873step1 raw41873step0; decide +kernel
      have hl : raw41873step1Labels = raw41873step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41873step0 raw41873step0Labels permutation41 permutation7
    mixedMoment B raw41873step1 raw41873step1Labels = mixedMoment B raw41873step2 raw41873step2Labels := by
      have ha : raw41873step2 = -raw41873step1 := by apply Matrix.ext; change ∀ i j, raw41873step2 i j = -(raw41873step1 i j); unfold raw41873step2 raw41873step1; decide +kernel
      have hl : raw41873step2Labels = raw41873step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41873step2 raw41873step2Labels = mixedMoment B raw41873step3 raw41873step3Labels := by
      have ha : raw41873step3 = raw41873step2 := by apply Matrix.ext; unfold raw41873step3 raw41873step2; decide +kernel
      have hl : raw41873step2Labels = labelEmbedding6 ∘ raw41873step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41873step2 raw41873step2Labels raw41873step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4336 node4336Labels := by rfl

theorem canonical41874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41874 raw41874Labels = mixedMoment B node1742 node1742Labels := by
  calc
    mixedMoment B raw41874 raw41874Labels = mixedMoment B raw41874step0 raw41874step0Labels := by
      have hz : ∀ j, raw41874 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41874step0 = (fun i j => raw41874 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41874step0 raw41874; decide +kernel
      have hl : raw41874step0Labels = raw41874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41874 raw41874Labels permutation346 hz
    mixedMoment B raw41874step0 raw41874step0Labels = mixedMoment B raw41874step1 raw41874step1Labels := by
      have ha : raw41874step1 = (fun i j => raw41874step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41874step1 raw41874step0; decide +kernel
      have hl : raw41874step1Labels = raw41874step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41874step0 raw41874step0Labels permutation36 permutation2
    mixedMoment B raw41874step1 raw41874step1Labels = mixedMoment B raw41874step2 raw41874step2Labels := by
      have ha : raw41874step2 = raw41874step1 := by apply Matrix.ext; unfold raw41874step2 raw41874step1; decide +kernel
      have hl : raw41874step1Labels = labelEmbedding1 ∘ raw41874step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41874step1 raw41874step1Labels raw41874step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1742 node1742Labels := by rfl

theorem canonical41875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41875 raw41875Labels = mixedMoment B node4371 node4371Labels := by
  calc
    mixedMoment B raw41875 raw41875Labels = mixedMoment B raw41875step0 raw41875step0Labels := by
      have hz : ∀ j, raw41875 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41875step0 = (fun i j => raw41875 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41875step0 raw41875; decide +kernel
      have hl : raw41875step0Labels = raw41875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41875 raw41875Labels permutation346 hz
    mixedMoment B raw41875step0 raw41875step0Labels = mixedMoment B raw41875step1 raw41875step1Labels := by
      have ha : raw41875step1 = (fun i j => raw41875step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41875step1 raw41875step0; decide +kernel
      have hl : raw41875step1Labels = raw41875step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41875step0 raw41875step0Labels permutation53 permutation7
    mixedMoment B raw41875step1 raw41875step1Labels = mixedMoment B raw41875step2 raw41875step2Labels := by
      have ha : raw41875step2 = -raw41875step1 := by apply Matrix.ext; change ∀ i j, raw41875step2 i j = -(raw41875step1 i j); unfold raw41875step2 raw41875step1; decide +kernel
      have hl : raw41875step2Labels = raw41875step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41875step2 raw41875step2Labels = mixedMoment B raw41875step3 raw41875step3Labels := by
      have ha : raw41875step3 = raw41875step2 := by apply Matrix.ext; unfold raw41875step3 raw41875step2; decide +kernel
      have hl : raw41875step2Labels = labelEmbedding6 ∘ raw41875step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41875step2 raw41875step2Labels raw41875step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4371 node4371Labels := by rfl

theorem canonical41876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41876 raw41876Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw41876 raw41876Labels = mixedMoment B raw41876step0 raw41876step0Labels := by
      have hz : ∀ j, raw41876 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41876step0 = (fun i j => raw41876 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41876step0 raw41876; decide +kernel
      have hl : raw41876step0Labels = raw41876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41876 raw41876Labels permutation346 hz
    mixedMoment B raw41876step0 raw41876step0Labels = mixedMoment B raw41876step1 raw41876step1Labels := by
      have ha : raw41876step1 = (fun i j => raw41876step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41876step1 raw41876step0; decide +kernel
      have hl : raw41876step1Labels = raw41876step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41876step0 raw41876step0Labels permutation35 permutation2
    mixedMoment B raw41876step1 raw41876step1Labels = mixedMoment B raw41876step2 raw41876step2Labels := by
      have ha : raw41876step2 = raw41876step1 := by apply Matrix.ext; unfold raw41876step2 raw41876step1; decide +kernel
      have hl : raw41876step1Labels = labelEmbedding1 ∘ raw41876step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41876step1 raw41876step1Labels raw41876step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

theorem canonical41877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41877 raw41877Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw41877 raw41877Labels = mixedMoment B raw41877step0 raw41877step0Labels := by
      have hz : ∀ j, raw41877 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41877step0 = (fun i j => raw41877 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41877step0 raw41877; decide +kernel
      have hl : raw41877step0Labels = raw41877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41877 raw41877Labels permutation346 hz
    mixedMoment B raw41877step0 raw41877step0Labels = mixedMoment B raw41877step1 raw41877step1Labels := by
      have ha : raw41877step1 = (fun i j => raw41877step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41877step1 raw41877step0; decide +kernel
      have hl : raw41877step1Labels = raw41877step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41877step0 raw41877step0Labels permutation49 permutation7
    mixedMoment B raw41877step1 raw41877step1Labels = mixedMoment B raw41877step2 raw41877step2Labels := by
      have ha : raw41877step2 = -raw41877step1 := by apply Matrix.ext; change ∀ i j, raw41877step2 i j = -(raw41877step1 i j); unfold raw41877step2 raw41877step1; decide +kernel
      have hl : raw41877step2Labels = raw41877step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41877step2 raw41877step2Labels = mixedMoment B raw41877step3 raw41877step3Labels := by
      have ha : raw41877step3 = raw41877step2 := by apply Matrix.ext; unfold raw41877step3 raw41877step2; decide +kernel
      have hl : raw41877step2Labels = labelEmbedding6 ∘ raw41877step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41877step2 raw41877step2Labels raw41877step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4442 node4442Labels := by rfl

theorem canonical41878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41878 raw41878Labels = mixedMoment B node1684 node1684Labels := by
  calc
    mixedMoment B raw41878 raw41878Labels = mixedMoment B raw41878step0 raw41878step0Labels := by
      have ha : raw41878step0 = (fun i j => raw41878 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41878step0 raw41878; decide +kernel
      have hl : raw41878step0Labels = raw41878Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41878 raw41878Labels permutation180 permutation2
    mixedMoment B raw41878step0 raw41878step0Labels = mixedMoment B raw41878step1 raw41878step1Labels := by
      have ha : raw41878step1 = raw41878step0 := by apply Matrix.ext; unfold raw41878step1 raw41878step0; decide +kernel
      have hl : raw41878step0Labels = labelEmbedding1 ∘ raw41878step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41878step0 raw41878step0Labels raw41878step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1684 node1684Labels := by rfl

theorem canonical41879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41879 raw41879Labels = mixedMoment B node4331 node4331Labels := by
  calc
    mixedMoment B raw41879 raw41879Labels = mixedMoment B raw41879step0 raw41879step0Labels := by
      have ha : raw41879step0 = (fun i j => raw41879 (permutation197 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41879step0 raw41879; decide +kernel
      have hl : raw41879step0Labels = raw41879Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41879 raw41879Labels permutation197 permutation7
    mixedMoment B raw41879step0 raw41879step0Labels = mixedMoment B raw41879step1 raw41879step1Labels := by
      have ha : raw41879step1 = -raw41879step0 := by apply Matrix.ext; change ∀ i j, raw41879step1 i j = -(raw41879step0 i j); unfold raw41879step1 raw41879step0; decide +kernel
      have hl : raw41879step1Labels = raw41879step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41879step1 raw41879step1Labels = mixedMoment B raw41879step2 raw41879step2Labels := by
      have ha : raw41879step2 = raw41879step1 := by apply Matrix.ext; unfold raw41879step2 raw41879step1; decide +kernel
      have hl : raw41879step1Labels = labelEmbedding6 ∘ raw41879step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41879step1 raw41879step1Labels raw41879step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4331 node4331Labels := by rfl

theorem canonical41880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41880 raw41880Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw41880 raw41880Labels = mixedMoment B raw41880step0 raw41880step0Labels := by
      have hz : ∀ j, raw41880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41880step0 = (fun i j => raw41880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41880step0 raw41880; decide +kernel
      have hl : raw41880step0Labels = raw41880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41880 raw41880Labels permutation434 hz
    mixedMoment B raw41880step0 raw41880step0Labels = mixedMoment B raw41880step1 raw41880step1Labels := by
      have ha : raw41880step1 = (fun i j => raw41880step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41880step1 raw41880step0; decide +kernel
      have hl : raw41880step1Labels = raw41880step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41880step0 raw41880step0Labels permutation38 permutation2
    mixedMoment B raw41880step1 raw41880step1Labels = mixedMoment B raw41880step2 raw41880step2Labels := by
      have ha : raw41880step2 = raw41880step1 := by apply Matrix.ext; unfold raw41880step2 raw41880step1; decide +kernel
      have hl : raw41880step1Labels = labelEmbedding1 ∘ raw41880step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41880step1 raw41880step1Labels raw41880step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

theorem canonical41881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41881 raw41881Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw41881 raw41881Labels = mixedMoment B raw41881step0 raw41881step0Labels := by
      have hz : ∀ j, raw41881 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41881step0 = (fun i j => raw41881 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41881step0 raw41881; decide +kernel
      have hl : raw41881step0Labels = raw41881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41881 raw41881Labels permutation434 hz
    mixedMoment B raw41881step0 raw41881step0Labels = mixedMoment B raw41881step1 raw41881step1Labels := by
      have ha : raw41881step1 = (fun i j => raw41881step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41881step1 raw41881step0; decide +kernel
      have hl : raw41881step1Labels = raw41881step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41881step0 raw41881step0Labels permutation53 permutation7
    mixedMoment B raw41881step1 raw41881step1Labels = mixedMoment B raw41881step2 raw41881step2Labels := by
      have ha : raw41881step2 = -raw41881step1 := by apply Matrix.ext; change ∀ i j, raw41881step2 i j = -(raw41881step1 i j); unfold raw41881step2 raw41881step1; decide +kernel
      have hl : raw41881step2Labels = raw41881step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41881step2 raw41881step2Labels = mixedMoment B raw41881step3 raw41881step3Labels := by
      have ha : raw41881step3 = raw41881step2 := by apply Matrix.ext; unfold raw41881step3 raw41881step2; decide +kernel
      have hl : raw41881step2Labels = labelEmbedding6 ∘ raw41881step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41881step2 raw41881step2Labels raw41881step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4475 node4475Labels := by rfl

theorem canonical41882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41882 raw41882Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw41882 raw41882Labels = mixedMoment B raw41882step0 raw41882step0Labels := by
      have hz : ∀ j, raw41882 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41882step0 = (fun i j => raw41882 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41882step0 raw41882; decide +kernel
      have hl : raw41882step0Labels = raw41882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41882 raw41882Labels permutation434 hz
    mixedMoment B raw41882step0 raw41882step0Labels = mixedMoment B raw41882step1 raw41882step1Labels := by
      have ha : raw41882step1 = (fun i j => raw41882step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41882step1 raw41882step0; decide +kernel
      have hl : raw41882step1Labels = raw41882step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41882step0 raw41882step0Labels permutation38 permutation2
    mixedMoment B raw41882step1 raw41882step1Labels = mixedMoment B raw41882step2 raw41882step2Labels := by
      have ha : raw41882step2 = raw41882step1 := by apply Matrix.ext; unfold raw41882step2 raw41882step1; decide +kernel
      have hl : raw41882step1Labels = labelEmbedding1 ∘ raw41882step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41882step1 raw41882step1Labels raw41882step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

theorem canonical41883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41883 raw41883Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw41883 raw41883Labels = mixedMoment B raw41883step0 raw41883step0Labels := by
      have hz : ∀ j, raw41883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41883step0 = (fun i j => raw41883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41883step0 raw41883; decide +kernel
      have hl : raw41883step0Labels = raw41883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41883 raw41883Labels permutation434 hz
    mixedMoment B raw41883step0 raw41883step0Labels = mixedMoment B raw41883step1 raw41883step1Labels := by
      have ha : raw41883step1 = (fun i j => raw41883step0 (permutation47 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41883step1 raw41883step0; decide +kernel
      have hl : raw41883step1Labels = raw41883step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41883step0 raw41883step0Labels permutation47 permutation7
    mixedMoment B raw41883step1 raw41883step1Labels = mixedMoment B raw41883step2 raw41883step2Labels := by
      have ha : raw41883step2 = -raw41883step1 := by apply Matrix.ext; change ∀ i j, raw41883step2 i j = -(raw41883step1 i j); unfold raw41883step2 raw41883step1; decide +kernel
      have hl : raw41883step2Labels = raw41883step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41883step2 raw41883step2Labels = mixedMoment B raw41883step3 raw41883step3Labels := by
      have ha : raw41883step3 = raw41883step2 := by apply Matrix.ext; unfold raw41883step3 raw41883step2; decide +kernel
      have hl : raw41883step2Labels = labelEmbedding6 ∘ raw41883step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41883step2 raw41883step2Labels raw41883step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

theorem canonical41884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41884 raw41884Labels = mixedMoment B node1712 node1712Labels := by
  calc
    mixedMoment B raw41884 raw41884Labels = mixedMoment B raw41884step0 raw41884step0Labels := by
      have hz : ∀ j, raw41884 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41884step0 = (fun i j => raw41884 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41884step0 raw41884; decide +kernel
      have hl : raw41884step0Labels = raw41884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41884 raw41884Labels permutation434 hz
    mixedMoment B raw41884step0 raw41884step0Labels = mixedMoment B raw41884step1 raw41884step1Labels := by
      have ha : raw41884step1 = (fun i j => raw41884step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41884step1 raw41884step0; decide +kernel
      have hl : raw41884step1Labels = raw41884step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41884step0 raw41884step0Labels permutation38 permutation2
    mixedMoment B raw41884step1 raw41884step1Labels = mixedMoment B raw41884step2 raw41884step2Labels := by
      have ha : raw41884step2 = raw41884step1 := by apply Matrix.ext; unfold raw41884step2 raw41884step1; decide +kernel
      have hl : raw41884step1Labels = labelEmbedding1 ∘ raw41884step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41884step1 raw41884step1Labels raw41884step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1712 node1712Labels := by rfl

theorem canonical41885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41885 raw41885Labels = mixedMoment B node4368 node4368Labels := by
  calc
    mixedMoment B raw41885 raw41885Labels = mixedMoment B raw41885step0 raw41885step0Labels := by
      have hz : ∀ j, raw41885 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41885step0 = (fun i j => raw41885 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41885step0 raw41885; decide +kernel
      have hl : raw41885step0Labels = raw41885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41885 raw41885Labels permutation434 hz
    mixedMoment B raw41885step0 raw41885step0Labels = mixedMoment B raw41885step1 raw41885step1Labels := by
      have ha : raw41885step1 = (fun i j => raw41885step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41885step1 raw41885step0; decide +kernel
      have hl : raw41885step1Labels = raw41885step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41885step0 raw41885step0Labels permutation46 permutation7
    mixedMoment B raw41885step1 raw41885step1Labels = mixedMoment B raw41885step2 raw41885step2Labels := by
      have ha : raw41885step2 = -raw41885step1 := by apply Matrix.ext; change ∀ i j, raw41885step2 i j = -(raw41885step1 i j); unfold raw41885step2 raw41885step1; decide +kernel
      have hl : raw41885step2Labels = raw41885step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41885step2 raw41885step2Labels = mixedMoment B raw41885step3 raw41885step3Labels := by
      have ha : raw41885step3 = raw41885step2 := by apply Matrix.ext; unfold raw41885step3 raw41885step2; decide +kernel
      have hl : raw41885step2Labels = labelEmbedding6 ∘ raw41885step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41885step2 raw41885step2Labels raw41885step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4368 node4368Labels := by rfl

theorem canonical41886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41886 raw41886Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw41886 raw41886Labels = mixedMoment B raw41886step0 raw41886step0Labels := by
      have ha : raw41886step0 = (fun i j => raw41886 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41886step0 raw41886; decide +kernel
      have hl : raw41886step0Labels = raw41886Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41886 raw41886Labels permutation206 permutation2
    mixedMoment B raw41886step0 raw41886step0Labels = mixedMoment B raw41886step1 raw41886step1Labels := by
      have ha : raw41886step1 = raw41886step0 := by apply Matrix.ext; unfold raw41886step1 raw41886step0; decide +kernel
      have hl : raw41886step0Labels = labelEmbedding1 ∘ raw41886step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41886step0 raw41886step0Labels raw41886step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

theorem canonical41887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41887 raw41887Labels = mixedMoment B node4328 node4328Labels := by
  calc
    mixedMoment B raw41887 raw41887Labels = mixedMoment B raw41887step0 raw41887step0Labels := by
      have ha : raw41887step0 = (fun i j => raw41887 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41887step0 raw41887; decide +kernel
      have hl : raw41887step0Labels = raw41887Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41887 raw41887Labels permutation214 permutation7
    mixedMoment B raw41887step0 raw41887step0Labels = mixedMoment B raw41887step1 raw41887step1Labels := by
      have ha : raw41887step1 = -raw41887step0 := by apply Matrix.ext; change ∀ i j, raw41887step1 i j = -(raw41887step0 i j); unfold raw41887step1 raw41887step0; decide +kernel
      have hl : raw41887step1Labels = raw41887step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41887step1 raw41887step1Labels = mixedMoment B raw41887step2 raw41887step2Labels := by
      have ha : raw41887step2 = raw41887step1 := by apply Matrix.ext; unfold raw41887step2 raw41887step1; decide +kernel
      have hl : raw41887step1Labels = labelEmbedding6 ∘ raw41887step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41887step1 raw41887step1Labels raw41887step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4328 node4328Labels := by rfl

theorem canonical41888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41888 raw41888Labels = mixedMoment B node1711 node1711Labels := by
  calc
    mixedMoment B raw41888 raw41888Labels = mixedMoment B raw41888step0 raw41888step0Labels := by
      have ha : raw41888step0 = (fun i j => raw41888 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41888step0 raw41888; decide +kernel
      have hl : raw41888step0Labels = raw41888Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41888 raw41888Labels permutation180 permutation2
    mixedMoment B raw41888step0 raw41888step0Labels = mixedMoment B raw41888step1 raw41888step1Labels := by
      have ha : raw41888step1 = raw41888step0 := by apply Matrix.ext; unfold raw41888step1 raw41888step0; decide +kernel
      have hl : raw41888step0Labels = labelEmbedding1 ∘ raw41888step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41888step0 raw41888step0Labels raw41888step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1711 node1711Labels := by rfl

theorem canonical41889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41889 raw41889Labels = mixedMoment B node4366 node4366Labels := by
  calc
    mixedMoment B raw41889 raw41889Labels = mixedMoment B raw41889step0 raw41889step0Labels := by
      have ha : raw41889step0 = (fun i j => raw41889 (permutation255 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41889step0 raw41889; decide +kernel
      have hl : raw41889step0Labels = raw41889Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41889 raw41889Labels permutation255 permutation7
    mixedMoment B raw41889step0 raw41889step0Labels = mixedMoment B raw41889step1 raw41889step1Labels := by
      have ha : raw41889step1 = -raw41889step0 := by apply Matrix.ext; change ∀ i j, raw41889step1 i j = -(raw41889step0 i j); unfold raw41889step1 raw41889step0; decide +kernel
      have hl : raw41889step1Labels = raw41889step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41889step1 raw41889step1Labels = mixedMoment B raw41889step2 raw41889step2Labels := by
      have ha : raw41889step2 = raw41889step1 := by apply Matrix.ext; unfold raw41889step2 raw41889step1; decide +kernel
      have hl : raw41889step1Labels = labelEmbedding6 ∘ raw41889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41889step1 raw41889step1Labels raw41889step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4366 node4366Labels := by rfl

theorem canonical41890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41890 raw41890Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw41890 raw41890Labels = mixedMoment B raw41890step0 raw41890step0Labels := by
      have ha : raw41890step0 = (fun i j => raw41890 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41890step0 raw41890; decide +kernel
      have hl : raw41890step0Labels = raw41890Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41890 raw41890Labels permutation179 permutation2
    mixedMoment B raw41890step0 raw41890step0Labels = mixedMoment B raw41890step1 raw41890step1Labels := by
      have ha : raw41890step1 = raw41890step0 := by apply Matrix.ext; unfold raw41890step1 raw41890step0; decide +kernel
      have hl : raw41890step0Labels = labelEmbedding1 ∘ raw41890step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41890step0 raw41890step0Labels raw41890step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

theorem canonical41891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41891 raw41891Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw41891 raw41891Labels = mixedMoment B raw41891step0 raw41891step0Labels := by
      have ha : raw41891step0 = (fun i j => raw41891 (permutation243 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41891step0 raw41891; decide +kernel
      have hl : raw41891step0Labels = raw41891Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41891 raw41891Labels permutation243 permutation7
    mixedMoment B raw41891step0 raw41891step0Labels = mixedMoment B raw41891step1 raw41891step1Labels := by
      have ha : raw41891step1 = -raw41891step0 := by apply Matrix.ext; change ∀ i j, raw41891step1 i j = -(raw41891step0 i j); unfold raw41891step1 raw41891step0; decide +kernel
      have hl : raw41891step1Labels = raw41891step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41891step1 raw41891step1Labels = mixedMoment B raw41891step2 raw41891step2Labels := by
      have ha : raw41891step2 = raw41891step1 := by apply Matrix.ext; unfold raw41891step2 raw41891step1; decide +kernel
      have hl : raw41891step1Labels = labelEmbedding6 ∘ raw41891step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41891step1 raw41891step1Labels raw41891step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4439 node4439Labels := by rfl

theorem canonical41892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41892 raw41892Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw41892 raw41892Labels = mixedMoment B raw41892step0 raw41892step0Labels := by
      have hz : ∀ j, raw41892 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41892step0 = (fun i j => raw41892 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41892step0 raw41892; decide +kernel
      have hl : raw41892step0Labels = raw41892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41892 raw41892Labels permutation434 hz
    mixedMoment B raw41892step0 raw41892step0Labels = mixedMoment B raw41892step1 raw41892step1Labels := by
      have hz : ∀ j, raw41892step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41892step1 = (fun i j => raw41892step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41892step1 raw41892step0; decide +kernel
      have hl : raw41892step1Labels = raw41892step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41892step0 raw41892step0Labels permutation80 hz
    mixedMoment B raw41892step1 raw41892step1Labels = mixedMoment B raw41892step2 raw41892step2Labels := by
      have ha : raw41892step2 = raw41892step1 := by apply Matrix.ext; unfold raw41892step2 raw41892step1; decide +kernel
      have hl : raw41892step1Labels = labelEmbedding1 ∘ raw41892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41892step1 raw41892step1Labels raw41892step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1740 node1740Labels := by rfl

theorem canonical41893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41893 raw41893Labels = mixedMoment B node4480 node4480Labels := by
  calc
    mixedMoment B raw41893 raw41893Labels = mixedMoment B raw41893step0 raw41893step0Labels := by
      have hz : ∀ j, raw41893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41893step0 = (fun i j => raw41893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41893step0 raw41893; decide +kernel
      have hl : raw41893step0Labels = raw41893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41893 raw41893Labels permutation434 hz
    mixedMoment B raw41893step0 raw41893step0Labels = mixedMoment B raw41893step1 raw41893step1Labels := by
      have hz : ∀ j, raw41893step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41893step1 = (fun i j => raw41893step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41893step1 raw41893step0; decide +kernel
      have hl : raw41893step1Labels = raw41893step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41893step0 raw41893step0Labels permutation80 hz
    mixedMoment B raw41893step1 raw41893step1Labels = mixedMoment B raw41893step2 raw41893step2Labels := by
      have ha : raw41893step2 = (fun i j => raw41893step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41893step2 raw41893step1; decide +kernel
      have hl : raw41893step2Labels = raw41893step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41893step1 raw41893step1Labels permutation12 permutation7
    mixedMoment B raw41893step2 raw41893step2Labels = mixedMoment B raw41893step3 raw41893step3Labels := by
      have ha : raw41893step3 = -raw41893step2 := by apply Matrix.ext; change ∀ i j, raw41893step3 i j = -(raw41893step2 i j); unfold raw41893step3 raw41893step2; decide +kernel
      have hl : raw41893step3Labels = raw41893step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41893step3 raw41893step3Labels = mixedMoment B raw41893step4 raw41893step4Labels := by
      have ha : raw41893step4 = raw41893step3 := by apply Matrix.ext; unfold raw41893step4 raw41893step3; decide +kernel
      have hl : raw41893step3Labels = labelEmbedding6 ∘ raw41893step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41893step3 raw41893step3Labels raw41893step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4480 node4480Labels := by rfl

theorem canonical41894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41894 raw41894Labels = mixedMoment B node1735 node1735Labels := by
  calc
    mixedMoment B raw41894 raw41894Labels = mixedMoment B raw41894step0 raw41894step0Labels := by
      have hz : ∀ j, raw41894 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41894step0 = (fun i j => raw41894 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41894step0 raw41894; decide +kernel
      have hl : raw41894step0Labels = raw41894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41894 raw41894Labels permutation434 hz
    mixedMoment B raw41894step0 raw41894step0Labels = mixedMoment B raw41894step1 raw41894step1Labels := by
      have hz : ∀ j, raw41894step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41894step1 = (fun i j => raw41894step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41894step1 raw41894step0; decide +kernel
      have hl : raw41894step1Labels = raw41894step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41894step0 raw41894step0Labels permutation80 hz
    mixedMoment B raw41894step1 raw41894step1Labels = mixedMoment B raw41894step2 raw41894step2Labels := by
      have ha : raw41894step2 = raw41894step1 := by apply Matrix.ext; unfold raw41894step2 raw41894step1; decide +kernel
      have hl : raw41894step1Labels = labelEmbedding1 ∘ raw41894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41894step1 raw41894step1Labels raw41894step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1735 node1735Labels := by rfl

theorem canonical41895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41895 raw41895Labels = mixedMoment B node4373 node4373Labels := by
  calc
    mixedMoment B raw41895 raw41895Labels = mixedMoment B raw41895step0 raw41895step0Labels := by
      have hz : ∀ j, raw41895 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41895step0 = (fun i j => raw41895 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41895step0 raw41895; decide +kernel
      have hl : raw41895step0Labels = raw41895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41895 raw41895Labels permutation434 hz
    mixedMoment B raw41895step0 raw41895step0Labels = mixedMoment B raw41895step1 raw41895step1Labels := by
      have hz : ∀ j, raw41895step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41895step1 = (fun i j => raw41895step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41895step1 raw41895step0; decide +kernel
      have hl : raw41895step1Labels = raw41895step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41895step0 raw41895step0Labels permutation80 hz
    mixedMoment B raw41895step1 raw41895step1Labels = mixedMoment B raw41895step2 raw41895step2Labels := by
      have ha : raw41895step2 = (fun i j => raw41895step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41895step2 raw41895step1; decide +kernel
      have hl : raw41895step2Labels = raw41895step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41895step1 raw41895step1Labels permutation10 permutation7
    mixedMoment B raw41895step2 raw41895step2Labels = mixedMoment B raw41895step3 raw41895step3Labels := by
      have ha : raw41895step3 = -raw41895step2 := by apply Matrix.ext; change ∀ i j, raw41895step3 i j = -(raw41895step2 i j); unfold raw41895step3 raw41895step2; decide +kernel
      have hl : raw41895step3Labels = raw41895step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41895step3 raw41895step3Labels = mixedMoment B raw41895step4 raw41895step4Labels := by
      have ha : raw41895step4 = raw41895step3 := by apply Matrix.ext; unfold raw41895step4 raw41895step3; decide +kernel
      have hl : raw41895step3Labels = labelEmbedding6 ∘ raw41895step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41895step3 raw41895step3Labels raw41895step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4373 node4373Labels := by rfl

theorem canonical41896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41896 raw41896Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw41896 raw41896Labels = mixedMoment B raw41896step0 raw41896step0Labels := by
      have hz : ∀ j, raw41896 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41896step0 = (fun i j => raw41896 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41896step0 raw41896; decide +kernel
      have hl : raw41896step0Labels = raw41896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41896 raw41896Labels permutation346 hz
    mixedMoment B raw41896step0 raw41896step0Labels = mixedMoment B raw41896step1 raw41896step1Labels := by
      have ha : raw41896step1 = (fun i j => raw41896step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41896step1 raw41896step0; decide +kernel
      have hl : raw41896step1Labels = raw41896step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41896step0 raw41896step0Labels permutation38 permutation2
    mixedMoment B raw41896step1 raw41896step1Labels = mixedMoment B raw41896step2 raw41896step2Labels := by
      have ha : raw41896step2 = raw41896step1 := by apply Matrix.ext; unfold raw41896step2 raw41896step1; decide +kernel
      have hl : raw41896step1Labels = labelEmbedding1 ∘ raw41896step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41896step1 raw41896step1Labels raw41896step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

theorem canonical41897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41897 raw41897Labels = mixedMoment B node4334 node4334Labels := by
  calc
    mixedMoment B raw41897 raw41897Labels = mixedMoment B raw41897step0 raw41897step0Labels := by
      have hz : ∀ j, raw41897 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41897step0 = (fun i j => raw41897 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41897step0 raw41897; decide +kernel
      have hl : raw41897step0Labels = raw41897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41897 raw41897Labels permutation346 hz
    mixedMoment B raw41897step0 raw41897step0Labels = mixedMoment B raw41897step1 raw41897step1Labels := by
      have ha : raw41897step1 = (fun i j => raw41897step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41897step1 raw41897step0; decide +kernel
      have hl : raw41897step1Labels = raw41897step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41897step0 raw41897step0Labels permutation40 permutation7
    mixedMoment B raw41897step1 raw41897step1Labels = mixedMoment B raw41897step2 raw41897step2Labels := by
      have ha : raw41897step2 = -raw41897step1 := by apply Matrix.ext; change ∀ i j, raw41897step2 i j = -(raw41897step1 i j); unfold raw41897step2 raw41897step1; decide +kernel
      have hl : raw41897step2Labels = raw41897step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41897step2 raw41897step2Labels = mixedMoment B raw41897step3 raw41897step3Labels := by
      have ha : raw41897step3 = raw41897step2 := by apply Matrix.ext; unfold raw41897step3 raw41897step2; decide +kernel
      have hl : raw41897step2Labels = labelEmbedding6 ∘ raw41897step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41897step2 raw41897step2Labels raw41897step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4334 node4334Labels := by rfl

theorem canonical41898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41898 raw41898Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw41898 raw41898Labels = mixedMoment B raw41898step0 raw41898step0Labels := by
      have hz : ∀ j, raw41898 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41898step0 = (fun i j => raw41898 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41898step0 raw41898; decide +kernel
      have hl : raw41898step0Labels = raw41898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41898 raw41898Labels permutation346 hz
    mixedMoment B raw41898step0 raw41898step0Labels = mixedMoment B raw41898step1 raw41898step1Labels := by
      have ha : raw41898step1 = (fun i j => raw41898step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41898step1 raw41898step0; decide +kernel
      have hl : raw41898step1Labels = raw41898step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41898step0 raw41898step0Labels permutation37 permutation2
    mixedMoment B raw41898step1 raw41898step1Labels = mixedMoment B raw41898step2 raw41898step2Labels := by
      have ha : raw41898step2 = raw41898step1 := by apply Matrix.ext; unfold raw41898step2 raw41898step1; decide +kernel
      have hl : raw41898step1Labels = labelEmbedding1 ∘ raw41898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41898step1 raw41898step1Labels raw41898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

theorem canonical41899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41899 raw41899Labels = mixedMoment B node4372 node4372Labels := by
  calc
    mixedMoment B raw41899 raw41899Labels = mixedMoment B raw41899step0 raw41899step0Labels := by
      have hz : ∀ j, raw41899 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41899step0 = (fun i j => raw41899 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41899step0 raw41899; decide +kernel
      have hl : raw41899step0Labels = raw41899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41899 raw41899Labels permutation346 hz
    mixedMoment B raw41899step0 raw41899step0Labels = mixedMoment B raw41899step1 raw41899step1Labels := by
      have ha : raw41899step1 = (fun i j => raw41899step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41899step1 raw41899step0; decide +kernel
      have hl : raw41899step1Labels = raw41899step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41899step0 raw41899step0Labels permutation54 permutation7
    mixedMoment B raw41899step1 raw41899step1Labels = mixedMoment B raw41899step2 raw41899step2Labels := by
      have ha : raw41899step2 = -raw41899step1 := by apply Matrix.ext; change ∀ i j, raw41899step2 i j = -(raw41899step1 i j); unfold raw41899step2 raw41899step1; decide +kernel
      have hl : raw41899step2Labels = raw41899step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41899step2 raw41899step2Labels = mixedMoment B raw41899step3 raw41899step3Labels := by
      have ha : raw41899step3 = raw41899step2 := by apply Matrix.ext; unfold raw41899step3 raw41899step2; decide +kernel
      have hl : raw41899step2Labels = labelEmbedding6 ∘ raw41899step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41899step2 raw41899step2Labels raw41899step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4372 node4372Labels := by rfl

theorem canonical41900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41900 raw41900Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw41900 raw41900Labels = mixedMoment B raw41900step0 raw41900step0Labels := by
      have hz : ∀ j, raw41900 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41900step0 = (fun i j => raw41900 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41900step0 raw41900; decide +kernel
      have hl : raw41900step0Labels = raw41900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41900 raw41900Labels permutation346 hz
    mixedMoment B raw41900step0 raw41900step0Labels = mixedMoment B raw41900step1 raw41900step1Labels := by
      have ha : raw41900step1 = (fun i j => raw41900step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41900step1 raw41900step0; decide +kernel
      have hl : raw41900step1Labels = raw41900step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41900step0 raw41900step0Labels permutation35 permutation2
    mixedMoment B raw41900step1 raw41900step1Labels = mixedMoment B raw41900step2 raw41900step2Labels := by
      have ha : raw41900step2 = raw41900step1 := by apply Matrix.ext; unfold raw41900step2 raw41900step1; decide +kernel
      have hl : raw41900step1Labels = labelEmbedding1 ∘ raw41900step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41900step1 raw41900step1Labels raw41900step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

theorem canonical41901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41901 raw41901Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw41901 raw41901Labels = mixedMoment B raw41901step0 raw41901step0Labels := by
      have hz : ∀ j, raw41901 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41901step0 = (fun i j => raw41901 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41901step0 raw41901; decide +kernel
      have hl : raw41901step0Labels = raw41901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41901 raw41901Labels permutation346 hz
    mixedMoment B raw41901step0 raw41901step0Labels = mixedMoment B raw41901step1 raw41901step1Labels := by
      have ha : raw41901step1 = (fun i j => raw41901step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41901step1 raw41901step0; decide +kernel
      have hl : raw41901step1Labels = raw41901step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41901step0 raw41901step0Labels permutation48 permutation7
    mixedMoment B raw41901step1 raw41901step1Labels = mixedMoment B raw41901step2 raw41901step2Labels := by
      have ha : raw41901step2 = -raw41901step1 := by apply Matrix.ext; change ∀ i j, raw41901step2 i j = -(raw41901step1 i j); unfold raw41901step2 raw41901step1; decide +kernel
      have hl : raw41901step2Labels = raw41901step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41901step2 raw41901step2Labels = mixedMoment B raw41901step3 raw41901step3Labels := by
      have ha : raw41901step3 = raw41901step2 := by apply Matrix.ext; unfold raw41901step3 raw41901step2; decide +kernel
      have hl : raw41901step2Labels = labelEmbedding6 ∘ raw41901step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41901step2 raw41901step2Labels raw41901step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4444 node4444Labels := by rfl

theorem canonical41902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41902 raw41902Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw41902 raw41902Labels = mixedMoment B raw41902step0 raw41902step0Labels := by
      have ha : raw41902step0 = (fun i j => raw41902 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41902step0 raw41902; decide +kernel
      have hl : raw41902step0Labels = raw41902Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41902 raw41902Labels permutation181 permutation2
    mixedMoment B raw41902step0 raw41902step0Labels = mixedMoment B raw41902step1 raw41902step1Labels := by
      have ha : raw41902step1 = raw41902step0 := by apply Matrix.ext; unfold raw41902step1 raw41902step0; decide +kernel
      have hl : raw41902step0Labels = labelEmbedding1 ∘ raw41902step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41902step0 raw41902step0Labels raw41902step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

theorem canonical41903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41903 raw41903Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw41903 raw41903Labels = mixedMoment B raw41903step0 raw41903step0Labels := by
      have ha : raw41903step0 = (fun i j => raw41903 (permutation198 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41903step0 raw41903; decide +kernel
      have hl : raw41903step0Labels = raw41903Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41903 raw41903Labels permutation198 permutation7
    mixedMoment B raw41903step0 raw41903step0Labels = mixedMoment B raw41903step1 raw41903step1Labels := by
      have ha : raw41903step1 = -raw41903step0 := by apply Matrix.ext; change ∀ i j, raw41903step1 i j = -(raw41903step0 i j); unfold raw41903step1 raw41903step0; decide +kernel
      have hl : raw41903step1Labels = raw41903step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41903step1 raw41903step1Labels = mixedMoment B raw41903step2 raw41903step2Labels := by
      have ha : raw41903step2 = raw41903step1 := by apply Matrix.ext; unfold raw41903step2 raw41903step1; decide +kernel
      have hl : raw41903step1Labels = labelEmbedding6 ∘ raw41903step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41903step1 raw41903step1Labels raw41903step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4332 node4332Labels := by rfl

theorem canonical41904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41904 raw41904Labels = mixedMoment B node1699 node1699Labels := by
  calc
    mixedMoment B raw41904 raw41904Labels = mixedMoment B raw41904step0 raw41904step0Labels := by
      have ha : raw41904step0 = raw41904 := by apply Matrix.ext; unfold raw41904step0 raw41904; decide +kernel
      have hl : raw41904Labels = labelEmbedding1 ∘ raw41904step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41904 raw41904Labels raw41904step0Labels labelEmbedding1 hl
    _ = mixedMoment B node1699 node1699Labels := by rfl

theorem canonical41905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41905 raw41905Labels = mixedMoment B node4473 node4473Labels := by
  calc
    mixedMoment B raw41905 raw41905Labels = mixedMoment B raw41905step0 raw41905step0Labels := by
      have ha : raw41905step0 = (fun i j => raw41905 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41905step0 raw41905; decide +kernel
      have hl : raw41905step0Labels = raw41905Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41905 raw41905Labels permutation246 permutation7
    mixedMoment B raw41905step0 raw41905step0Labels = mixedMoment B raw41905step1 raw41905step1Labels := by
      have ha : raw41905step1 = -raw41905step0 := by apply Matrix.ext; change ∀ i j, raw41905step1 i j = -(raw41905step0 i j); unfold raw41905step1 raw41905step0; decide +kernel
      have hl : raw41905step1Labels = raw41905step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41905step1 raw41905step1Labels = mixedMoment B raw41905step2 raw41905step2Labels := by
      have ha : raw41905step2 = raw41905step1 := by apply Matrix.ext; unfold raw41905step2 raw41905step1; decide +kernel
      have hl : raw41905step1Labels = labelEmbedding6 ∘ raw41905step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41905step1 raw41905step1Labels raw41905step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4473 node4473Labels := by rfl

theorem canonical41906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41906 raw41906Labels = mixedMoment B node1697 node1697Labels := by
  calc
    mixedMoment B raw41906 raw41906Labels = mixedMoment B raw41906step0 raw41906step0Labels := by
      have ha : raw41906step0 = raw41906 := by apply Matrix.ext; unfold raw41906step0 raw41906; decide +kernel
      have hl : raw41906Labels = labelEmbedding1 ∘ raw41906step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41906 raw41906Labels raw41906step0Labels labelEmbedding1 hl
    _ = mixedMoment B node1697 node1697Labels := by rfl

theorem canonical41907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41907 raw41907Labels = mixedMoment B node4363 node4363Labels := by
  calc
    mixedMoment B raw41907 raw41907Labels = mixedMoment B raw41907step0 raw41907step0Labels := by
      have ha : raw41907step0 = (fun i j => raw41907 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41907step0 raw41907; decide +kernel
      have hl : raw41907step0Labels = raw41907Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41907 raw41907Labels permutation224 permutation7
    mixedMoment B raw41907step0 raw41907step0Labels = mixedMoment B raw41907step1 raw41907step1Labels := by
      have ha : raw41907step1 = -raw41907step0 := by apply Matrix.ext; change ∀ i j, raw41907step1 i j = -(raw41907step0 i j); unfold raw41907step1 raw41907step0; decide +kernel
      have hl : raw41907step1Labels = raw41907step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41907step1 raw41907step1Labels = mixedMoment B raw41907step2 raw41907step2Labels := by
      have ha : raw41907step2 = raw41907step1 := by apply Matrix.ext; unfold raw41907step2 raw41907step1; decide +kernel
      have hl : raw41907step1Labels = labelEmbedding6 ∘ raw41907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41907step1 raw41907step1Labels raw41907step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4363 node4363Labels := by rfl

theorem canonical41908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41908 raw41908Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw41908 raw41908Labels = mixedMoment B raw41908step0 raw41908step0Labels := by
      have hz : ∀ j, raw41908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41908step0 = (fun i j => raw41908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41908step0 raw41908; decide +kernel
      have hl : raw41908step0Labels = raw41908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41908 raw41908Labels permutation434 hz
    mixedMoment B raw41908step0 raw41908step0Labels = mixedMoment B raw41908step1 raw41908step1Labels := by
      have ha : raw41908step1 = raw41908step0 := by apply Matrix.ext; unfold raw41908step1 raw41908step0; decide +kernel
      have hl : raw41908step0Labels = labelEmbedding1 ∘ raw41908step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41908step0 raw41908step0Labels raw41908step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

theorem canonical41909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41909 raw41909Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw41909 raw41909Labels = mixedMoment B raw41909step0 raw41909step0Labels := by
      have hz : ∀ j, raw41909 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41909step0 = (fun i j => raw41909 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41909step0 raw41909; decide +kernel
      have hl : raw41909step0Labels = raw41909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41909 raw41909Labels permutation434 hz
    mixedMoment B raw41909step0 raw41909step0Labels = mixedMoment B raw41909step1 raw41909step1Labels := by
      have ha : raw41909step1 = (fun i j => raw41909step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41909step1 raw41909step0; decide +kernel
      have hl : raw41909step1Labels = raw41909step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41909step0 raw41909step0Labels permutation50 permutation7
    mixedMoment B raw41909step1 raw41909step1Labels = mixedMoment B raw41909step2 raw41909step2Labels := by
      have ha : raw41909step2 = -raw41909step1 := by apply Matrix.ext; change ∀ i j, raw41909step2 i j = -(raw41909step1 i j); unfold raw41909step2 raw41909step1; decide +kernel
      have hl : raw41909step2Labels = raw41909step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41909step2 raw41909step2Labels = mixedMoment B raw41909step3 raw41909step3Labels := by
      have ha : raw41909step3 = raw41909step2 := by apply Matrix.ext; unfold raw41909step3 raw41909step2; decide +kernel
      have hl : raw41909step2Labels = labelEmbedding6 ∘ raw41909step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41909step2 raw41909step2Labels raw41909step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4474 node4474Labels := by rfl

theorem canonical41910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41910 raw41910Labels = mixedMoment B node1704 node1704Labels := by
  calc
    mixedMoment B raw41910 raw41910Labels = mixedMoment B raw41910step0 raw41910step0Labels := by
      have hz : ∀ j, raw41910 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41910step0 = (fun i j => raw41910 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41910step0 raw41910; decide +kernel
      have hl : raw41910step0Labels = raw41910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41910 raw41910Labels permutation434 hz
    mixedMoment B raw41910step0 raw41910step0Labels = mixedMoment B raw41910step1 raw41910step1Labels := by
      have ha : raw41910step1 = raw41910step0 := by apply Matrix.ext; unfold raw41910step1 raw41910step0; decide +kernel
      have hl : raw41910step0Labels = labelEmbedding1 ∘ raw41910step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41910step0 raw41910step0Labels raw41910step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1704 node1704Labels := by rfl

theorem canonical41911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41911 raw41911Labels = mixedMoment B node4365 node4365Labels := by
  calc
    mixedMoment B raw41911 raw41911Labels = mixedMoment B raw41911step0 raw41911step0Labels := by
      have hz : ∀ j, raw41911 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41911step0 = (fun i j => raw41911 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41911step0 raw41911; decide +kernel
      have hl : raw41911step0Labels = raw41911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41911 raw41911Labels permutation434 hz
    mixedMoment B raw41911step0 raw41911step0Labels = mixedMoment B raw41911step1 raw41911step1Labels := by
      have ha : raw41911step1 = (fun i j => raw41911step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41911step1 raw41911step0; decide +kernel
      have hl : raw41911step1Labels = raw41911step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41911step0 raw41911step0Labels permutation44 permutation7
    mixedMoment B raw41911step1 raw41911step1Labels = mixedMoment B raw41911step2 raw41911step2Labels := by
      have ha : raw41911step2 = -raw41911step1 := by apply Matrix.ext; change ∀ i j, raw41911step2 i j = -(raw41911step1 i j); unfold raw41911step2 raw41911step1; decide +kernel
      have hl : raw41911step2Labels = raw41911step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41911step2 raw41911step2Labels = mixedMoment B raw41911step3 raw41911step3Labels := by
      have ha : raw41911step3 = raw41911step2 := by apply Matrix.ext; unfold raw41911step3 raw41911step2; decide +kernel
      have hl : raw41911step2Labels = labelEmbedding6 ∘ raw41911step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41911step2 raw41911step2Labels raw41911step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4365 node4365Labels := by rfl

theorem canonical41912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41912 raw41912Labels = mixedMoment B node1703 node1703Labels := by
  calc
    mixedMoment B raw41912 raw41912Labels = mixedMoment B raw41912step0 raw41912step0Labels := by
      have ha : raw41912step0 = (fun i j => raw41912 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41912step0 raw41912; decide +kernel
      have hl : raw41912step0Labels = raw41912Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41912 raw41912Labels permutation157 permutation2
    mixedMoment B raw41912step0 raw41912step0Labels = mixedMoment B raw41912step1 raw41912step1Labels := by
      have ha : raw41912step1 = raw41912step0 := by apply Matrix.ext; unfold raw41912step1 raw41912step0; decide +kernel
      have hl : raw41912step0Labels = labelEmbedding1 ∘ raw41912step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41912step0 raw41912step0Labels raw41912step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1703 node1703Labels := by rfl

theorem canonical41913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41913 raw41913Labels = mixedMoment B node4364 node4364Labels := by
  calc
    mixedMoment B raw41913 raw41913Labels = mixedMoment B raw41913step0 raw41913step0Labels := by
      have ha : raw41913step0 = (fun i j => raw41913 (permutation247 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41913step0 raw41913; decide +kernel
      have hl : raw41913step0Labels = raw41913Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41913 raw41913Labels permutation247 permutation7
    mixedMoment B raw41913step0 raw41913step0Labels = mixedMoment B raw41913step1 raw41913step1Labels := by
      have ha : raw41913step1 = -raw41913step0 := by apply Matrix.ext; change ∀ i j, raw41913step1 i j = -(raw41913step0 i j); unfold raw41913step1 raw41913step0; decide +kernel
      have hl : raw41913step1Labels = raw41913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41913step1 raw41913step1Labels = mixedMoment B raw41913step2 raw41913step2Labels := by
      have ha : raw41913step2 = raw41913step1 := by apply Matrix.ext; unfold raw41913step2 raw41913step1; decide +kernel
      have hl : raw41913step1Labels = labelEmbedding6 ∘ raw41913step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41913step1 raw41913step1Labels raw41913step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4364 node4364Labels := by rfl

theorem canonical41914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41914 raw41914Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw41914 raw41914Labels = mixedMoment B raw41914step0 raw41914step0Labels := by
      have hz : ∀ j, raw41914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41914step0 = (fun i j => raw41914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41914step0 raw41914; decide +kernel
      have hl : raw41914step0Labels = raw41914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41914 raw41914Labels permutation434 hz
    mixedMoment B raw41914step0 raw41914step0Labels = mixedMoment B raw41914step1 raw41914step1Labels := by
      have hz : ∀ j, raw41914step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41914step1 = (fun i j => raw41914step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41914step1 raw41914step0; decide +kernel
      have hl : raw41914step1Labels = raw41914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41914step0 raw41914step0Labels permutation80 hz
    mixedMoment B raw41914step1 raw41914step1Labels = mixedMoment B raw41914step2 raw41914step2Labels := by
      have ha : raw41914step2 = raw41914step1 := by apply Matrix.ext; unfold raw41914step2 raw41914step1; decide +kernel
      have hl : raw41914step1Labels = labelEmbedding1 ∘ raw41914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41914step1 raw41914step1Labels raw41914step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

theorem canonical41915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41915 raw41915Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw41915 raw41915Labels = mixedMoment B raw41915step0 raw41915step0Labels := by
      have hz : ∀ j, raw41915 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41915step0 = (fun i j => raw41915 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41915step0 raw41915; decide +kernel
      have hl : raw41915step0Labels = raw41915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41915 raw41915Labels permutation434 hz
    mixedMoment B raw41915step0 raw41915step0Labels = mixedMoment B raw41915step1 raw41915step1Labels := by
      have hz : ∀ j, raw41915step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41915step1 = (fun i j => raw41915step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41915step1 raw41915step0; decide +kernel
      have hl : raw41915step1Labels = raw41915step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41915step0 raw41915step0Labels permutation80 hz
    mixedMoment B raw41915step1 raw41915step1Labels = mixedMoment B raw41915step2 raw41915step2Labels := by
      have ha : raw41915step2 = (fun i j => raw41915step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41915step2 raw41915step1; decide +kernel
      have hl : raw41915step2Labels = raw41915step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41915step1 raw41915step1Labels permutation12 permutation7
    mixedMoment B raw41915step2 raw41915step2Labels = mixedMoment B raw41915step3 raw41915step3Labels := by
      have ha : raw41915step3 = -raw41915step2 := by apply Matrix.ext; change ∀ i j, raw41915step3 i j = -(raw41915step2 i j); unfold raw41915step3 raw41915step2; decide +kernel
      have hl : raw41915step3Labels = raw41915step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41915step3 raw41915step3Labels = mixedMoment B raw41915step4 raw41915step4Labels := by
      have ha : raw41915step4 = raw41915step3 := by apply Matrix.ext; unfold raw41915step4 raw41915step3; decide +kernel
      have hl : raw41915step3Labels = labelEmbedding6 ∘ raw41915step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41915step3 raw41915step3Labels raw41915step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4476 node4476Labels := by rfl

theorem canonical41916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41916 raw41916Labels = mixedMoment B node1722 node1722Labels := by
  calc
    mixedMoment B raw41916 raw41916Labels = mixedMoment B raw41916step0 raw41916step0Labels := by
      have hz : ∀ j, raw41916 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41916step0 = (fun i j => raw41916 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41916step0 raw41916; decide +kernel
      have hl : raw41916step0Labels = raw41916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41916 raw41916Labels permutation434 hz
    mixedMoment B raw41916step0 raw41916step0Labels = mixedMoment B raw41916step1 raw41916step1Labels := by
      have hz : ∀ j, raw41916step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41916step1 = (fun i j => raw41916step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41916step1 raw41916step0; decide +kernel
      have hl : raw41916step1Labels = raw41916step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41916step0 raw41916step0Labels permutation80 hz
    mixedMoment B raw41916step1 raw41916step1Labels = mixedMoment B raw41916step2 raw41916step2Labels := by
      have ha : raw41916step2 = raw41916step1 := by apply Matrix.ext; unfold raw41916step2 raw41916step1; decide +kernel
      have hl : raw41916step1Labels = labelEmbedding1 ∘ raw41916step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41916step1 raw41916step1Labels raw41916step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1722 node1722Labels := by rfl

theorem canonical41917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41917 raw41917Labels = mixedMoment B node4370 node4370Labels := by
  calc
    mixedMoment B raw41917 raw41917Labels = mixedMoment B raw41917step0 raw41917step0Labels := by
      have hz : ∀ j, raw41917 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41917step0 = (fun i j => raw41917 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41917step0 raw41917; decide +kernel
      have hl : raw41917step0Labels = raw41917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41917 raw41917Labels permutation434 hz
    mixedMoment B raw41917step0 raw41917step0Labels = mixedMoment B raw41917step1 raw41917step1Labels := by
      have hz : ∀ j, raw41917step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41917step1 = (fun i j => raw41917step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41917step1 raw41917step0; decide +kernel
      have hl : raw41917step1Labels = raw41917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41917step0 raw41917step0Labels permutation80 hz
    mixedMoment B raw41917step1 raw41917step1Labels = mixedMoment B raw41917step2 raw41917step2Labels := by
      have ha : raw41917step2 = (fun i j => raw41917step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41917step2 raw41917step1; decide +kernel
      have hl : raw41917step2Labels = raw41917step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41917step1 raw41917step1Labels permutation10 permutation7
    mixedMoment B raw41917step2 raw41917step2Labels = mixedMoment B raw41917step3 raw41917step3Labels := by
      have ha : raw41917step3 = -raw41917step2 := by apply Matrix.ext; change ∀ i j, raw41917step3 i j = -(raw41917step2 i j); unfold raw41917step3 raw41917step2; decide +kernel
      have hl : raw41917step3Labels = raw41917step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41917step3 raw41917step3Labels = mixedMoment B raw41917step4 raw41917step4Labels := by
      have ha : raw41917step4 = raw41917step3 := by apply Matrix.ext; unfold raw41917step4 raw41917step3; decide +kernel
      have hl : raw41917step3Labels = labelEmbedding6 ∘ raw41917step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41917step3 raw41917step3Labels raw41917step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4370 node4370Labels := by rfl

theorem canonical41918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41918 raw41918Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw41918 raw41918Labels = mixedMoment B raw41918step0 raw41918step0Labels := by
      have hz : ∀ j, raw41918 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41918step0 = (fun i j => raw41918 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41918step0 raw41918; decide +kernel
      have hl : raw41918step0Labels = raw41918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41918 raw41918Labels permutation346 hz
    mixedMoment B raw41918step0 raw41918step0Labels = mixedMoment B raw41918step1 raw41918step1Labels := by
      have ha : raw41918step1 = (fun i j => raw41918step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41918step1 raw41918step0; decide +kernel
      have hl : raw41918step1Labels = raw41918step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41918step0 raw41918step0Labels permutation38 permutation2
    mixedMoment B raw41918step1 raw41918step1Labels = mixedMoment B raw41918step2 raw41918step2Labels := by
      have ha : raw41918step2 = raw41918step1 := by apply Matrix.ext; unfold raw41918step2 raw41918step1; decide +kernel
      have hl : raw41918step1Labels = labelEmbedding1 ∘ raw41918step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41918step1 raw41918step1Labels raw41918step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

theorem canonical41919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41919 raw41919Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw41919 raw41919Labels = mixedMoment B raw41919step0 raw41919step0Labels := by
      have hz : ∀ j, raw41919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41919step0 = (fun i j => raw41919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41919step0 raw41919; decide +kernel
      have hl : raw41919step0Labels = raw41919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41919 raw41919Labels permutation346 hz
    mixedMoment B raw41919step0 raw41919step0Labels = mixedMoment B raw41919step1 raw41919step1Labels := by
      have ha : raw41919step1 = (fun i j => raw41919step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41919step1 raw41919step0; decide +kernel
      have hl : raw41919step1Labels = raw41919step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41919step0 raw41919step0Labels permutation40 permutation7
    mixedMoment B raw41919step1 raw41919step1Labels = mixedMoment B raw41919step2 raw41919step2Labels := by
      have ha : raw41919step2 = -raw41919step1 := by apply Matrix.ext; change ∀ i j, raw41919step2 i j = -(raw41919step1 i j); unfold raw41919step2 raw41919step1; decide +kernel
      have hl : raw41919step2Labels = raw41919step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41919step2 raw41919step2Labels = mixedMoment B raw41919step3 raw41919step3Labels := by
      have ha : raw41919step3 = raw41919step2 := by apply Matrix.ext; unfold raw41919step3 raw41919step2; decide +kernel
      have hl : raw41919step2Labels = labelEmbedding6 ∘ raw41919step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41919step2 raw41919step2Labels raw41919step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4330 node4330Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2272) =
      Integer.Sparse.eval keyMomentRow2272 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2272).leftCharge (GramAssembly.key 2272).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2223) := by
    have ha : gramCharges (GramAssembly.key 2272).leftCharge (GramAssembly.key 2272).rightCharge = raw41856 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41856Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41856 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2272).leftCharge (GramAssembly.key 2272).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4777) := by
    have ha : gramCharges (GramAssembly.key 2272).leftCharge (GramAssembly.key 2272).rightCharge = raw41857 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41857Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41857 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2272).leftCharge (GramAssembly.key 2272).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2272).leftCharge (GramAssembly.key 2272).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2272, Integer.Sparse.eval]
  ring

theorem keyMoment2273 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2273) =
      Integer.Sparse.eval keyMomentRow2273 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2273).leftCharge (GramAssembly.key 2273).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1685) := by
    have ha : gramCharges (GramAssembly.key 2273).leftCharge (GramAssembly.key 2273).rightCharge = raw41858 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41858Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41858 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2273).leftCharge (GramAssembly.key 2273).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4336) := by
    have ha : gramCharges (GramAssembly.key 2273).leftCharge (GramAssembly.key 2273).rightCharge = raw41859 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41859Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41859 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2273).leftCharge (GramAssembly.key 2273).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2273).leftCharge (GramAssembly.key 2273).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2273, Integer.Sparse.eval]
  ring

theorem keyMoment2274 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2274) =
      Integer.Sparse.eval keyMomentRow2274 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2274).leftCharge (GramAssembly.key 2274).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2164) := by
    have ha : gramCharges (GramAssembly.key 2274).leftCharge (GramAssembly.key 2274).rightCharge = raw41860 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41860Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41860 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2274).leftCharge (GramAssembly.key 2274).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4670) := by
    have ha : gramCharges (GramAssembly.key 2274).leftCharge (GramAssembly.key 2274).rightCharge = raw41861 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41861Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41861 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2274).leftCharge (GramAssembly.key 2274).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2274).leftCharge (GramAssembly.key 2274).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2274, Integer.Sparse.eval]
  ring

theorem keyMoment2275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2275) =
      Integer.Sparse.eval keyMomentRow2275 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2275).leftCharge (GramAssembly.key 2275).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1684) := by
    have ha : gramCharges (GramAssembly.key 2275).leftCharge (GramAssembly.key 2275).rightCharge = raw41862 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41862Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41862 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2275).leftCharge (GramAssembly.key 2275).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4331) := by
    have ha : gramCharges (GramAssembly.key 2275).leftCharge (GramAssembly.key 2275).rightCharge = raw41863 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41863Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41863 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2275).leftCharge (GramAssembly.key 2275).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2275).leftCharge (GramAssembly.key 2275).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2275, Integer.Sparse.eval]
  ring

theorem keyMoment2276 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2276) =
      Integer.Sparse.eval keyMomentRow2276 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2276).leftCharge (GramAssembly.key 2276).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2181) := by
    have ha : gramCharges (GramAssembly.key 2276).leftCharge (GramAssembly.key 2276).rightCharge = raw41864 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41864Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41864 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2276).leftCharge (GramAssembly.key 2276).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4757) := by
    have ha : gramCharges (GramAssembly.key 2276).leftCharge (GramAssembly.key 2276).rightCharge = raw41865 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41865Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41865 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2276).leftCharge (GramAssembly.key 2276).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2276).leftCharge (GramAssembly.key 2276).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2276, Integer.Sparse.eval]
  ring

theorem keyMoment2277 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2277) =
      Integer.Sparse.eval keyMomentRow2277 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2277).leftCharge (GramAssembly.key 2277).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1746) := by
    have ha : gramCharges (GramAssembly.key 2277).leftCharge (GramAssembly.key 2277).rightCharge = raw41866 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41866Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41866 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2277).leftCharge (GramAssembly.key 2277).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4478) := by
    have ha : gramCharges (GramAssembly.key 2277).leftCharge (GramAssembly.key 2277).rightCharge = raw41867 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41867Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41867 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2277).leftCharge (GramAssembly.key 2277).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2277).leftCharge (GramAssembly.key 2277).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2277, Integer.Sparse.eval]
  ring

theorem keyMoment2278 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2278) =
      Integer.Sparse.eval keyMomentRow2278 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2278).leftCharge (GramAssembly.key 2278).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1745) := by
    have ha : gramCharges (GramAssembly.key 2278).leftCharge (GramAssembly.key 2278).rightCharge = raw41868 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41868Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41868 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2278).leftCharge (GramAssembly.key 2278).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4464) := by
    have ha : gramCharges (GramAssembly.key 2278).leftCharge (GramAssembly.key 2278).rightCharge = raw41869 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41869Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41869 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2278).leftCharge (GramAssembly.key 2278).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2278).leftCharge (GramAssembly.key 2278).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2278, Integer.Sparse.eval]
  ring

theorem keyMoment2279 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2279) =
      Integer.Sparse.eval keyMomentRow2279 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2279).leftCharge (GramAssembly.key 2279).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1743) := by
    have ha : gramCharges (GramAssembly.key 2279).leftCharge (GramAssembly.key 2279).rightCharge = raw41870 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41870Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41870 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2279).leftCharge (GramAssembly.key 2279).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4375) := by
    have ha : gramCharges (GramAssembly.key 2279).leftCharge (GramAssembly.key 2279).rightCharge = raw41871 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41871Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41871 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2279).leftCharge (GramAssembly.key 2279).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2279).leftCharge (GramAssembly.key 2279).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2279, Integer.Sparse.eval]
  ring

theorem keyMoment2280 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2280) =
      Integer.Sparse.eval keyMomentRow2280 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2280).leftCharge (GramAssembly.key 2280).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1685) := by
    have ha : gramCharges (GramAssembly.key 2280).leftCharge (GramAssembly.key 2280).rightCharge = raw41872 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41872Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41872 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2280).leftCharge (GramAssembly.key 2280).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4336) := by
    have ha : gramCharges (GramAssembly.key 2280).leftCharge (GramAssembly.key 2280).rightCharge = raw41873 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41873Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41873 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2280).leftCharge (GramAssembly.key 2280).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2280).leftCharge (GramAssembly.key 2280).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2280, Integer.Sparse.eval]
  ring

theorem keyMoment2281 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2281) =
      Integer.Sparse.eval keyMomentRow2281 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2281).leftCharge (GramAssembly.key 2281).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1742) := by
    have ha : gramCharges (GramAssembly.key 2281).leftCharge (GramAssembly.key 2281).rightCharge = raw41874 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41874Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41874 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2281).leftCharge (GramAssembly.key 2281).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4371) := by
    have ha : gramCharges (GramAssembly.key 2281).leftCharge (GramAssembly.key 2281).rightCharge = raw41875 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41875Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41875 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2281).leftCharge (GramAssembly.key 2281).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2281).leftCharge (GramAssembly.key 2281).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2281, Integer.Sparse.eval]
  ring

theorem keyMoment2282 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2282) =
      Integer.Sparse.eval keyMomentRow2282 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2282).leftCharge (GramAssembly.key 2282).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1744) := by
    have ha : gramCharges (GramAssembly.key 2282).leftCharge (GramAssembly.key 2282).rightCharge = raw41876 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41876Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41876 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2282).leftCharge (GramAssembly.key 2282).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4442) := by
    have ha : gramCharges (GramAssembly.key 2282).leftCharge (GramAssembly.key 2282).rightCharge = raw41877 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41877Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41877 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2282).leftCharge (GramAssembly.key 2282).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2282).leftCharge (GramAssembly.key 2282).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2282, Integer.Sparse.eval]
  ring

theorem keyMoment2283 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2283) =
      Integer.Sparse.eval keyMomentRow2283 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2283).leftCharge (GramAssembly.key 2283).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1684) := by
    have ha : gramCharges (GramAssembly.key 2283).leftCharge (GramAssembly.key 2283).rightCharge = raw41878 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41878Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41878 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2283).leftCharge (GramAssembly.key 2283).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4331) := by
    have ha : gramCharges (GramAssembly.key 2283).leftCharge (GramAssembly.key 2283).rightCharge = raw41879 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41879Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41879 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2283).leftCharge (GramAssembly.key 2283).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2283).leftCharge (GramAssembly.key 2283).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2283, Integer.Sparse.eval]
  ring

theorem keyMoment2284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2284) =
      Integer.Sparse.eval keyMomentRow2284 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2284).leftCharge (GramAssembly.key 2284).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1715) := by
    have ha : gramCharges (GramAssembly.key 2284).leftCharge (GramAssembly.key 2284).rightCharge = raw41880 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41880Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41880 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2284).leftCharge (GramAssembly.key 2284).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4475) := by
    have ha : gramCharges (GramAssembly.key 2284).leftCharge (GramAssembly.key 2284).rightCharge = raw41881 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41881Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41881 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2284).leftCharge (GramAssembly.key 2284).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2284).leftCharge (GramAssembly.key 2284).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2284, Integer.Sparse.eval]
  ring

theorem keyMoment2285 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2285) =
      Integer.Sparse.eval keyMomentRow2285 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2285).leftCharge (GramAssembly.key 2285).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1714) := by
    have ha : gramCharges (GramAssembly.key 2285).leftCharge (GramAssembly.key 2285).rightCharge = raw41882 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41882Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41882 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2285).leftCharge (GramAssembly.key 2285).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4459) := by
    have ha : gramCharges (GramAssembly.key 2285).leftCharge (GramAssembly.key 2285).rightCharge = raw41883 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41883Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41883 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2285).leftCharge (GramAssembly.key 2285).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2285).leftCharge (GramAssembly.key 2285).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2285, Integer.Sparse.eval]
  ring

theorem keyMoment2286 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2286) =
      Integer.Sparse.eval keyMomentRow2286 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2286).leftCharge (GramAssembly.key 2286).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1712) := by
    have ha : gramCharges (GramAssembly.key 2286).leftCharge (GramAssembly.key 2286).rightCharge = raw41884 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41884Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41884 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2286).leftCharge (GramAssembly.key 2286).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4368) := by
    have ha : gramCharges (GramAssembly.key 2286).leftCharge (GramAssembly.key 2286).rightCharge = raw41885 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41885Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41885 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2286).leftCharge (GramAssembly.key 2286).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2286).leftCharge (GramAssembly.key 2286).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2286, Integer.Sparse.eval]
  ring

theorem keyMoment2287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2287) =
      Integer.Sparse.eval keyMomentRow2287 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2287).leftCharge (GramAssembly.key 2287).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1667) := by
    have ha : gramCharges (GramAssembly.key 2287).leftCharge (GramAssembly.key 2287).rightCharge = raw41886 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41886Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41886 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2287).leftCharge (GramAssembly.key 2287).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4328) := by
    have ha : gramCharges (GramAssembly.key 2287).leftCharge (GramAssembly.key 2287).rightCharge = raw41887 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41887Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41887 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2287).leftCharge (GramAssembly.key 2287).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2287).leftCharge (GramAssembly.key 2287).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2287, Integer.Sparse.eval]
  ring

theorem keyMoment2288 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2288) =
      Integer.Sparse.eval keyMomentRow2288 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2288).leftCharge (GramAssembly.key 2288).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1711) := by
    have ha : gramCharges (GramAssembly.key 2288).leftCharge (GramAssembly.key 2288).rightCharge = raw41888 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41888Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41888 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2288).leftCharge (GramAssembly.key 2288).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4366) := by
    have ha : gramCharges (GramAssembly.key 2288).leftCharge (GramAssembly.key 2288).rightCharge = raw41889 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41889Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41889 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2288).leftCharge (GramAssembly.key 2288).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2288).leftCharge (GramAssembly.key 2288).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2288, Integer.Sparse.eval]
  ring

theorem keyMoment2289 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2289) =
      Integer.Sparse.eval keyMomentRow2289 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2289).leftCharge (GramAssembly.key 2289).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1713) := by
    have ha : gramCharges (GramAssembly.key 2289).leftCharge (GramAssembly.key 2289).rightCharge = raw41890 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41890Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41890 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2289).leftCharge (GramAssembly.key 2289).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4439) := by
    have ha : gramCharges (GramAssembly.key 2289).leftCharge (GramAssembly.key 2289).rightCharge = raw41891 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41891Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41891 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2289).leftCharge (GramAssembly.key 2289).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2289).leftCharge (GramAssembly.key 2289).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2289, Integer.Sparse.eval]
  ring

theorem keyMoment2290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2290) =
      Integer.Sparse.eval keyMomentRow2290 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2290).leftCharge (GramAssembly.key 2290).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1740) := by
    have ha : gramCharges (GramAssembly.key 2290).leftCharge (GramAssembly.key 2290).rightCharge = raw41892 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41892Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41892 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2290).leftCharge (GramAssembly.key 2290).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4480) := by
    have ha : gramCharges (GramAssembly.key 2290).leftCharge (GramAssembly.key 2290).rightCharge = raw41893 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41893Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41893 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2290).leftCharge (GramAssembly.key 2290).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2290).leftCharge (GramAssembly.key 2290).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2290, Integer.Sparse.eval]
  ring

theorem keyMoment2291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2291) =
      Integer.Sparse.eval keyMomentRow2291 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2291).leftCharge (GramAssembly.key 2291).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1735) := by
    have ha : gramCharges (GramAssembly.key 2291).leftCharge (GramAssembly.key 2291).rightCharge = raw41894 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41894Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41894 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2291).leftCharge (GramAssembly.key 2291).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4373) := by
    have ha : gramCharges (GramAssembly.key 2291).leftCharge (GramAssembly.key 2291).rightCharge = raw41895 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41895Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41895 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2291).leftCharge (GramAssembly.key 2291).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2291).leftCharge (GramAssembly.key 2291).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2291, Integer.Sparse.eval]
  ring

theorem keyMoment2292 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2292) =
      Integer.Sparse.eval keyMomentRow2292 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2292).leftCharge (GramAssembly.key 2292).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1679) := by
    have ha : gramCharges (GramAssembly.key 2292).leftCharge (GramAssembly.key 2292).rightCharge = raw41896 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41896Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41896 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2292).leftCharge (GramAssembly.key 2292).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4334) := by
    have ha : gramCharges (GramAssembly.key 2292).leftCharge (GramAssembly.key 2292).rightCharge = raw41897 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41897Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41897 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2292).leftCharge (GramAssembly.key 2292).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2292).leftCharge (GramAssembly.key 2292).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2292, Integer.Sparse.eval]
  ring

theorem keyMoment2293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2293) =
      Integer.Sparse.eval keyMomentRow2293 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2293).leftCharge (GramAssembly.key 2293).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1734) := by
    have ha : gramCharges (GramAssembly.key 2293).leftCharge (GramAssembly.key 2293).rightCharge = raw41898 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41898Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41898 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2293).leftCharge (GramAssembly.key 2293).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4372) := by
    have ha : gramCharges (GramAssembly.key 2293).leftCharge (GramAssembly.key 2293).rightCharge = raw41899 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41899Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41899 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2293).leftCharge (GramAssembly.key 2293).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2293).leftCharge (GramAssembly.key 2293).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2293, Integer.Sparse.eval]
  ring

theorem keyMoment2294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2294) =
      Integer.Sparse.eval keyMomentRow2294 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2294).leftCharge (GramAssembly.key 2294).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1736) := by
    have ha : gramCharges (GramAssembly.key 2294).leftCharge (GramAssembly.key 2294).rightCharge = raw41900 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41900Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41900 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2294).leftCharge (GramAssembly.key 2294).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4444) := by
    have ha : gramCharges (GramAssembly.key 2294).leftCharge (GramAssembly.key 2294).rightCharge = raw41901 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41901Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41901 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2294).leftCharge (GramAssembly.key 2294).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2294).leftCharge (GramAssembly.key 2294).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2294, Integer.Sparse.eval]
  ring

theorem keyMoment2295 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2295) =
      Integer.Sparse.eval keyMomentRow2295 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2295).leftCharge (GramAssembly.key 2295).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1678) := by
    have ha : gramCharges (GramAssembly.key 2295).leftCharge (GramAssembly.key 2295).rightCharge = raw41902 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41902Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41902 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2295).leftCharge (GramAssembly.key 2295).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4332) := by
    have ha : gramCharges (GramAssembly.key 2295).leftCharge (GramAssembly.key 2295).rightCharge = raw41903 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41903Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41903 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2295).leftCharge (GramAssembly.key 2295).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2295).leftCharge (GramAssembly.key 2295).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2295, Integer.Sparse.eval]
  ring

theorem keyMoment2296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2296) =
      Integer.Sparse.eval keyMomentRow2296 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2296).leftCharge (GramAssembly.key 2296).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1699) := by
    have ha : gramCharges (GramAssembly.key 2296).leftCharge (GramAssembly.key 2296).rightCharge = raw41904 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41904Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41904 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2296).leftCharge (GramAssembly.key 2296).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4473) := by
    have ha : gramCharges (GramAssembly.key 2296).leftCharge (GramAssembly.key 2296).rightCharge = raw41905 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41905Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41905 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2296).leftCharge (GramAssembly.key 2296).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2296).leftCharge (GramAssembly.key 2296).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2296, Integer.Sparse.eval]
  ring

theorem keyMoment2297 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2297) =
      Integer.Sparse.eval keyMomentRow2297 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2297).leftCharge (GramAssembly.key 2297).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1697) := by
    have ha : gramCharges (GramAssembly.key 2297).leftCharge (GramAssembly.key 2297).rightCharge = raw41906 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41906Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41906 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2297).leftCharge (GramAssembly.key 2297).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4363) := by
    have ha : gramCharges (GramAssembly.key 2297).leftCharge (GramAssembly.key 2297).rightCharge = raw41907 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41907Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41907 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2297).leftCharge (GramAssembly.key 2297).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2297).leftCharge (GramAssembly.key 2297).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2297, Integer.Sparse.eval]
  ring

theorem keyMoment2298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2298) =
      Integer.Sparse.eval keyMomentRow2298 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2298).leftCharge (GramAssembly.key 2298).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1709) := by
    have ha : gramCharges (GramAssembly.key 2298).leftCharge (GramAssembly.key 2298).rightCharge = raw41908 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41908Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41908 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2298).leftCharge (GramAssembly.key 2298).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4474) := by
    have ha : gramCharges (GramAssembly.key 2298).leftCharge (GramAssembly.key 2298).rightCharge = raw41909 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41909Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41909 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2298).leftCharge (GramAssembly.key 2298).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2298).leftCharge (GramAssembly.key 2298).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2298, Integer.Sparse.eval]
  ring

theorem keyMoment2299 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2299) =
      Integer.Sparse.eval keyMomentRow2299 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2299).leftCharge (GramAssembly.key 2299).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1704) := by
    have ha : gramCharges (GramAssembly.key 2299).leftCharge (GramAssembly.key 2299).rightCharge = raw41910 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41910Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41910 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2299).leftCharge (GramAssembly.key 2299).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4365) := by
    have ha : gramCharges (GramAssembly.key 2299).leftCharge (GramAssembly.key 2299).rightCharge = raw41911 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41911Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41911 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2299).leftCharge (GramAssembly.key 2299).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2299).leftCharge (GramAssembly.key 2299).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2299, Integer.Sparse.eval]
  ring

theorem keyMoment2300 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2300) =
      Integer.Sparse.eval keyMomentRow2300 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2300).leftCharge (GramAssembly.key 2300).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1703) := by
    have ha : gramCharges (GramAssembly.key 2300).leftCharge (GramAssembly.key 2300).rightCharge = raw41912 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41912Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41912 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2300).leftCharge (GramAssembly.key 2300).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4364) := by
    have ha : gramCharges (GramAssembly.key 2300).leftCharge (GramAssembly.key 2300).rightCharge = raw41913 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41913Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41913 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2300).leftCharge (GramAssembly.key 2300).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2300).leftCharge (GramAssembly.key 2300).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2300, Integer.Sparse.eval]
  ring

theorem keyMoment2301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2301) =
      Integer.Sparse.eval keyMomentRow2301 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2301).leftCharge (GramAssembly.key 2301).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1729) := by
    have ha : gramCharges (GramAssembly.key 2301).leftCharge (GramAssembly.key 2301).rightCharge = raw41914 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41914Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41914 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2301).leftCharge (GramAssembly.key 2301).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4476) := by
    have ha : gramCharges (GramAssembly.key 2301).leftCharge (GramAssembly.key 2301).rightCharge = raw41915 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41915Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41915 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2301).leftCharge (GramAssembly.key 2301).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2301).leftCharge (GramAssembly.key 2301).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2301, Integer.Sparse.eval]
  ring

theorem keyMoment2302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2302) =
      Integer.Sparse.eval keyMomentRow2302 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2302).leftCharge (GramAssembly.key 2302).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1722) := by
    have ha : gramCharges (GramAssembly.key 2302).leftCharge (GramAssembly.key 2302).rightCharge = raw41916 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41916Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41916 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2302).leftCharge (GramAssembly.key 2302).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4370) := by
    have ha : gramCharges (GramAssembly.key 2302).leftCharge (GramAssembly.key 2302).rightCharge = raw41917 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41917Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41917 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2302).leftCharge (GramAssembly.key 2302).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2302).leftCharge (GramAssembly.key 2302).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2302, Integer.Sparse.eval]
  ring

theorem keyMoment2303 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2303) =
      Integer.Sparse.eval keyMomentRow2303 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2303).leftCharge (GramAssembly.key 2303).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1672) := by
    have ha : gramCharges (GramAssembly.key 2303).leftCharge (GramAssembly.key 2303).rightCharge = raw41918 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41918Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41918 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2303).leftCharge (GramAssembly.key 2303).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4330) := by
    have ha : gramCharges (GramAssembly.key 2303).leftCharge (GramAssembly.key 2303).rightCharge = raw41919 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41919Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41919 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2303).leftCharge (GramAssembly.key 2303).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2303).leftCharge (GramAssembly.key 2303).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2303, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2272 : keyMomentRows (2272 : Fin 2886) =
    keyMomentRow2272 := by decide +kernel

theorem keyMomentRowsAt2273 : keyMomentRows (2273 : Fin 2886) =
    keyMomentRow2273 := by decide +kernel

theorem keyMomentRowsAt2274 : keyMomentRows (2274 : Fin 2886) =
    keyMomentRow2274 := by decide +kernel

theorem keyMomentRowsAt2275 : keyMomentRows (2275 : Fin 2886) =
    keyMomentRow2275 := by decide +kernel

theorem keyMomentRowsAt2276 : keyMomentRows (2276 : Fin 2886) =
    keyMomentRow2276 := by decide +kernel

theorem keyMomentRowsAt2277 : keyMomentRows (2277 : Fin 2886) =
    keyMomentRow2277 := by decide +kernel

theorem keyMomentRowsAt2278 : keyMomentRows (2278 : Fin 2886) =
    keyMomentRow2278 := by decide +kernel

theorem keyMomentRowsAt2279 : keyMomentRows (2279 : Fin 2886) =
    keyMomentRow2279 := by decide +kernel

theorem keyMomentRowsAt2280 : keyMomentRows (2280 : Fin 2886) =
    keyMomentRow2280 := by decide +kernel

theorem keyMomentRowsAt2281 : keyMomentRows (2281 : Fin 2886) =
    keyMomentRow2281 := by decide +kernel

theorem keyMomentRowsAt2282 : keyMomentRows (2282 : Fin 2886) =
    keyMomentRow2282 := by decide +kernel

theorem keyMomentRowsAt2283 : keyMomentRows (2283 : Fin 2886) =
    keyMomentRow2283 := by decide +kernel

theorem keyMomentRowsAt2284 : keyMomentRows (2284 : Fin 2886) =
    keyMomentRow2284 := by decide +kernel

theorem keyMomentRowsAt2285 : keyMomentRows (2285 : Fin 2886) =
    keyMomentRow2285 := by decide +kernel

theorem keyMomentRowsAt2286 : keyMomentRows (2286 : Fin 2886) =
    keyMomentRow2286 := by decide +kernel

theorem keyMomentRowsAt2287 : keyMomentRows (2287 : Fin 2886) =
    keyMomentRow2287 := by decide +kernel

theorem keyMomentRowsAt2288 : keyMomentRows (2288 : Fin 2886) =
    keyMomentRow2288 := by decide +kernel

theorem keyMomentRowsAt2289 : keyMomentRows (2289 : Fin 2886) =
    keyMomentRow2289 := by decide +kernel

theorem keyMomentRowsAt2290 : keyMomentRows (2290 : Fin 2886) =
    keyMomentRow2290 := by decide +kernel

theorem keyMomentRowsAt2291 : keyMomentRows (2291 : Fin 2886) =
    keyMomentRow2291 := by decide +kernel

theorem keyMomentRowsAt2292 : keyMomentRows (2292 : Fin 2886) =
    keyMomentRow2292 := by decide +kernel

theorem keyMomentRowsAt2293 : keyMomentRows (2293 : Fin 2886) =
    keyMomentRow2293 := by decide +kernel

theorem keyMomentRowsAt2294 : keyMomentRows (2294 : Fin 2886) =
    keyMomentRow2294 := by decide +kernel

theorem keyMomentRowsAt2295 : keyMomentRows (2295 : Fin 2886) =
    keyMomentRow2295 := by decide +kernel

theorem keyMomentRowsAt2296 : keyMomentRows (2296 : Fin 2886) =
    keyMomentRow2296 := by decide +kernel

theorem keyMomentRowsAt2297 : keyMomentRows (2297 : Fin 2886) =
    keyMomentRow2297 := by decide +kernel

theorem keyMomentRowsAt2298 : keyMomentRows (2298 : Fin 2886) =
    keyMomentRow2298 := by decide +kernel

theorem keyMomentRowsAt2299 : keyMomentRows (2299 : Fin 2886) =
    keyMomentRow2299 := by decide +kernel

theorem keyMomentRowsAt2300 : keyMomentRows (2300 : Fin 2886) =
    keyMomentRow2300 := by decide +kernel

theorem keyMomentRowsAt2301 : keyMomentRows (2301 : Fin 2886) =
    keyMomentRow2301 := by decide +kernel

theorem keyMomentRowsAt2302 : keyMomentRows (2302 : Fin 2886) =
    keyMomentRow2302 := by decide +kernel

theorem keyMomentRowsAt2303 : keyMomentRows (2303 : Fin 2886) =
    keyMomentRow2303 := by decide +kernel

theorem keyMomentChunkSound71_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 71) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2272 ∨ k.val = 2273 ∨ k.val = 2274 ∨ k.val = 2275 ∨ k.val = 2276 ∨ k.val = 2277 ∨ k.val = 2278 ∨ k.val = 2279 ∨ k.val = 2280 ∨ k.val = 2281 ∨ k.val = 2282 ∨ k.val = 2283 ∨ k.val = 2284 ∨ k.val = 2285 ∨ k.val = 2286 ∨ k.val = 2287 ∨ k.val = 2288 ∨ k.val = 2289 ∨ k.val = 2290 ∨ k.val = 2291 ∨ k.val = 2292 ∨ k.val = 2293 ∨ k.val = 2294 ∨ k.val = 2295 ∨ k.val = 2296 ∨ k.val = 2297 ∨ k.val = 2298 ∨ k.val = 2299 ∨ k.val = 2300 ∨ k.val = 2301 ∨ k.val = 2302 ∨ k.val = 2303 := by omega
  rcases heq with h2272 | h2273 | h2274 | h2275 | h2276 | h2277 | h2278 | h2279 | h2280 | h2281 | h2282 | h2283 | h2284 | h2285 | h2286 | h2287 | h2288 | h2289 | h2290 | h2291 | h2292 | h2293 | h2294 | h2295 | h2296 | h2297 | h2298 | h2299 | h2300 | h2301 | h2302 | h2303
  · have he : k = (2272 : Fin 2886) := Fin.ext h2272
    subst k
    rw [keyMomentRowsAt2272]
    exact keyMoment2272 B hB
  · have he : k = (2273 : Fin 2886) := Fin.ext h2273
    subst k
    rw [keyMomentRowsAt2273]
    exact keyMoment2273 B hB
  · have he : k = (2274 : Fin 2886) := Fin.ext h2274
    subst k
    rw [keyMomentRowsAt2274]
    exact keyMoment2274 B hB
  · have he : k = (2275 : Fin 2886) := Fin.ext h2275
    subst k
    rw [keyMomentRowsAt2275]
    exact keyMoment2275 B hB
  · have he : k = (2276 : Fin 2886) := Fin.ext h2276
    subst k
    rw [keyMomentRowsAt2276]
    exact keyMoment2276 B hB
  · have he : k = (2277 : Fin 2886) := Fin.ext h2277
    subst k
    rw [keyMomentRowsAt2277]
    exact keyMoment2277 B hB
  · have he : k = (2278 : Fin 2886) := Fin.ext h2278
    subst k
    rw [keyMomentRowsAt2278]
    exact keyMoment2278 B hB
  · have he : k = (2279 : Fin 2886) := Fin.ext h2279
    subst k
    rw [keyMomentRowsAt2279]
    exact keyMoment2279 B hB
  · have he : k = (2280 : Fin 2886) := Fin.ext h2280
    subst k
    rw [keyMomentRowsAt2280]
    exact keyMoment2280 B hB
  · have he : k = (2281 : Fin 2886) := Fin.ext h2281
    subst k
    rw [keyMomentRowsAt2281]
    exact keyMoment2281 B hB
  · have he : k = (2282 : Fin 2886) := Fin.ext h2282
    subst k
    rw [keyMomentRowsAt2282]
    exact keyMoment2282 B hB
  · have he : k = (2283 : Fin 2886) := Fin.ext h2283
    subst k
    rw [keyMomentRowsAt2283]
    exact keyMoment2283 B hB
  · have he : k = (2284 : Fin 2886) := Fin.ext h2284
    subst k
    rw [keyMomentRowsAt2284]
    exact keyMoment2284 B hB
  · have he : k = (2285 : Fin 2886) := Fin.ext h2285
    subst k
    rw [keyMomentRowsAt2285]
    exact keyMoment2285 B hB
  · have he : k = (2286 : Fin 2886) := Fin.ext h2286
    subst k
    rw [keyMomentRowsAt2286]
    exact keyMoment2286 B hB
  · have he : k = (2287 : Fin 2886) := Fin.ext h2287
    subst k
    rw [keyMomentRowsAt2287]
    exact keyMoment2287 B hB
  · have he : k = (2288 : Fin 2886) := Fin.ext h2288
    subst k
    rw [keyMomentRowsAt2288]
    exact keyMoment2288 B hB
  · have he : k = (2289 : Fin 2886) := Fin.ext h2289
    subst k
    rw [keyMomentRowsAt2289]
    exact keyMoment2289 B hB
  · have he : k = (2290 : Fin 2886) := Fin.ext h2290
    subst k
    rw [keyMomentRowsAt2290]
    exact keyMoment2290 B hB
  · have he : k = (2291 : Fin 2886) := Fin.ext h2291
    subst k
    rw [keyMomentRowsAt2291]
    exact keyMoment2291 B hB
  · have he : k = (2292 : Fin 2886) := Fin.ext h2292
    subst k
    rw [keyMomentRowsAt2292]
    exact keyMoment2292 B hB
  · have he : k = (2293 : Fin 2886) := Fin.ext h2293
    subst k
    rw [keyMomentRowsAt2293]
    exact keyMoment2293 B hB
  · have he : k = (2294 : Fin 2886) := Fin.ext h2294
    subst k
    rw [keyMomentRowsAt2294]
    exact keyMoment2294 B hB
  · have he : k = (2295 : Fin 2886) := Fin.ext h2295
    subst k
    rw [keyMomentRowsAt2295]
    exact keyMoment2295 B hB
  · have he : k = (2296 : Fin 2886) := Fin.ext h2296
    subst k
    rw [keyMomentRowsAt2296]
    exact keyMoment2296 B hB
  · have he : k = (2297 : Fin 2886) := Fin.ext h2297
    subst k
    rw [keyMomentRowsAt2297]
    exact keyMoment2297 B hB
  · have he : k = (2298 : Fin 2886) := Fin.ext h2298
    subst k
    rw [keyMomentRowsAt2298]
    exact keyMoment2298 B hB
  · have he : k = (2299 : Fin 2886) := Fin.ext h2299
    subst k
    rw [keyMomentRowsAt2299]
    exact keyMoment2299 B hB
  · have he : k = (2300 : Fin 2886) := Fin.ext h2300
    subst k
    rw [keyMomentRowsAt2300]
    exact keyMoment2300 B hB
  · have he : k = (2301 : Fin 2886) := Fin.ext h2301
    subst k
    rw [keyMomentRowsAt2301]
    exact keyMoment2301 B hB
  · have he : k = (2302 : Fin 2886) := Fin.ext h2302
    subst k
    rw [keyMomentRowsAt2302]
    exact keyMoment2302 B hB
  · have he : k = (2303 : Fin 2886) := Fin.ext h2303
    subst k
    rw [keyMomentRowsAt2303]
    exact keyMoment2303 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound71_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound71_e_oai
