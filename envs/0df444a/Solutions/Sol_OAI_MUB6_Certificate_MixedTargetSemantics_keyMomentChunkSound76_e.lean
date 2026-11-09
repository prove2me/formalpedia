-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound76_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:05:30.940968+00:00
-- url     : https://prove2.me/submissions/bb4b18f7-5f6b-48a7-a58f-845c37ec0973

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical329
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical42176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42176 raw42176Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw42176 raw42176Labels = mixedMoment B raw42176step0 raw42176step0Labels := by
      have ha : raw42176step0 = (fun i j => raw42176 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42176step0 raw42176; decide +kernel
      have hl : raw42176step0Labels = raw42176Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42176 raw42176Labels permutation682 permutation2
    mixedMoment B raw42176step0 raw42176step0Labels = mixedMoment B raw42176step1 raw42176step1Labels := by
      have ha : raw42176step1 = -raw42176step0 := by apply Matrix.ext; change ∀ i j, raw42176step1 i j = -(raw42176step0 i j); unfold raw42176step1 raw42176step0; decide +kernel
      have hl : raw42176step1Labels = raw42176step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42176step1 raw42176step1Labels = mixedMoment B raw42176step2 raw42176step2Labels := by
      have ha : raw42176step2 = raw42176step1 := by apply Matrix.ext; unfold raw42176step2 raw42176step1; decide +kernel
      have hl : raw42176step1Labels = labelEmbedding1 ∘ raw42176step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42176step1 raw42176step1Labels raw42176step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical42177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42177 raw42177Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42177 raw42177Labels = mixedMoment B raw42177step0 raw42177step0Labels := by
      have ha : raw42177step0 = (fun i j => raw42177 (permutation643 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42177step0 raw42177; decide +kernel
      have hl : raw42177step0Labels = raw42177Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42177 raw42177Labels permutation643 permutation7
    mixedMoment B raw42177step0 raw42177step0Labels = mixedMoment B raw42177step1 raw42177step1Labels := by
      have ha : raw42177step1 = raw42177step0 := by apply Matrix.ext; unfold raw42177step1 raw42177step0; decide +kernel
      have hl : raw42177step0Labels = labelEmbedding6 ∘ raw42177step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42177step0 raw42177step0Labels raw42177step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical42178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42178 raw42178Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw42178 raw42178Labels = mixedMoment B raw42178step0 raw42178step0Labels := by
      have ha : raw42178step0 = (fun i j => raw42178 (permutation659 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42178step0 raw42178; decide +kernel
      have hl : raw42178step0Labels = raw42178Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42178 raw42178Labels permutation659 permutation4
    mixedMoment B raw42178step0 raw42178step0Labels = mixedMoment B raw42178step1 raw42178step1Labels := by
      have ha : raw42178step1 = raw42178step0 := by apply Matrix.ext; unfold raw42178step1 raw42178step0; decide +kernel
      have hl : raw42178step0Labels = labelEmbedding1 ∘ raw42178step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42178step0 raw42178step0Labels raw42178step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2750 node2750Labels := by rfl

theorem canonical42179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42179 raw42179Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw42179 raw42179Labels = mixedMoment B raw42179step0 raw42179step0Labels := by
      have ha : raw42179step0 = (fun i j => raw42179 (permutation659 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42179step0 raw42179; decide +kernel
      have hl : raw42179step0Labels = raw42179Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42179 raw42179Labels permutation659 permutation4
    mixedMoment B raw42179step0 raw42179step0Labels = mixedMoment B raw42179step1 raw42179step1Labels := by
      have ha : raw42179step1 = raw42179step0 := by apply Matrix.ext; unfold raw42179step1 raw42179step0; decide +kernel
      have hl : raw42179step0Labels = labelEmbedding10 ∘ raw42179step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42179step0 raw42179step0Labels raw42179step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical42180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42180 raw42180Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw42180 raw42180Labels = mixedMoment B raw42180step0 raw42180step0Labels := by
      have ha : raw42180step0 = (fun i j => raw42180 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42180step0 raw42180; decide +kernel
      have hl : raw42180step0Labels = raw42180Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42180 raw42180Labels permutation157 permutation2
    mixedMoment B raw42180step0 raw42180step0Labels = mixedMoment B raw42180step1 raw42180step1Labels := by
      have ha : raw42180step1 = raw42180step0 := by apply Matrix.ext; unfold raw42180step1 raw42180step0; decide +kernel
      have hl : raw42180step0Labels = labelEmbedding1 ∘ raw42180step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42180step0 raw42180step0Labels raw42180step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3994 node3994Labels := by rfl

theorem canonical42181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42181 raw42181Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw42181 raw42181Labels = mixedMoment B raw42181step0 raw42181step0Labels := by
      have ha : raw42181step0 = (fun i j => raw42181 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42181step0 raw42181; decide +kernel
      have hl : raw42181step0Labels = raw42181Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42181 raw42181Labels permutation152 permutation3
    mixedMoment B raw42181step0 raw42181step0Labels = mixedMoment B raw42181step1 raw42181step1Labels := by
      have ha : raw42181step1 = raw42181step0 := by apply Matrix.ext; unfold raw42181step1 raw42181step0; decide +kernel
      have hl : raw42181step0Labels = labelEmbedding7 ∘ raw42181step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42181step0 raw42181step0Labels raw42181step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical42182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42182 raw42182Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw42182 raw42182Labels = mixedMoment B raw42182step0 raw42182step0Labels := by
      have hz : ∀ j, raw42182 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42182step0 = (fun i j => raw42182 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42182step0 raw42182; decide +kernel
      have hl : raw42182step0Labels = raw42182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42182 raw42182Labels permutation434 hz
    mixedMoment B raw42182step0 raw42182step0Labels = mixedMoment B raw42182step1 raw42182step1Labels := by
      have hz : ∀ j, raw42182step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42182step1 = (fun i j => raw42182step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42182step1 raw42182step0; decide +kernel
      have hl : raw42182step1Labels = raw42182step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42182step0 raw42182step0Labels permutation80 hz
    mixedMoment B raw42182step1 raw42182step1Labels = mixedMoment B raw42182step2 raw42182step2Labels := by
      have ha : raw42182step2 = (fun i j => raw42182step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42182step2 raw42182step1; decide +kernel
      have hl : raw42182step2Labels = raw42182step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42182step1 raw42182step1Labels permutation26 permutation4
    mixedMoment B raw42182step2 raw42182step2Labels = mixedMoment B raw42182step3 raw42182step3Labels := by
      have ha : raw42182step3 = raw42182step2 := by apply Matrix.ext; unfold raw42182step3 raw42182step2; decide +kernel
      have hl : raw42182step2Labels = labelEmbedding1 ∘ raw42182step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42182step2 raw42182step2Labels raw42182step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3119 node3119Labels := by rfl

theorem canonical42183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42183 raw42183Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw42183 raw42183Labels = mixedMoment B raw42183step0 raw42183step0Labels := by
      have hz : ∀ j, raw42183 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42183step0 = (fun i j => raw42183 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42183step0 raw42183; decide +kernel
      have hl : raw42183step0Labels = raw42183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42183 raw42183Labels permutation434 hz
    mixedMoment B raw42183step0 raw42183step0Labels = mixedMoment B raw42183step1 raw42183step1Labels := by
      have hz : ∀ j, raw42183step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42183step1 = (fun i j => raw42183step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42183step1 raw42183step0; decide +kernel
      have hl : raw42183step1Labels = raw42183step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42183step0 raw42183step0Labels permutation80 hz
    mixedMoment B raw42183step1 raw42183step1Labels = mixedMoment B raw42183step2 raw42183step2Labels := by
      have ha : raw42183step2 = (fun i j => raw42183step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42183step2 raw42183step1; decide +kernel
      have hl : raw42183step2Labels = raw42183step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42183step1 raw42183step1Labels permutation31 permutation5
    mixedMoment B raw42183step2 raw42183step2Labels = mixedMoment B raw42183step3 raw42183step3Labels := by
      have ha : raw42183step3 = raw42183step2 := by apply Matrix.ext; unfold raw42183step3 raw42183step2; decide +kernel
      have hl : raw42183step2Labels = labelEmbedding9 ∘ raw42183step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42183step2 raw42183step2Labels raw42183step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical42184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42184 raw42184Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw42184 raw42184Labels = mixedMoment B raw42184step0 raw42184step0Labels := by
      have hz : ∀ j, raw42184 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42184step0 = (fun i j => raw42184 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42184step0 raw42184; decide +kernel
      have hl : raw42184step0Labels = raw42184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42184 raw42184Labels permutation434 hz
    mixedMoment B raw42184step0 raw42184step0Labels = mixedMoment B raw42184step1 raw42184step1Labels := by
      have hz : ∀ j, raw42184step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42184step1 = (fun i j => raw42184step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42184step1 raw42184step0; decide +kernel
      have hl : raw42184step1Labels = raw42184step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42184step0 raw42184step0Labels permutation80 hz
    mixedMoment B raw42184step1 raw42184step1Labels = mixedMoment B raw42184step2 raw42184step2Labels := by
      have ha : raw42184step2 = (fun i j => raw42184step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42184step2 raw42184step1; decide +kernel
      have hl : raw42184step2Labels = raw42184step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42184step1 raw42184step1Labels permutation20 permutation4
    mixedMoment B raw42184step2 raw42184step2Labels = mixedMoment B raw42184step3 raw42184step3Labels := by
      have ha : raw42184step3 = raw42184step2 := by apply Matrix.ext; unfold raw42184step3 raw42184step2; decide +kernel
      have hl : raw42184step2Labels = labelEmbedding1 ∘ raw42184step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42184step2 raw42184step2Labels raw42184step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

theorem canonical42185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42185 raw42185Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw42185 raw42185Labels = mixedMoment B raw42185step0 raw42185step0Labels := by
      have hz : ∀ j, raw42185 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42185step0 = (fun i j => raw42185 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42185step0 raw42185; decide +kernel
      have hl : raw42185step0Labels = raw42185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42185 raw42185Labels permutation434 hz
    mixedMoment B raw42185step0 raw42185step0Labels = mixedMoment B raw42185step1 raw42185step1Labels := by
      have hz : ∀ j, raw42185step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42185step1 = (fun i j => raw42185step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42185step1 raw42185step0; decide +kernel
      have hl : raw42185step1Labels = raw42185step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42185step0 raw42185step0Labels permutation80 hz
    mixedMoment B raw42185step1 raw42185step1Labels = mixedMoment B raw42185step2 raw42185step2Labels := by
      have ha : raw42185step2 = (fun i j => raw42185step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42185step2 raw42185step1; decide +kernel
      have hl : raw42185step2Labels = raw42185step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42185step1 raw42185step1Labels permutation28 permutation7
    mixedMoment B raw42185step2 raw42185step2Labels = mixedMoment B raw42185step3 raw42185step3Labels := by
      have ha : raw42185step3 = raw42185step2 := by apply Matrix.ext; unfold raw42185step3 raw42185step2; decide +kernel
      have hl : raw42185step2Labels = labelEmbedding6 ∘ raw42185step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42185step2 raw42185step2Labels raw42185step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

theorem canonical42186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42186 raw42186Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw42186 raw42186Labels = mixedMoment B raw42186step0 raw42186step0Labels := by
      have hz : ∀ j, raw42186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42186step0 = (fun i j => raw42186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42186step0 raw42186; decide +kernel
      have hl : raw42186step0Labels = raw42186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42186 raw42186Labels permutation346 hz
    mixedMoment B raw42186step0 raw42186step0Labels = mixedMoment B raw42186step1 raw42186step1Labels := by
      have ha : raw42186step1 = raw42186step0 := by apply Matrix.ext; unfold raw42186step1 raw42186step0; decide +kernel
      have hl : raw42186step0Labels = labelEmbedding1 ∘ raw42186step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42186step0 raw42186step0Labels raw42186step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

theorem canonical42187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42187 raw42187Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw42187 raw42187Labels = mixedMoment B raw42187step0 raw42187step0Labels := by
      have hz : ∀ j, raw42187 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42187step0 = (fun i j => raw42187 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42187step0 raw42187; decide +kernel
      have hl : raw42187step0Labels = raw42187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42187 raw42187Labels permutation346 hz
    mixedMoment B raw42187step0 raw42187step0Labels = mixedMoment B raw42187step1 raw42187step1Labels := by
      have ha : raw42187step1 = (fun i j => raw42187step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42187step1 raw42187step0; decide +kernel
      have hl : raw42187step1Labels = raw42187step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42187step0 raw42187step0Labels permutation145 permutation5
    mixedMoment B raw42187step1 raw42187step1Labels = mixedMoment B raw42187step2 raw42187step2Labels := by
      have ha : raw42187step2 = raw42187step1 := by apply Matrix.ext; unfold raw42187step2 raw42187step1; decide +kernel
      have hl : raw42187step1Labels = labelEmbedding9 ∘ raw42187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42187step1 raw42187step1Labels raw42187step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical42188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42188 raw42188Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw42188 raw42188Labels = mixedMoment B raw42188step0 raw42188step0Labels := by
      have hz : ∀ j, raw42188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42188step0 = (fun i j => raw42188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42188step0 raw42188; decide +kernel
      have hl : raw42188step0Labels = raw42188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42188 raw42188Labels permutation346 hz
    mixedMoment B raw42188step0 raw42188step0Labels = mixedMoment B raw42188step1 raw42188step1Labels := by
      have ha : raw42188step1 = (fun i j => raw42188step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42188step1 raw42188step0; decide +kernel
      have hl : raw42188step1Labels = raw42188step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42188step0 raw42188step0Labels permutation151 permutation2
    mixedMoment B raw42188step1 raw42188step1Labels = mixedMoment B raw42188step2 raw42188step2Labels := by
      have ha : raw42188step2 = -raw42188step1 := by apply Matrix.ext; change ∀ i j, raw42188step2 i j = -(raw42188step1 i j); unfold raw42188step2 raw42188step1; decide +kernel
      have hl : raw42188step2Labels = raw42188step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42188step2 raw42188step2Labels = mixedMoment B raw42188step3 raw42188step3Labels := by
      have ha : raw42188step3 = raw42188step2 := by apply Matrix.ext; unfold raw42188step3 raw42188step2; decide +kernel
      have hl : raw42188step2Labels = labelEmbedding1 ∘ raw42188step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42188step2 raw42188step2Labels raw42188step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical42189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42189 raw42189Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw42189 raw42189Labels = mixedMoment B raw42189step0 raw42189step0Labels := by
      have hz : ∀ j, raw42189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42189step0 = (fun i j => raw42189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42189step0 raw42189; decide +kernel
      have hl : raw42189step0Labels = raw42189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42189 raw42189Labels permutation346 hz
    mixedMoment B raw42189step0 raw42189step0Labels = mixedMoment B raw42189step1 raw42189step1Labels := by
      have ha : raw42189step1 = (fun i j => raw42189step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42189step1 raw42189step0; decide +kernel
      have hl : raw42189step1Labels = raw42189step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42189step0 raw42189step0Labels permutation139 permutation7
    mixedMoment B raw42189step1 raw42189step1Labels = mixedMoment B raw42189step2 raw42189step2Labels := by
      have ha : raw42189step2 = raw42189step1 := by apply Matrix.ext; unfold raw42189step2 raw42189step1; decide +kernel
      have hl : raw42189step1Labels = labelEmbedding6 ∘ raw42189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42189step1 raw42189step1Labels raw42189step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical42190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42190 raw42190Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw42190 raw42190Labels = mixedMoment B raw42190step0 raw42190step0Labels := by
      have hz : ∀ j, raw42190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42190step0 = (fun i j => raw42190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42190step0 raw42190; decide +kernel
      have hl : raw42190step0Labels = raw42190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42190 raw42190Labels permutation346 hz
    mixedMoment B raw42190step0 raw42190step0Labels = mixedMoment B raw42190step1 raw42190step1Labels := by
      have ha : raw42190step1 = (fun i j => raw42190step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42190step1 raw42190step0; decide +kernel
      have hl : raw42190step1Labels = raw42190step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42190step0 raw42190step0Labels permutation151 permutation2
    mixedMoment B raw42190step1 raw42190step1Labels = mixedMoment B raw42190step2 raw42190step2Labels := by
      have ha : raw42190step2 = -raw42190step1 := by apply Matrix.ext; change ∀ i j, raw42190step2 i j = -(raw42190step1 i j); unfold raw42190step2 raw42190step1; decide +kernel
      have hl : raw42190step2Labels = raw42190step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42190step2 raw42190step2Labels = mixedMoment B raw42190step3 raw42190step3Labels := by
      have ha : raw42190step3 = raw42190step2 := by apply Matrix.ext; unfold raw42190step3 raw42190step2; decide +kernel
      have hl : raw42190step2Labels = labelEmbedding1 ∘ raw42190step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42190step2 raw42190step2Labels raw42190step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

theorem canonical42191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42191 raw42191Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw42191 raw42191Labels = mixedMoment B raw42191step0 raw42191step0Labels := by
      have hz : ∀ j, raw42191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42191step0 = (fun i j => raw42191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42191step0 raw42191; decide +kernel
      have hl : raw42191step0Labels = raw42191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42191 raw42191Labels permutation346 hz
    mixedMoment B raw42191step0 raw42191step0Labels = mixedMoment B raw42191step1 raw42191step1Labels := by
      have ha : raw42191step1 = (fun i j => raw42191step0 (permutation148 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42191step1 raw42191step0; decide +kernel
      have hl : raw42191step1Labels = raw42191step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42191step0 raw42191step0Labels permutation148 permutation7
    mixedMoment B raw42191step1 raw42191step1Labels = mixedMoment B raw42191step2 raw42191step2Labels := by
      have ha : raw42191step2 = raw42191step1 := by apply Matrix.ext; unfold raw42191step2 raw42191step1; decide +kernel
      have hl : raw42191step1Labels = labelEmbedding6 ∘ raw42191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42191step1 raw42191step1Labels raw42191step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

theorem canonical42192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42192 raw42192Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw42192 raw42192Labels = mixedMoment B raw42192step0 raw42192step0Labels := by
      have hz : ∀ j, raw42192 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42192step0 = (fun i j => raw42192 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42192step0 raw42192; decide +kernel
      have hl : raw42192step0Labels = raw42192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42192 raw42192Labels permutation346 hz
    mixedMoment B raw42192step0 raw42192step0Labels = mixedMoment B raw42192step1 raw42192step1Labels := by
      have ha : raw42192step1 = (fun i j => raw42192step0 (permutation146 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42192step1 raw42192step0; decide +kernel
      have hl : raw42192step1Labels = raw42192step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42192step0 raw42192step0Labels permutation146 permutation4
    mixedMoment B raw42192step1 raw42192step1Labels = mixedMoment B raw42192step2 raw42192step2Labels := by
      have ha : raw42192step2 = raw42192step1 := by apply Matrix.ext; unfold raw42192step2 raw42192step1; decide +kernel
      have hl : raw42192step1Labels = labelEmbedding1 ∘ raw42192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42192step1 raw42192step1Labels raw42192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

theorem canonical42193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42193 raw42193Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw42193 raw42193Labels = mixedMoment B raw42193step0 raw42193step0Labels := by
      have hz : ∀ j, raw42193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42193step0 = (fun i j => raw42193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42193step0 raw42193; decide +kernel
      have hl : raw42193step0Labels = raw42193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42193 raw42193Labels permutation346 hz
    mixedMoment B raw42193step0 raw42193step0Labels = mixedMoment B raw42193step1 raw42193step1Labels := by
      have ha : raw42193step1 = (fun i j => raw42193step0 (permutation146 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42193step1 raw42193step0; decide +kernel
      have hl : raw42193step1Labels = raw42193step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42193step0 raw42193step0Labels permutation146 permutation4
    mixedMoment B raw42193step1 raw42193step1Labels = mixedMoment B raw42193step2 raw42193step2Labels := by
      have ha : raw42193step2 = raw42193step1 := by apply Matrix.ext; unfold raw42193step2 raw42193step1; decide +kernel
      have hl : raw42193step1Labels = labelEmbedding10 ∘ raw42193step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42193step1 raw42193step1Labels raw42193step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical42194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42194 raw42194Labels = mixedMoment B node3997 node3997Labels := by
  calc
    mixedMoment B raw42194 raw42194Labels = mixedMoment B raw42194step0 raw42194step0Labels := by
      have hz : ∀ j, raw42194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42194step0 = (fun i j => raw42194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42194step0 raw42194; decide +kernel
      have hl : raw42194step0Labels = raw42194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42194 raw42194Labels permutation346 hz
    mixedMoment B raw42194step0 raw42194step0Labels = mixedMoment B raw42194step1 raw42194step1Labels := by
      have ha : raw42194step1 = (fun i j => raw42194step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42194step1 raw42194step0; decide +kernel
      have hl : raw42194step1Labels = raw42194step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42194step0 raw42194step0Labels permutation37 permutation2
    mixedMoment B raw42194step1 raw42194step1Labels = mixedMoment B raw42194step2 raw42194step2Labels := by
      have ha : raw42194step2 = raw42194step1 := by apply Matrix.ext; unfold raw42194step2 raw42194step1; decide +kernel
      have hl : raw42194step1Labels = labelEmbedding1 ∘ raw42194step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42194step1 raw42194step1Labels raw42194step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3997 node3997Labels := by rfl

theorem canonical42195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42195 raw42195Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw42195 raw42195Labels = mixedMoment B raw42195step0 raw42195step0Labels := by
      have hz : ∀ j, raw42195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42195step0 = (fun i j => raw42195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42195step0 raw42195; decide +kernel
      have hl : raw42195step0Labels = raw42195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42195 raw42195Labels permutation346 hz
    mixedMoment B raw42195step0 raw42195step0Labels = mixedMoment B raw42195step1 raw42195step1Labels := by
      have ha : raw42195step1 = (fun i j => raw42195step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42195step1 raw42195step0; decide +kernel
      have hl : raw42195step1Labels = raw42195step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42195step0 raw42195step0Labels permutation32 permutation3
    mixedMoment B raw42195step1 raw42195step1Labels = mixedMoment B raw42195step2 raw42195step2Labels := by
      have ha : raw42195step2 = raw42195step1 := by apply Matrix.ext; unfold raw42195step2 raw42195step1; decide +kernel
      have hl : raw42195step1Labels = labelEmbedding7 ∘ raw42195step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42195step1 raw42195step1Labels raw42195step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical42196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42196 raw42196Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw42196 raw42196Labels = mixedMoment B raw42196step0 raw42196step0Labels := by
      have ha : raw42196step0 = (fun i j => raw42196 (permutation641 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42196step0 raw42196; decide +kernel
      have hl : raw42196step0Labels = raw42196Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42196 raw42196Labels permutation641 permutation4
    mixedMoment B raw42196step0 raw42196step0Labels = mixedMoment B raw42196step1 raw42196step1Labels := by
      have ha : raw42196step1 = raw42196step0 := by apply Matrix.ext; unfold raw42196step1 raw42196step0; decide +kernel
      have hl : raw42196step0Labels = labelEmbedding1 ∘ raw42196step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42196step0 raw42196step0Labels raw42196step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

theorem canonical42197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42197 raw42197Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw42197 raw42197Labels = mixedMoment B raw42197step0 raw42197step0Labels := by
      have ha : raw42197step0 = (fun i j => raw42197 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42197step0 raw42197; decide +kernel
      have hl : raw42197step0Labels = raw42197Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42197 raw42197Labels permutation152 permutation3
    mixedMoment B raw42197step0 raw42197step0Labels = mixedMoment B raw42197step1 raw42197step1Labels := by
      have ha : raw42197step1 = raw42197step0 := by apply Matrix.ext; unfold raw42197step1 raw42197step0; decide +kernel
      have hl : raw42197step0Labels = labelEmbedding7 ∘ raw42197step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42197step0 raw42197step0Labels raw42197step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

theorem canonical42198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42198 raw42198Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw42198 raw42198Labels = mixedMoment B raw42198step0 raw42198step0Labels := by
      have ha : raw42198step0 = (fun i j => raw42198 (permutation428 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42198step0 raw42198; decide +kernel
      have hl : raw42198step0Labels = raw42198Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42198 raw42198Labels permutation428 permutation4
    mixedMoment B raw42198step0 raw42198step0Labels = mixedMoment B raw42198step1 raw42198step1Labels := by
      have ha : raw42198step1 = raw42198step0 := by apply Matrix.ext; unfold raw42198step1 raw42198step0; decide +kernel
      have hl : raw42198step0Labels = labelEmbedding1 ∘ raw42198step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42198step0 raw42198step0Labels raw42198step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

theorem canonical42199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42199 raw42199Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42199 raw42199Labels = mixedMoment B raw42199step0 raw42199step0Labels := by
      have ha : raw42199step0 = (fun i j => raw42199 (permutation428 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42199step0 raw42199; decide +kernel
      have hl : raw42199step0Labels = raw42199Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42199 raw42199Labels permutation428 permutation4
    mixedMoment B raw42199step0 raw42199step0Labels = mixedMoment B raw42199step1 raw42199step1Labels := by
      have ha : raw42199step1 = raw42199step0 := by apply Matrix.ext; unfold raw42199step1 raw42199step0; decide +kernel
      have hl : raw42199step0Labels = labelEmbedding10 ∘ raw42199step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42199step0 raw42199step0Labels raw42199step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical42200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42200 raw42200Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw42200 raw42200Labels = mixedMoment B raw42200step0 raw42200step0Labels := by
      have hz : ∀ j, raw42200 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42200step0 = (fun i j => raw42200 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42200step0 raw42200; decide +kernel
      have hl : raw42200step0Labels = raw42200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42200 raw42200Labels permutation520 hz
    mixedMoment B raw42200step0 raw42200step0Labels = mixedMoment B raw42200step1 raw42200step1Labels := by
      have hz : ∀ j, raw42200step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42200step1 = (fun i j => raw42200step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42200step1 raw42200step0; decide +kernel
      have hl : raw42200step1Labels = raw42200step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42200step0 raw42200step0Labels permutation104 hz
    mixedMoment B raw42200step1 raw42200step1Labels = mixedMoment B raw42200step2 raw42200step2Labels := by
      have ha : raw42200step2 = (fun i j => raw42200step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42200step2 raw42200step1; decide +kernel
      have hl : raw42200step2Labels = raw42200step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42200step1 raw42200step1Labels permutation31 permutation2
    mixedMoment B raw42200step2 raw42200step2Labels = mixedMoment B raw42200step3 raw42200step3Labels := by
      have ha : raw42200step3 = -raw42200step2 := by apply Matrix.ext; change ∀ i j, raw42200step3 i j = -(raw42200step2 i j); unfold raw42200step3 raw42200step2; decide +kernel
      have hl : raw42200step3Labels = raw42200step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42200step3 raw42200step3Labels = mixedMoment B raw42200step4 raw42200step4Labels := by
      have ha : raw42200step4 = raw42200step3 := by apply Matrix.ext; unfold raw42200step4 raw42200step3; decide +kernel
      have hl : raw42200step3Labels = labelEmbedding1 ∘ raw42200step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42200step3 raw42200step3Labels raw42200step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3225 node3225Labels := by rfl

theorem canonical42201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42201 raw42201Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw42201 raw42201Labels = mixedMoment B raw42201step0 raw42201step0Labels := by
      have hz : ∀ j, raw42201 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42201step0 = (fun i j => raw42201 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42201step0 raw42201; decide +kernel
      have hl : raw42201step0Labels = raw42201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42201 raw42201Labels permutation520 hz
    mixedMoment B raw42201step0 raw42201step0Labels = mixedMoment B raw42201step1 raw42201step1Labels := by
      have hz : ∀ j, raw42201step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42201step1 = (fun i j => raw42201step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42201step1 raw42201step0; decide +kernel
      have hl : raw42201step1Labels = raw42201step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42201step0 raw42201step0Labels permutation104 hz
    mixedMoment B raw42201step1 raw42201step1Labels = mixedMoment B raw42201step2 raw42201step2Labels := by
      have ha : raw42201step2 = (fun i j => raw42201step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42201step2 raw42201step1; decide +kernel
      have hl : raw42201step2Labels = raw42201step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42201step1 raw42201step1Labels permutation28 permutation5
    mixedMoment B raw42201step2 raw42201step2Labels = mixedMoment B raw42201step3 raw42201step3Labels := by
      have ha : raw42201step3 = raw42201step2 := by apply Matrix.ext; unfold raw42201step3 raw42201step2; decide +kernel
      have hl : raw42201step2Labels = labelEmbedding9 ∘ raw42201step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42201step2 raw42201step2Labels raw42201step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical42202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42202 raw42202Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw42202 raw42202Labels = mixedMoment B raw42202step0 raw42202step0Labels := by
      have hz : ∀ j, raw42202 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42202step0 = (fun i j => raw42202 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42202step0 raw42202; decide +kernel
      have hl : raw42202step0Labels = raw42202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42202 raw42202Labels permutation434 hz
    mixedMoment B raw42202step0 raw42202step0Labels = mixedMoment B raw42202step1 raw42202step1Labels := by
      have ha : raw42202step1 = (fun i j => raw42202step0 (permutation138 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42202step1 raw42202step0; decide +kernel
      have hl : raw42202step1Labels = raw42202step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42202step0 raw42202step0Labels permutation138 permutation4
    mixedMoment B raw42202step1 raw42202step1Labels = mixedMoment B raw42202step2 raw42202step2Labels := by
      have ha : raw42202step2 = raw42202step1 := by apply Matrix.ext; unfold raw42202step2 raw42202step1; decide +kernel
      have hl : raw42202step1Labels = labelEmbedding1 ∘ raw42202step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42202step1 raw42202step1Labels raw42202step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3086 node3086Labels := by rfl

theorem canonical42203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42203 raw42203Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw42203 raw42203Labels = mixedMoment B raw42203step0 raw42203step0Labels := by
      have hz : ∀ j, raw42203 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42203step0 = (fun i j => raw42203 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42203step0 raw42203; decide +kernel
      have hl : raw42203step0Labels = raw42203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42203 raw42203Labels permutation434 hz
    mixedMoment B raw42203step0 raw42203step0Labels = mixedMoment B raw42203step1 raw42203step1Labels := by
      have ha : raw42203step1 = (fun i j => raw42203step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42203step1 raw42203step0; decide +kernel
      have hl : raw42203step1Labels = raw42203step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42203step0 raw42203step0Labels permutation148 permutation5
    mixedMoment B raw42203step1 raw42203step1Labels = mixedMoment B raw42203step2 raw42203step2Labels := by
      have ha : raw42203step2 = raw42203step1 := by apply Matrix.ext; unfold raw42203step2 raw42203step1; decide +kernel
      have hl : raw42203step1Labels = labelEmbedding9 ∘ raw42203step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42203step1 raw42203step1Labels raw42203step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

theorem canonical42204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42204 raw42204Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw42204 raw42204Labels = mixedMoment B raw42204step0 raw42204step0Labels := by
      have hz : ∀ j, raw42204 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42204step0 = (fun i j => raw42204 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42204step0 raw42204; decide +kernel
      have hl : raw42204step0Labels = raw42204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42204 raw42204Labels permutation434 hz
    mixedMoment B raw42204step0 raw42204step0Labels = mixedMoment B raw42204step1 raw42204step1Labels := by
      have ha : raw42204step1 = (fun i j => raw42204step0 (permutation80 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42204step1 raw42204step0; decide +kernel
      have hl : raw42204step1Labels = raw42204step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42204step0 raw42204step0Labels permutation80 permutation4
    mixedMoment B raw42204step1 raw42204step1Labels = mixedMoment B raw42204step2 raw42204step2Labels := by
      have ha : raw42204step2 = -raw42204step1 := by apply Matrix.ext; change ∀ i j, raw42204step2 i j = -(raw42204step1 i j); unfold raw42204step2 raw42204step1; decide +kernel
      have hl : raw42204step2Labels = raw42204step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42204step2 raw42204step2Labels = mixedMoment B raw42204step3 raw42204step3Labels := by
      have ha : raw42204step3 = raw42204step2 := by apply Matrix.ext; unfold raw42204step3 raw42204step2; decide +kernel
      have hl : raw42204step2Labels = labelEmbedding1 ∘ raw42204step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42204step2 raw42204step2Labels raw42204step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

theorem canonical42205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42205 raw42205Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw42205 raw42205Labels = mixedMoment B raw42205step0 raw42205step0Labels := by
      have hz : ∀ j, raw42205 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42205step0 = (fun i j => raw42205 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42205step0 raw42205; decide +kernel
      have hl : raw42205step0Labels = raw42205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42205 raw42205Labels permutation434 hz
    mixedMoment B raw42205step0 raw42205step0Labels = mixedMoment B raw42205step1 raw42205step1Labels := by
      have ha : raw42205step1 = (fun i j => raw42205step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42205step1 raw42205step0; decide +kernel
      have hl : raw42205step1Labels = raw42205step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42205step0 raw42205step0Labels permutation148 permutation5
    mixedMoment B raw42205step1 raw42205step1Labels = mixedMoment B raw42205step2 raw42205step2Labels := by
      have ha : raw42205step2 = raw42205step1 := by apply Matrix.ext; unfold raw42205step2 raw42205step1; decide +kernel
      have hl : raw42205step1Labels = labelEmbedding9 ∘ raw42205step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42205step1 raw42205step1Labels raw42205step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical42206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42206 raw42206Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw42206 raw42206Labels = mixedMoment B raw42206step0 raw42206step0Labels := by
      have hz : ∀ j, raw42206 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42206step0 = (fun i j => raw42206 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42206step0 raw42206; decide +kernel
      have hl : raw42206step0Labels = raw42206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42206 raw42206Labels permutation434 hz
    mixedMoment B raw42206step0 raw42206step0Labels = mixedMoment B raw42206step1 raw42206step1Labels := by
      have ha : raw42206step1 = (fun i j => raw42206step0 (permutation81 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42206step1 raw42206step0; decide +kernel
      have hl : raw42206step1Labels = raw42206step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42206step0 raw42206step0Labels permutation81 permutation4
    mixedMoment B raw42206step1 raw42206step1Labels = mixedMoment B raw42206step2 raw42206step2Labels := by
      have ha : raw42206step2 = -raw42206step1 := by apply Matrix.ext; change ∀ i j, raw42206step2 i j = -(raw42206step1 i j); unfold raw42206step2 raw42206step1; decide +kernel
      have hl : raw42206step2Labels = raw42206step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42206step2 raw42206step2Labels = mixedMoment B raw42206step3 raw42206step3Labels := by
      have ha : raw42206step3 = raw42206step2 := by apply Matrix.ext; unfold raw42206step3 raw42206step2; decide +kernel
      have hl : raw42206step2Labels = labelEmbedding1 ∘ raw42206step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42206step2 raw42206step2Labels raw42206step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

theorem canonical42207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42207 raw42207Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw42207 raw42207Labels = mixedMoment B raw42207step0 raw42207step0Labels := by
      have hz : ∀ j, raw42207 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42207step0 = (fun i j => raw42207 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42207step0 raw42207; decide +kernel
      have hl : raw42207step0Labels = raw42207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42207 raw42207Labels permutation434 hz
    mixedMoment B raw42207step0 raw42207step0Labels = mixedMoment B raw42207step1 raw42207step1Labels := by
      have ha : raw42207step1 = (fun i j => raw42207step0 (permutation81 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42207step1 raw42207step0; decide +kernel
      have hl : raw42207step1Labels = raw42207step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42207step0 raw42207step0Labels permutation81 permutation4
    mixedMoment B raw42207step1 raw42207step1Labels = mixedMoment B raw42207step2 raw42207step2Labels := by
      have ha : raw42207step2 = -raw42207step1 := by apply Matrix.ext; change ∀ i j, raw42207step2 i j = -(raw42207step1 i j); unfold raw42207step2 raw42207step1; decide +kernel
      have hl : raw42207step2Labels = raw42207step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42207step2 raw42207step2Labels = mixedMoment B raw42207step3 raw42207step3Labels := by
      have ha : raw42207step3 = raw42207step2 := by apply Matrix.ext; unfold raw42207step3 raw42207step2; decide +kernel
      have hl : raw42207step2Labels = labelEmbedding10 ∘ raw42207step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42207step2 raw42207step2Labels raw42207step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

theorem canonical42208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42208 raw42208Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw42208 raw42208Labels = mixedMoment B raw42208step0 raw42208step0Labels := by
      have hz : ∀ j, raw42208 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42208step0 = (fun i j => raw42208 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42208step0 raw42208; decide +kernel
      have hl : raw42208step0Labels = raw42208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42208 raw42208Labels permutation434 hz
    mixedMoment B raw42208step0 raw42208step0Labels = mixedMoment B raw42208step1 raw42208step1Labels := by
      have ha : raw42208step1 = (fun i j => raw42208step0 (permutation114 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42208step1 raw42208step0; decide +kernel
      have hl : raw42208step1Labels = raw42208step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42208step0 raw42208step0Labels permutation114 permutation4
    mixedMoment B raw42208step1 raw42208step1Labels = mixedMoment B raw42208step2 raw42208step2Labels := by
      have ha : raw42208step2 = raw42208step1 := by apply Matrix.ext; unfold raw42208step2 raw42208step1; decide +kernel
      have hl : raw42208step1Labels = labelEmbedding1 ∘ raw42208step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42208step1 raw42208step1Labels raw42208step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2729 node2729Labels := by rfl

theorem canonical42209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42209 raw42209Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw42209 raw42209Labels = mixedMoment B raw42209step0 raw42209step0Labels := by
      have hz : ∀ j, raw42209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42209step0 = (fun i j => raw42209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42209step0 raw42209; decide +kernel
      have hl : raw42209step0Labels = raw42209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42209 raw42209Labels permutation434 hz
    mixedMoment B raw42209step0 raw42209step0Labels = mixedMoment B raw42209step1 raw42209step1Labels := by
      have ha : raw42209step1 = (fun i j => raw42209step0 (permutation114 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42209step1 raw42209step0; decide +kernel
      have hl : raw42209step1Labels = raw42209step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42209step0 raw42209step0Labels permutation114 permutation4
    mixedMoment B raw42209step1 raw42209step1Labels = mixedMoment B raw42209step2 raw42209step2Labels := by
      have ha : raw42209step2 = raw42209step1 := by apply Matrix.ext; unfold raw42209step2 raw42209step1; decide +kernel
      have hl : raw42209step1Labels = labelEmbedding10 ∘ raw42209step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42209step1 raw42209step1Labels raw42209step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

theorem canonical42210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42210 raw42210Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw42210 raw42210Labels = mixedMoment B raw42210step0 raw42210step0Labels := by
      have ha : raw42210step0 = (fun i j => raw42210 (permutation356 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42210step0 raw42210; decide +kernel
      have hl : raw42210step0Labels = raw42210Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42210 raw42210Labels permutation356 permutation4
    mixedMoment B raw42210step0 raw42210step0Labels = mixedMoment B raw42210step1 raw42210step1Labels := by
      have ha : raw42210step1 = -raw42210step0 := by apply Matrix.ext; change ∀ i j, raw42210step1 i j = -(raw42210step0 i j); unfold raw42210step1 raw42210step0; decide +kernel
      have hl : raw42210step1Labels = raw42210step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42210step1 raw42210step1Labels = mixedMoment B raw42210step2 raw42210step2Labels := by
      have ha : raw42210step2 = raw42210step1 := by apply Matrix.ext; unfold raw42210step2 raw42210step1; decide +kernel
      have hl : raw42210step1Labels = labelEmbedding1 ∘ raw42210step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42210step1 raw42210step1Labels raw42210step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3872 node3872Labels := by rfl

theorem canonical42211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42211 raw42211Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42211 raw42211Labels = mixedMoment B raw42211step0 raw42211step0Labels := by
      have ha : raw42211step0 = (fun i j => raw42211 (permutation661 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42211step0 raw42211; decide +kernel
      have hl : raw42211step0Labels = raw42211Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42211 raw42211Labels permutation661 permutation5
    mixedMoment B raw42211step0 raw42211step0Labels = mixedMoment B raw42211step1 raw42211step1Labels := by
      have ha : raw42211step1 = raw42211step0 := by apply Matrix.ext; unfold raw42211step1 raw42211step0; decide +kernel
      have hl : raw42211step0Labels = labelEmbedding9 ∘ raw42211step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42211step0 raw42211step0Labels raw42211step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical42212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42212 raw42212Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw42212 raw42212Labels = mixedMoment B raw42212step0 raw42212step0Labels := by
      have ha : raw42212step0 = (fun i j => raw42212 (permutation351 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42212step0 raw42212; decide +kernel
      have hl : raw42212step0Labels = raw42212Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42212 raw42212Labels permutation351 permutation4
    mixedMoment B raw42212step0 raw42212step0Labels = mixedMoment B raw42212step1 raw42212step1Labels := by
      have ha : raw42212step1 = -raw42212step0 := by apply Matrix.ext; change ∀ i j, raw42212step1 i j = -(raw42212step0 i j); unfold raw42212step1 raw42212step0; decide +kernel
      have hl : raw42212step1Labels = raw42212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42212step1 raw42212step1Labels = mixedMoment B raw42212step2 raw42212step2Labels := by
      have ha : raw42212step2 = raw42212step1 := by apply Matrix.ext; unfold raw42212step2 raw42212step1; decide +kernel
      have hl : raw42212step1Labels = labelEmbedding1 ∘ raw42212step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42212step1 raw42212step1Labels raw42212step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical42213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42213 raw42213Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw42213 raw42213Labels = mixedMoment B raw42213step0 raw42213step0Labels := by
      have ha : raw42213step0 = (fun i j => raw42213 (permutation351 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42213step0 raw42213; decide +kernel
      have hl : raw42213step0Labels = raw42213Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42213 raw42213Labels permutation351 permutation4
    mixedMoment B raw42213step0 raw42213step0Labels = mixedMoment B raw42213step1 raw42213step1Labels := by
      have ha : raw42213step1 = -raw42213step0 := by apply Matrix.ext; change ∀ i j, raw42213step1 i j = -(raw42213step0 i j); unfold raw42213step1 raw42213step0; decide +kernel
      have hl : raw42213step1Labels = raw42213step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42213step1 raw42213step1Labels = mixedMoment B raw42213step2 raw42213step2Labels := by
      have ha : raw42213step2 = raw42213step1 := by apply Matrix.ext; unfold raw42213step2 raw42213step1; decide +kernel
      have hl : raw42213step1Labels = labelEmbedding10 ∘ raw42213step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42213step1 raw42213step1Labels raw42213step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical42214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42214 raw42214Labels = mixedMoment B node3866 node3866Labels := by
  calc
    mixedMoment B raw42214 raw42214Labels = mixedMoment B raw42214step0 raw42214step0Labels := by
      have ha : raw42214step0 = (fun i j => raw42214 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42214step0 raw42214; decide +kernel
      have hl : raw42214step0Labels = raw42214Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42214 raw42214Labels permutation682 permutation2
    mixedMoment B raw42214step0 raw42214step0Labels = mixedMoment B raw42214step1 raw42214step1Labels := by
      have ha : raw42214step1 = -raw42214step0 := by apply Matrix.ext; change ∀ i j, raw42214step1 i j = -(raw42214step0 i j); unfold raw42214step1 raw42214step0; decide +kernel
      have hl : raw42214step1Labels = raw42214step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42214step1 raw42214step1Labels = mixedMoment B raw42214step2 raw42214step2Labels := by
      have ha : raw42214step2 = raw42214step1 := by apply Matrix.ext; unfold raw42214step2 raw42214step1; decide +kernel
      have hl : raw42214step1Labels = labelEmbedding1 ∘ raw42214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42214step1 raw42214step1Labels raw42214step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3866 node3866Labels := by rfl

theorem canonical42215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42215 raw42215Labels = mixedMoment B node5382 node5382Labels := by
  calc
    mixedMoment B raw42215 raw42215Labels = mixedMoment B raw42215step0 raw42215step0Labels := by
      have ha : raw42215step0 = (fun i j => raw42215 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42215step0 raw42215; decide +kernel
      have hl : raw42215step0Labels = raw42215Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42215 raw42215Labels permutation414 permutation6
    _ = mixedMoment B node5382 node5382Labels := by rfl

theorem canonical42216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42216 raw42216Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw42216 raw42216Labels = mixedMoment B raw42216step0 raw42216step0Labels := by
      have ha : raw42216step0 = (fun i j => raw42216 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42216step0 raw42216; decide +kernel
      have hl : raw42216step0Labels = raw42216Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42216 raw42216Labels permutation682 permutation2
    mixedMoment B raw42216step0 raw42216step0Labels = mixedMoment B raw42216step1 raw42216step1Labels := by
      have ha : raw42216step1 = -raw42216step0 := by apply Matrix.ext; change ∀ i j, raw42216step1 i j = -(raw42216step0 i j); unfold raw42216step1 raw42216step0; decide +kernel
      have hl : raw42216step1Labels = raw42216step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42216step1 raw42216step1Labels = mixedMoment B raw42216step2 raw42216step2Labels := by
      have ha : raw42216step2 = raw42216step1 := by apply Matrix.ext; unfold raw42216step2 raw42216step1; decide +kernel
      have hl : raw42216step1Labels = labelEmbedding1 ∘ raw42216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42216step1 raw42216step1Labels raw42216step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

theorem canonical42217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42217 raw42217Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw42217 raw42217Labels = mixedMoment B raw42217step0 raw42217step0Labels := by
      have ha : raw42217step0 = (fun i j => raw42217 (permutation643 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42217step0 raw42217; decide +kernel
      have hl : raw42217step0Labels = raw42217Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42217 raw42217Labels permutation643 permutation7
    mixedMoment B raw42217step0 raw42217step0Labels = mixedMoment B raw42217step1 raw42217step1Labels := by
      have ha : raw42217step1 = raw42217step0 := by apply Matrix.ext; unfold raw42217step1 raw42217step0; decide +kernel
      have hl : raw42217step0Labels = labelEmbedding6 ∘ raw42217step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42217step0 raw42217step0Labels raw42217step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

theorem canonical42218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42218 raw42218Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw42218 raw42218Labels = mixedMoment B raw42218step0 raw42218step0Labels := by
      have ha : raw42218step0 = (fun i j => raw42218 (permutation615 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42218step0 raw42218; decide +kernel
      have hl : raw42218step0Labels = raw42218Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42218 raw42218Labels permutation615 permutation4
    mixedMoment B raw42218step0 raw42218step0Labels = mixedMoment B raw42218step1 raw42218step1Labels := by
      have ha : raw42218step1 = raw42218step0 := by apply Matrix.ext; unfold raw42218step1 raw42218step0; decide +kernel
      have hl : raw42218step0Labels = labelEmbedding1 ∘ raw42218step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42218step0 raw42218step0Labels raw42218step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2708 node2708Labels := by rfl

theorem canonical42219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42219 raw42219Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw42219 raw42219Labels = mixedMoment B raw42219step0 raw42219step0Labels := by
      have ha : raw42219step0 = (fun i j => raw42219 (permutation615 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42219step0 raw42219; decide +kernel
      have hl : raw42219step0Labels = raw42219Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42219 raw42219Labels permutation615 permutation4
    mixedMoment B raw42219step0 raw42219step0Labels = mixedMoment B raw42219step1 raw42219step1Labels := by
      have ha : raw42219step1 = raw42219step0 := by apply Matrix.ext; unfold raw42219step1 raw42219step0; decide +kernel
      have hl : raw42219step0Labels = labelEmbedding10 ∘ raw42219step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42219step0 raw42219step0Labels raw42219step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

theorem canonical42220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42220 raw42220Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw42220 raw42220Labels = mixedMoment B raw42220step0 raw42220step0Labels := by
      have ha : raw42220step0 = (fun i j => raw42220 (permutation352 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42220step0 raw42220; decide +kernel
      have hl : raw42220step0Labels = raw42220Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42220 raw42220Labels permutation352 permutation4
    mixedMoment B raw42220step0 raw42220step0Labels = mixedMoment B raw42220step1 raw42220step1Labels := by
      have ha : raw42220step1 = -raw42220step0 := by apply Matrix.ext; change ∀ i j, raw42220step1 i j = -(raw42220step0 i j); unfold raw42220step1 raw42220step0; decide +kernel
      have hl : raw42220step1Labels = raw42220step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42220step1 raw42220step1Labels = mixedMoment B raw42220step2 raw42220step2Labels := by
      have ha : raw42220step2 = raw42220step1 := by apply Matrix.ext; unfold raw42220step2 raw42220step1; decide +kernel
      have hl : raw42220step1Labels = labelEmbedding1 ∘ raw42220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42220step1 raw42220step1Labels raw42220step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical42221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42221 raw42221Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42221 raw42221Labels = mixedMoment B raw42221step0 raw42221step0Labels := by
      have ha : raw42221step0 = (fun i j => raw42221 (permutation389 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42221step0 raw42221; decide +kernel
      have hl : raw42221step0Labels = raw42221Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42221 raw42221Labels permutation389 permutation6
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical42222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42222 raw42222Labels = mixedMoment B node3882 node3882Labels := by
  calc
    mixedMoment B raw42222 raw42222Labels = mixedMoment B raw42222step0 raw42222step0Labels := by
      have ha : raw42222step0 = (fun i j => raw42222 (permutation346 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42222step0 raw42222; decide +kernel
      have hl : raw42222step0Labels = raw42222Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42222 raw42222Labels permutation346 permutation4
    mixedMoment B raw42222step0 raw42222step0Labels = mixedMoment B raw42222step1 raw42222step1Labels := by
      have ha : raw42222step1 = -raw42222step0 := by apply Matrix.ext; change ∀ i j, raw42222step1 i j = -(raw42222step0 i j); unfold raw42222step1 raw42222step0; decide +kernel
      have hl : raw42222step1Labels = raw42222step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42222step1 raw42222step1Labels = mixedMoment B raw42222step2 raw42222step2Labels := by
      have ha : raw42222step2 = raw42222step1 := by apply Matrix.ext; unfold raw42222step2 raw42222step1; decide +kernel
      have hl : raw42222step1Labels = labelEmbedding1 ∘ raw42222step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42222step1 raw42222step1Labels raw42222step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3882 node3882Labels := by rfl

theorem canonical42223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42223 raw42223Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw42223 raw42223Labels = mixedMoment B raw42223step0 raw42223step0Labels := by
      have ha : raw42223step0 = (fun i j => raw42223 (permutation346 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42223step0 raw42223; decide +kernel
      have hl : raw42223step0Labels = raw42223Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42223 raw42223Labels permutation346 permutation4
    mixedMoment B raw42223step0 raw42223step0Labels = mixedMoment B raw42223step1 raw42223step1Labels := by
      have ha : raw42223step1 = -raw42223step0 := by apply Matrix.ext; change ∀ i j, raw42223step1 i j = -(raw42223step0 i j); unfold raw42223step1 raw42223step0; decide +kernel
      have hl : raw42223step1Labels = raw42223step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42223step1 raw42223step1Labels = mixedMoment B raw42223step2 raw42223step2Labels := by
      have ha : raw42223step2 = raw42223step1 := by apply Matrix.ext; unfold raw42223step2 raw42223step1; decide +kernel
      have hl : raw42223step1Labels = labelEmbedding10 ∘ raw42223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42223step1 raw42223step1Labels raw42223step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical42224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42224 raw42224Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw42224 raw42224Labels = mixedMoment B raw42224step0 raw42224step0Labels := by
      have hz : ∀ j, raw42224 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42224step0 = (fun i j => raw42224 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42224step0 raw42224; decide +kernel
      have hl : raw42224step0Labels = raw42224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42224 raw42224Labels permutation520 hz
    mixedMoment B raw42224step0 raw42224step0Labels = mixedMoment B raw42224step1 raw42224step1Labels := by
      have ha : raw42224step1 = (fun i j => raw42224step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42224step1 raw42224step0; decide +kernel
      have hl : raw42224step1Labels = raw42224step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42224step0 raw42224step0Labels permutation145 permutation2
    mixedMoment B raw42224step1 raw42224step1Labels = mixedMoment B raw42224step2 raw42224step2Labels := by
      have ha : raw42224step2 = -raw42224step1 := by apply Matrix.ext; change ∀ i j, raw42224step2 i j = -(raw42224step1 i j); unfold raw42224step2 raw42224step1; decide +kernel
      have hl : raw42224step2Labels = raw42224step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42224step2 raw42224step2Labels = mixedMoment B raw42224step3 raw42224step3Labels := by
      have ha : raw42224step3 = raw42224step2 := by apply Matrix.ext; unfold raw42224step3 raw42224step2; decide +kernel
      have hl : raw42224step2Labels = labelEmbedding1 ∘ raw42224step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42224step2 raw42224step2Labels raw42224step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

theorem canonical42225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42225 raw42225Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw42225 raw42225Labels = mixedMoment B raw42225step0 raw42225step0Labels := by
      have hz : ∀ j, raw42225 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42225step0 = (fun i j => raw42225 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42225step0 raw42225; decide +kernel
      have hl : raw42225step0Labels = raw42225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42225 raw42225Labels permutation520 hz
    mixedMoment B raw42225step0 raw42225step0Labels = mixedMoment B raw42225step1 raw42225step1Labels := by
      have ha : raw42225step1 = (fun i j => raw42225step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42225step1 raw42225step0; decide +kernel
      have hl : raw42225step1Labels = raw42225step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42225step0 raw42225step0Labels permutation145 permutation3
    mixedMoment B raw42225step1 raw42225step1Labels = mixedMoment B raw42225step2 raw42225step2Labels := by
      have ha : raw42225step2 = -raw42225step1 := by apply Matrix.ext; change ∀ i j, raw42225step2 i j = -(raw42225step1 i j); unfold raw42225step2 raw42225step1; decide +kernel
      have hl : raw42225step2Labels = raw42225step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42225step2 raw42225step2Labels = mixedMoment B raw42225step3 raw42225step3Labels := by
      have ha : raw42225step3 = raw42225step2 := by apply Matrix.ext; unfold raw42225step3 raw42225step2; decide +kernel
      have hl : raw42225step2Labels = labelEmbedding7 ∘ raw42225step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42225step2 raw42225step2Labels raw42225step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical42226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42226 raw42226Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw42226 raw42226Labels = mixedMoment B raw42226step0 raw42226step0Labels := by
      have ha : raw42226step0 = (fun i j => raw42226 (permutation617 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42226step0 raw42226; decide +kernel
      have hl : raw42226step0Labels = raw42226Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42226 raw42226Labels permutation617 permutation4
    mixedMoment B raw42226step0 raw42226step0Labels = mixedMoment B raw42226step1 raw42226step1Labels := by
      have ha : raw42226step1 = raw42226step0 := by apply Matrix.ext; unfold raw42226step1 raw42226step0; decide +kernel
      have hl : raw42226step0Labels = labelEmbedding1 ∘ raw42226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42226step0 raw42226step0Labels raw42226step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3085 node3085Labels := by rfl

theorem canonical42227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42227 raw42227Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw42227 raw42227Labels = mixedMoment B raw42227step0 raw42227step0Labels := by
      have ha : raw42227step0 = (fun i j => raw42227 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42227step0 raw42227; decide +kernel
      have hl : raw42227step0Labels = raw42227Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42227 raw42227Labels permutation674 permutation5
    mixedMoment B raw42227step0 raw42227step0Labels = mixedMoment B raw42227step1 raw42227step1Labels := by
      have ha : raw42227step1 = raw42227step0 := by apply Matrix.ext; unfold raw42227step1 raw42227step0; decide +kernel
      have hl : raw42227step0Labels = labelEmbedding9 ∘ raw42227step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42227step0 raw42227step0Labels raw42227step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

theorem canonical42228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42228 raw42228Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw42228 raw42228Labels = mixedMoment B raw42228step0 raw42228step0Labels := by
      have ha : raw42228step0 = raw42228 := by apply Matrix.ext; unfold raw42228step0 raw42228; decide +kernel
      have hl : raw42228Labels = labelEmbedding1 ∘ raw42228step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42228 raw42228Labels raw42228step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3977 node3977Labels := by rfl

theorem canonical42229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42229 raw42229Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw42229 raw42229Labels = mixedMoment B raw42229step0 raw42229step0Labels := by
      have ha : raw42229step0 = (fun i j => raw42229 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42229step0 raw42229; decide +kernel
      have hl : raw42229step0Labels = raw42229Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42229 raw42229Labels permutation682 permutation3
    mixedMoment B raw42229step0 raw42229step0Labels = mixedMoment B raw42229step1 raw42229step1Labels := by
      have ha : raw42229step1 = -raw42229step0 := by apply Matrix.ext; change ∀ i j, raw42229step1 i j = -(raw42229step0 i j); unfold raw42229step1 raw42229step0; decide +kernel
      have hl : raw42229step1Labels = raw42229step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42229step1 raw42229step1Labels = mixedMoment B raw42229step2 raw42229step2Labels := by
      have ha : raw42229step2 = raw42229step1 := by apply Matrix.ext; unfold raw42229step2 raw42229step1; decide +kernel
      have hl : raw42229step1Labels = labelEmbedding7 ∘ raw42229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42229step1 raw42229step1Labels raw42229step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical42230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42230 raw42230Labels = mixedMoment B node3976 node3976Labels := by
  calc
    mixedMoment B raw42230 raw42230Labels = mixedMoment B raw42230step0 raw42230step0Labels := by
      have ha : raw42230step0 = raw42230 := by apply Matrix.ext; unfold raw42230step0 raw42230; decide +kernel
      have hl : raw42230Labels = labelEmbedding1 ∘ raw42230step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42230 raw42230Labels raw42230step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3976 node3976Labels := by rfl

theorem canonical42231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42231 raw42231Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw42231 raw42231Labels = mixedMoment B raw42231step0 raw42231step0Labels := by
      have ha : raw42231step0 = (fun i j => raw42231 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42231step0 raw42231; decide +kernel
      have hl : raw42231step0Labels = raw42231Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42231 raw42231Labels permutation682 permutation3
    mixedMoment B raw42231step0 raw42231step0Labels = mixedMoment B raw42231step1 raw42231step1Labels := by
      have ha : raw42231step1 = -raw42231step0 := by apply Matrix.ext; change ∀ i j, raw42231step1 i j = -(raw42231step0 i j); unfold raw42231step1 raw42231step0; decide +kernel
      have hl : raw42231step1Labels = raw42231step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42231step1 raw42231step1Labels = mixedMoment B raw42231step2 raw42231step2Labels := by
      have ha : raw42231step2 = raw42231step1 := by apply Matrix.ext; unfold raw42231step2 raw42231step1; decide +kernel
      have hl : raw42231step1Labels = labelEmbedding7 ∘ raw42231step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42231step1 raw42231step1Labels raw42231step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5471 node5471Labels := by rfl

theorem canonical42232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42232 raw42232Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw42232 raw42232Labels = mixedMoment B raw42232step0 raw42232step0Labels := by
      have ha : raw42232step0 = (fun i j => raw42232 (permutation538 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42232step0 raw42232; decide +kernel
      have hl : raw42232step0Labels = raw42232Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42232 raw42232Labels permutation538 permutation4
    mixedMoment B raw42232step0 raw42232step0Labels = mixedMoment B raw42232step1 raw42232step1Labels := by
      have ha : raw42232step1 = raw42232step0 := by apply Matrix.ext; unfold raw42232step1 raw42232step0; decide +kernel
      have hl : raw42232step0Labels = labelEmbedding1 ∘ raw42232step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42232step0 raw42232step0Labels raw42232step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2728 node2728Labels := by rfl

theorem canonical42233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42233 raw42233Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw42233 raw42233Labels = mixedMoment B raw42233step0 raw42233step0Labels := by
      have ha : raw42233step0 = (fun i j => raw42233 (permutation538 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42233step0 raw42233; decide +kernel
      have hl : raw42233step0Labels = raw42233Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42233 raw42233Labels permutation538 permutation4
    mixedMoment B raw42233step0 raw42233step0Labels = mixedMoment B raw42233step1 raw42233step1Labels := by
      have ha : raw42233step1 = raw42233step0 := by apply Matrix.ext; unfold raw42233step1 raw42233step0; decide +kernel
      have hl : raw42233step0Labels = labelEmbedding10 ∘ raw42233step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42233step0 raw42233step0Labels raw42233step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

theorem canonical42234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42234 raw42234Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw42234 raw42234Labels = mixedMoment B raw42234step0 raw42234step0Labels := by
      have hz : ∀ j, raw42234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42234step0 = (fun i j => raw42234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42234step0 raw42234; decide +kernel
      have hl : raw42234step0Labels = raw42234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42234 raw42234Labels permutation434 hz
    mixedMoment B raw42234step0 raw42234step0Labels = mixedMoment B raw42234step1 raw42234step1Labels := by
      have ha : raw42234step1 = (fun i j => raw42234step0 (permutation134 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42234step1 raw42234step0; decide +kernel
      have hl : raw42234step1Labels = raw42234step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42234step0 raw42234step0Labels permutation134 permutation4
    mixedMoment B raw42234step1 raw42234step1Labels = mixedMoment B raw42234step2 raw42234step2Labels := by
      have ha : raw42234step2 = raw42234step1 := by apply Matrix.ext; unfold raw42234step2 raw42234step1; decide +kernel
      have hl : raw42234step1Labels = labelEmbedding1 ∘ raw42234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42234step1 raw42234step1Labels raw42234step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3097 node3097Labels := by rfl

theorem canonical42235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42235 raw42235Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw42235 raw42235Labels = mixedMoment B raw42235step0 raw42235step0Labels := by
      have hz : ∀ j, raw42235 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42235step0 = (fun i j => raw42235 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42235step0 raw42235; decide +kernel
      have hl : raw42235step0Labels = raw42235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42235 raw42235Labels permutation434 hz
    mixedMoment B raw42235step0 raw42235step0Labels = mixedMoment B raw42235step1 raw42235step1Labels := by
      have ha : raw42235step1 = (fun i j => raw42235step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42235step1 raw42235step0; decide +kernel
      have hl : raw42235step1Labels = raw42235step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42235step0 raw42235step0Labels permutation139 permutation5
    mixedMoment B raw42235step1 raw42235step1Labels = mixedMoment B raw42235step2 raw42235step2Labels := by
      have ha : raw42235step2 = raw42235step1 := by apply Matrix.ext; unfold raw42235step2 raw42235step1; decide +kernel
      have hl : raw42235step1Labels = labelEmbedding9 ∘ raw42235step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42235step1 raw42235step1Labels raw42235step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical42236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42236 raw42236Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw42236 raw42236Labels = mixedMoment B raw42236step0 raw42236step0Labels := by
      have hz : ∀ j, raw42236 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42236step0 = (fun i j => raw42236 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42236step0 raw42236; decide +kernel
      have hl : raw42236step0Labels = raw42236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42236 raw42236Labels permutation434 hz
    mixedMoment B raw42236step0 raw42236step0Labels = mixedMoment B raw42236step1 raw42236step1Labels := by
      have ha : raw42236step1 = (fun i j => raw42236step0 (permutation110 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42236step1 raw42236step0; decide +kernel
      have hl : raw42236step1Labels = raw42236step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42236step0 raw42236step0Labels permutation110 permutation4
    mixedMoment B raw42236step1 raw42236step1Labels = mixedMoment B raw42236step2 raw42236step2Labels := by
      have ha : raw42236step2 = raw42236step1 := by apply Matrix.ext; unfold raw42236step2 raw42236step1; decide +kernel
      have hl : raw42236step1Labels = labelEmbedding1 ∘ raw42236step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42236step1 raw42236step1Labels raw42236step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

theorem canonical42237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42237 raw42237Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw42237 raw42237Labels = mixedMoment B raw42237step0 raw42237step0Labels := by
      have hz : ∀ j, raw42237 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42237step0 = (fun i j => raw42237 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42237step0 raw42237; decide +kernel
      have hl : raw42237step0Labels = raw42237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42237 raw42237Labels permutation434 hz
    mixedMoment B raw42237step0 raw42237step0Labels = mixedMoment B raw42237step1 raw42237step1Labels := by
      have ha : raw42237step1 = (fun i j => raw42237step0 (permutation142 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42237step1 raw42237step0; decide +kernel
      have hl : raw42237step1Labels = raw42237step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42237step0 raw42237step0Labels permutation142 permutation7
    mixedMoment B raw42237step1 raw42237step1Labels = mixedMoment B raw42237step2 raw42237step2Labels := by
      have ha : raw42237step2 = raw42237step1 := by apply Matrix.ext; unfold raw42237step2 raw42237step1; decide +kernel
      have hl : raw42237step1Labels = labelEmbedding6 ∘ raw42237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42237step1 raw42237step1Labels raw42237step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

theorem canonical42238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42238 raw42238Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw42238 raw42238Labels = mixedMoment B raw42238step0 raw42238step0Labels := by
      have ha : raw42238step0 = (fun i j => raw42238 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42238step0 raw42238; decide +kernel
      have hl : raw42238step0Labels = raw42238Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42238 raw42238Labels permutation158 permutation2
    mixedMoment B raw42238step0 raw42238step0Labels = mixedMoment B raw42238step1 raw42238step1Labels := by
      have ha : raw42238step1 = raw42238step0 := by apply Matrix.ext; unfold raw42238step1 raw42238step0; decide +kernel
      have hl : raw42238step0Labels = labelEmbedding1 ∘ raw42238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42238step0 raw42238step0Labels raw42238step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3972 node3972Labels := by rfl

theorem canonical42239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42239 raw42239Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42239 raw42239Labels = mixedMoment B raw42239step0 raw42239step0Labels := by
      have ha : raw42239step0 = (fun i j => raw42239 (permutation654 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42239step0 raw42239; decide +kernel
      have hl : raw42239step0Labels = raw42239Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42239 raw42239Labels permutation654 permutation5
    mixedMoment B raw42239step0 raw42239step0Labels = mixedMoment B raw42239step1 raw42239step1Labels := by
      have ha : raw42239step1 = raw42239step0 := by apply Matrix.ext; unfold raw42239step1 raw42239step0; decide +kernel
      have hl : raw42239step0Labels = labelEmbedding9 ∘ raw42239step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42239step0 raw42239step0Labels raw42239step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2432) =
      Integer.Sparse.eval keyMomentRow2432 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2432).leftCharge (GramAssembly.key 2432).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3840) := by
    have ha : gramCharges (GramAssembly.key 2432).leftCharge (GramAssembly.key 2432).rightCharge = raw42176 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42176Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42176 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2432).leftCharge (GramAssembly.key 2432).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2432).leftCharge (GramAssembly.key 2432).rightCharge = raw42177 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42177Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42177 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2432).leftCharge (GramAssembly.key 2432).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2432).leftCharge (GramAssembly.key 2432).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2432, Integer.Sparse.eval]
  ring

theorem keyMoment2433 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2433) =
      Integer.Sparse.eval keyMomentRow2433 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2433).leftCharge (GramAssembly.key 2433).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2750) := by
    have ha : gramCharges (GramAssembly.key 2433).leftCharge (GramAssembly.key 2433).rightCharge = raw42178 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42178Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42178 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2433).leftCharge (GramAssembly.key 2433).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5281) := by
    have ha : gramCharges (GramAssembly.key 2433).leftCharge (GramAssembly.key 2433).rightCharge = raw42179 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42179Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42179 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2433).leftCharge (GramAssembly.key 2433).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2433).leftCharge (GramAssembly.key 2433).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2433, Integer.Sparse.eval]
  ring

theorem keyMoment2434 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2434) =
      Integer.Sparse.eval keyMomentRow2434 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2434).leftCharge (GramAssembly.key 2434).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3994) := by
    have ha : gramCharges (GramAssembly.key 2434).leftCharge (GramAssembly.key 2434).rightCharge = raw42180 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42180Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42180 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2434).leftCharge (GramAssembly.key 2434).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5478) := by
    have ha : gramCharges (GramAssembly.key 2434).leftCharge (GramAssembly.key 2434).rightCharge = raw42181 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42181Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42181 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2434).leftCharge (GramAssembly.key 2434).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2434).leftCharge (GramAssembly.key 2434).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2434, Integer.Sparse.eval]
  ring

theorem keyMoment2435 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2435) =
      Integer.Sparse.eval keyMomentRow2435 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2435).leftCharge (GramAssembly.key 2435).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3119) := by
    have ha : gramCharges (GramAssembly.key 2435).leftCharge (GramAssembly.key 2435).rightCharge = raw42182 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42182Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42182 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2435).leftCharge (GramAssembly.key 2435).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5304) := by
    have ha : gramCharges (GramAssembly.key 2435).leftCharge (GramAssembly.key 2435).rightCharge = raw42183 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42183Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42183 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2435).leftCharge (GramAssembly.key 2435).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2435).leftCharge (GramAssembly.key 2435).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2435, Integer.Sparse.eval]
  ring

theorem keyMoment2436 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2436) =
      Integer.Sparse.eval keyMomentRow2436 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2436).leftCharge (GramAssembly.key 2436).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2781) := by
    have ha : gramCharges (GramAssembly.key 2436).leftCharge (GramAssembly.key 2436).rightCharge = raw42184 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42184Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42184 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2436).leftCharge (GramAssembly.key 2436).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5295) := by
    have ha : gramCharges (GramAssembly.key 2436).leftCharge (GramAssembly.key 2436).rightCharge = raw42185 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42185Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42185 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2436).leftCharge (GramAssembly.key 2436).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2436).leftCharge (GramAssembly.key 2436).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2436, Integer.Sparse.eval]
  ring

theorem keyMoment2437 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2437) =
      Integer.Sparse.eval keyMomentRow2437 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2437).leftCharge (GramAssembly.key 2437).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3993) := by
    have ha : gramCharges (GramAssembly.key 2437).leftCharge (GramAssembly.key 2437).rightCharge = raw42186 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42186Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42186 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2437).leftCharge (GramAssembly.key 2437).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5438) := by
    have ha : gramCharges (GramAssembly.key 2437).leftCharge (GramAssembly.key 2437).rightCharge = raw42187 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42187Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42187 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2437).leftCharge (GramAssembly.key 2437).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2437).leftCharge (GramAssembly.key 2437).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2437, Integer.Sparse.eval]
  ring

theorem keyMoment2438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2438) =
      Integer.Sparse.eval keyMomentRow2438 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2438).leftCharge (GramAssembly.key 2438).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3572) := by
    have ha : gramCharges (GramAssembly.key 2438).leftCharge (GramAssembly.key 2438).rightCharge = raw42188 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42188Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42188 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2438).leftCharge (GramAssembly.key 2438).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5289) := by
    have ha : gramCharges (GramAssembly.key 2438).leftCharge (GramAssembly.key 2438).rightCharge = raw42189 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42189Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42189 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2438).leftCharge (GramAssembly.key 2438).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2438).leftCharge (GramAssembly.key 2438).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2438, Integer.Sparse.eval]
  ring

theorem keyMoment2439 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2439) =
      Integer.Sparse.eval keyMomentRow2439 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2439).leftCharge (GramAssembly.key 2439).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3540) := by
    have ha : gramCharges (GramAssembly.key 2439).leftCharge (GramAssembly.key 2439).rightCharge = raw42190 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42190Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42190 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2439).leftCharge (GramAssembly.key 2439).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2439).leftCharge (GramAssembly.key 2439).rightCharge = raw42191 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42191Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42191 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2439).leftCharge (GramAssembly.key 2439).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2439).leftCharge (GramAssembly.key 2439).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2439, Integer.Sparse.eval]
  ring

theorem keyMoment2440 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2440) =
      Integer.Sparse.eval keyMomentRow2440 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2440).leftCharge (GramAssembly.key 2440).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2763) := by
    have ha : gramCharges (GramAssembly.key 2440).leftCharge (GramAssembly.key 2440).rightCharge = raw42192 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42192Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42192 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2440).leftCharge (GramAssembly.key 2440).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5289) := by
    have ha : gramCharges (GramAssembly.key 2440).leftCharge (GramAssembly.key 2440).rightCharge = raw42193 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42193Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42193 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2440).leftCharge (GramAssembly.key 2440).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2440).leftCharge (GramAssembly.key 2440).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2440, Integer.Sparse.eval]
  ring

theorem keyMoment2441 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2441) =
      Integer.Sparse.eval keyMomentRow2441 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2441).leftCharge (GramAssembly.key 2441).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3997) := by
    have ha : gramCharges (GramAssembly.key 2441).leftCharge (GramAssembly.key 2441).rightCharge = raw42194 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42194Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42194 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2441).leftCharge (GramAssembly.key 2441).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5484) := by
    have ha : gramCharges (GramAssembly.key 2441).leftCharge (GramAssembly.key 2441).rightCharge = raw42195 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42195Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42195 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2441).leftCharge (GramAssembly.key 2441).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2441).leftCharge (GramAssembly.key 2441).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2441, Integer.Sparse.eval]
  ring

theorem keyMoment2442 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2442) =
      Integer.Sparse.eval keyMomentRow2442 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2442).leftCharge (GramAssembly.key 2442).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3978) := by
    have ha : gramCharges (GramAssembly.key 2442).leftCharge (GramAssembly.key 2442).rightCharge = raw42196 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42196Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42196 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2442).leftCharge (GramAssembly.key 2442).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5480) := by
    have ha : gramCharges (GramAssembly.key 2442).leftCharge (GramAssembly.key 2442).rightCharge = raw42197 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42197Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42197 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2442).leftCharge (GramAssembly.key 2442).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2442).leftCharge (GramAssembly.key 2442).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2442, Integer.Sparse.eval]
  ring

theorem keyMoment2443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2443) =
      Integer.Sparse.eval keyMomentRow2443 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2443).leftCharge (GramAssembly.key 2443).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3848) := by
    have ha : gramCharges (GramAssembly.key 2443).leftCharge (GramAssembly.key 2443).rightCharge = raw42198 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42198Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42198 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2443).leftCharge (GramAssembly.key 2443).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2443).leftCharge (GramAssembly.key 2443).rightCharge = raw42199 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42199Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42199 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2443).leftCharge (GramAssembly.key 2443).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2443).leftCharge (GramAssembly.key 2443).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2443, Integer.Sparse.eval]
  ring

theorem keyMoment2444 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2444) =
      Integer.Sparse.eval keyMomentRow2444 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2444).leftCharge (GramAssembly.key 2444).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3225) := by
    have ha : gramCharges (GramAssembly.key 2444).leftCharge (GramAssembly.key 2444).rightCharge = raw42200 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42200Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42200 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2444).leftCharge (GramAssembly.key 2444).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4896) := by
    have ha : gramCharges (GramAssembly.key 2444).leftCharge (GramAssembly.key 2444).rightCharge = raw42201 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42201Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42201 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2444).leftCharge (GramAssembly.key 2444).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2444).leftCharge (GramAssembly.key 2444).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2444, Integer.Sparse.eval]
  ring

theorem keyMoment2445 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2445) =
      Integer.Sparse.eval keyMomentRow2445 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2445).leftCharge (GramAssembly.key 2445).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3086) := by
    have ha : gramCharges (GramAssembly.key 2445).leftCharge (GramAssembly.key 2445).rightCharge = raw42202 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42202Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42202 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2445).leftCharge (GramAssembly.key 2445).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2445).leftCharge (GramAssembly.key 2445).rightCharge = raw42203 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42203Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42203 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2445).leftCharge (GramAssembly.key 2445).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2445).leftCharge (GramAssembly.key 2445).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2445, Integer.Sparse.eval]
  ring

theorem keyMoment2446 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2446) =
      Integer.Sparse.eval keyMomentRow2446 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2446).leftCharge (GramAssembly.key 2446).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3883) := by
    have ha : gramCharges (GramAssembly.key 2446).leftCharge (GramAssembly.key 2446).rightCharge = raw42204 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42204Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42204 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2446).leftCharge (GramAssembly.key 2446).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5411) := by
    have ha : gramCharges (GramAssembly.key 2446).leftCharge (GramAssembly.key 2446).rightCharge = raw42205 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42205Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42205 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2446).leftCharge (GramAssembly.key 2446).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2446).leftCharge (GramAssembly.key 2446).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2446, Integer.Sparse.eval]
  ring

theorem keyMoment2447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2447) =
      Integer.Sparse.eval keyMomentRow2447 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2447).leftCharge (GramAssembly.key 2447).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3881) := by
    have ha : gramCharges (GramAssembly.key 2447).leftCharge (GramAssembly.key 2447).rightCharge = raw42206 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42206Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42206 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2447).leftCharge (GramAssembly.key 2447).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5446) := by
    have ha : gramCharges (GramAssembly.key 2447).leftCharge (GramAssembly.key 2447).rightCharge = raw42207 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42207Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42207 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2447).leftCharge (GramAssembly.key 2447).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2447).leftCharge (GramAssembly.key 2447).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2447, Integer.Sparse.eval]
  ring

theorem keyMoment2448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2448) =
      Integer.Sparse.eval keyMomentRow2448 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2448).leftCharge (GramAssembly.key 2448).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2729) := by
    have ha : gramCharges (GramAssembly.key 2448).leftCharge (GramAssembly.key 2448).rightCharge = raw42208 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42208Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42208 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2448).leftCharge (GramAssembly.key 2448).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5264) := by
    have ha : gramCharges (GramAssembly.key 2448).leftCharge (GramAssembly.key 2448).rightCharge = raw42209 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42209Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42209 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2448).leftCharge (GramAssembly.key 2448).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2448).leftCharge (GramAssembly.key 2448).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2448, Integer.Sparse.eval]
  ring

theorem keyMoment2449 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2449) =
      Integer.Sparse.eval keyMomentRow2449 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2449).leftCharge (GramAssembly.key 2449).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3872) := by
    have ha : gramCharges (GramAssembly.key 2449).leftCharge (GramAssembly.key 2449).rightCharge = raw42210 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42210Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42210 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2449).leftCharge (GramAssembly.key 2449).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2449).leftCharge (GramAssembly.key 2449).rightCharge = raw42211 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42211Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42211 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2449).leftCharge (GramAssembly.key 2449).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2449).leftCharge (GramAssembly.key 2449).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2449, Integer.Sparse.eval]
  ring

theorem keyMoment2450 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2450) =
      Integer.Sparse.eval keyMomentRow2450 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2450).leftCharge (GramAssembly.key 2450).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3880) := by
    have ha : gramCharges (GramAssembly.key 2450).leftCharge (GramAssembly.key 2450).rightCharge = raw42212 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42212Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42212 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2450).leftCharge (GramAssembly.key 2450).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5445) := by
    have ha : gramCharges (GramAssembly.key 2450).leftCharge (GramAssembly.key 2450).rightCharge = raw42213 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42213Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42213 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2450).leftCharge (GramAssembly.key 2450).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2450).leftCharge (GramAssembly.key 2450).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2450, Integer.Sparse.eval]
  ring

theorem keyMoment2451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2451) =
      Integer.Sparse.eval keyMomentRow2451 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2451).leftCharge (GramAssembly.key 2451).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3866) := by
    have ha : gramCharges (GramAssembly.key 2451).leftCharge (GramAssembly.key 2451).rightCharge = raw42214 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42214Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42214 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2451).leftCharge (GramAssembly.key 2451).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5382) := by
    have ha : gramCharges (GramAssembly.key 2451).leftCharge (GramAssembly.key 2451).rightCharge = raw42215 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42215Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42215 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2451).leftCharge (GramAssembly.key 2451).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2451).leftCharge (GramAssembly.key 2451).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2451, Integer.Sparse.eval]
  ring

theorem keyMoment2452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2452) =
      Integer.Sparse.eval keyMomentRow2452 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2452).leftCharge (GramAssembly.key 2452).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3834) := by
    have ha : gramCharges (GramAssembly.key 2452).leftCharge (GramAssembly.key 2452).rightCharge = raw42216 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42216Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42216 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2452).leftCharge (GramAssembly.key 2452).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5381) := by
    have ha : gramCharges (GramAssembly.key 2452).leftCharge (GramAssembly.key 2452).rightCharge = raw42217 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42217Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42217 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2452).leftCharge (GramAssembly.key 2452).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2452).leftCharge (GramAssembly.key 2452).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2452, Integer.Sparse.eval]
  ring

theorem keyMoment2453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2453) =
      Integer.Sparse.eval keyMomentRow2453 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2453).leftCharge (GramAssembly.key 2453).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2708) := by
    have ha : gramCharges (GramAssembly.key 2453).leftCharge (GramAssembly.key 2453).rightCharge = raw42218 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42218Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42218 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2453).leftCharge (GramAssembly.key 2453).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5249) := by
    have ha : gramCharges (GramAssembly.key 2453).leftCharge (GramAssembly.key 2453).rightCharge = raw42219 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42219Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42219 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2453).leftCharge (GramAssembly.key 2453).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2453).leftCharge (GramAssembly.key 2453).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2453, Integer.Sparse.eval]
  ring

theorem keyMoment2454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2454) =
      Integer.Sparse.eval keyMomentRow2454 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2454).leftCharge (GramAssembly.key 2454).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3871) := by
    have ha : gramCharges (GramAssembly.key 2454).leftCharge (GramAssembly.key 2454).rightCharge = raw42220 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42220Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42220 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2454).leftCharge (GramAssembly.key 2454).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2454).leftCharge (GramAssembly.key 2454).rightCharge = raw42221 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42221Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42221 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2454).leftCharge (GramAssembly.key 2454).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2454).leftCharge (GramAssembly.key 2454).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2454, Integer.Sparse.eval]
  ring

theorem keyMoment2455 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2455) =
      Integer.Sparse.eval keyMomentRow2455 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2455).leftCharge (GramAssembly.key 2455).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3882) := by
    have ha : gramCharges (GramAssembly.key 2455).leftCharge (GramAssembly.key 2455).rightCharge = raw42222 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42222Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42222 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2455).leftCharge (GramAssembly.key 2455).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5447) := by
    have ha : gramCharges (GramAssembly.key 2455).leftCharge (GramAssembly.key 2455).rightCharge = raw42223 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42223Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42223 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2455).leftCharge (GramAssembly.key 2455).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2455).leftCharge (GramAssembly.key 2455).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2455, Integer.Sparse.eval]
  ring

theorem keyMoment2456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2456) =
      Integer.Sparse.eval keyMomentRow2456 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2456).leftCharge (GramAssembly.key 2456).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3227) := by
    have ha : gramCharges (GramAssembly.key 2456).leftCharge (GramAssembly.key 2456).rightCharge = raw42224 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42224Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42224 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2456).leftCharge (GramAssembly.key 2456).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4888) := by
    have ha : gramCharges (GramAssembly.key 2456).leftCharge (GramAssembly.key 2456).rightCharge = raw42225 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42225Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42225 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2456).leftCharge (GramAssembly.key 2456).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2456).leftCharge (GramAssembly.key 2456).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2456, Integer.Sparse.eval]
  ring

theorem keyMoment2457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2457) =
      Integer.Sparse.eval keyMomentRow2457 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2457).leftCharge (GramAssembly.key 2457).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3085) := by
    have ha : gramCharges (GramAssembly.key 2457).leftCharge (GramAssembly.key 2457).rightCharge = raw42226 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42226Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42226 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2457).leftCharge (GramAssembly.key 2457).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5256) := by
    have ha : gramCharges (GramAssembly.key 2457).leftCharge (GramAssembly.key 2457).rightCharge = raw42227 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42227Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42227 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2457).leftCharge (GramAssembly.key 2457).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2457).leftCharge (GramAssembly.key 2457).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2457, Integer.Sparse.eval]
  ring

theorem keyMoment2458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2458) =
      Integer.Sparse.eval keyMomentRow2458 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2458).leftCharge (GramAssembly.key 2458).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3977) := by
    have ha : gramCharges (GramAssembly.key 2458).leftCharge (GramAssembly.key 2458).rightCharge = raw42228 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42228Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42228 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2458).leftCharge (GramAssembly.key 2458).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5405) := by
    have ha : gramCharges (GramAssembly.key 2458).leftCharge (GramAssembly.key 2458).rightCharge = raw42229 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42229Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42229 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2458).leftCharge (GramAssembly.key 2458).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2458).leftCharge (GramAssembly.key 2458).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2458, Integer.Sparse.eval]
  ring

theorem keyMoment2459 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2459) =
      Integer.Sparse.eval keyMomentRow2459 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2459).leftCharge (GramAssembly.key 2459).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3976) := by
    have ha : gramCharges (GramAssembly.key 2459).leftCharge (GramAssembly.key 2459).rightCharge = raw42230 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42230Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42230 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2459).leftCharge (GramAssembly.key 2459).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5471) := by
    have ha : gramCharges (GramAssembly.key 2459).leftCharge (GramAssembly.key 2459).rightCharge = raw42231 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42231Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42231 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2459).leftCharge (GramAssembly.key 2459).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2459).leftCharge (GramAssembly.key 2459).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2459, Integer.Sparse.eval]
  ring

theorem keyMoment2460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2460) =
      Integer.Sparse.eval keyMomentRow2460 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2460).leftCharge (GramAssembly.key 2460).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2728) := by
    have ha : gramCharges (GramAssembly.key 2460).leftCharge (GramAssembly.key 2460).rightCharge = raw42232 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42232Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42232 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2460).leftCharge (GramAssembly.key 2460).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5263) := by
    have ha : gramCharges (GramAssembly.key 2460).leftCharge (GramAssembly.key 2460).rightCharge = raw42233 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42233Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42233 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2460).leftCharge (GramAssembly.key 2460).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2460).leftCharge (GramAssembly.key 2460).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2460, Integer.Sparse.eval]
  ring

theorem keyMoment2461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2461) =
      Integer.Sparse.eval keyMomentRow2461 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2461).leftCharge (GramAssembly.key 2461).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3097) := by
    have ha : gramCharges (GramAssembly.key 2461).leftCharge (GramAssembly.key 2461).rightCharge = raw42234 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42234Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42234 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2461).leftCharge (GramAssembly.key 2461).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5289) := by
    have ha : gramCharges (GramAssembly.key 2461).leftCharge (GramAssembly.key 2461).rightCharge = raw42235 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42235Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42235 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2461).leftCharge (GramAssembly.key 2461).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2461).leftCharge (GramAssembly.key 2461).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2461, Integer.Sparse.eval]
  ring

theorem keyMoment2462 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2462) =
      Integer.Sparse.eval keyMomentRow2462 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2462).leftCharge (GramAssembly.key 2462).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2735) := by
    have ha : gramCharges (GramAssembly.key 2462).leftCharge (GramAssembly.key 2462).rightCharge = raw42236 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42236Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42236 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2462).leftCharge (GramAssembly.key 2462).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5173) := by
    have ha : gramCharges (GramAssembly.key 2462).leftCharge (GramAssembly.key 2462).rightCharge = raw42237 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42237Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42237 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2462).leftCharge (GramAssembly.key 2462).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2462).leftCharge (GramAssembly.key 2462).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2462, Integer.Sparse.eval]
  ring

theorem keyMoment2463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2463) =
      Integer.Sparse.eval keyMomentRow2463 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2463).leftCharge (GramAssembly.key 2463).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3972) := by
    have ha : gramCharges (GramAssembly.key 2463).leftCharge (GramAssembly.key 2463).rightCharge = raw42238 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42238Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42238 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2463).leftCharge (GramAssembly.key 2463).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2463).leftCharge (GramAssembly.key 2463).rightCharge = raw42239 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42239Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42239 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2463).leftCharge (GramAssembly.key 2463).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2463).leftCharge (GramAssembly.key 2463).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2463, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2432 : keyMomentRows (2432 : Fin 2886) =
    keyMomentRow2432 := by decide +kernel

theorem keyMomentRowsAt2433 : keyMomentRows (2433 : Fin 2886) =
    keyMomentRow2433 := by decide +kernel

theorem keyMomentRowsAt2434 : keyMomentRows (2434 : Fin 2886) =
    keyMomentRow2434 := by decide +kernel

theorem keyMomentRowsAt2435 : keyMomentRows (2435 : Fin 2886) =
    keyMomentRow2435 := by decide +kernel

theorem keyMomentRowsAt2436 : keyMomentRows (2436 : Fin 2886) =
    keyMomentRow2436 := by decide +kernel

theorem keyMomentRowsAt2437 : keyMomentRows (2437 : Fin 2886) =
    keyMomentRow2437 := by decide +kernel

theorem keyMomentRowsAt2438 : keyMomentRows (2438 : Fin 2886) =
    keyMomentRow2438 := by decide +kernel

theorem keyMomentRowsAt2439 : keyMomentRows (2439 : Fin 2886) =
    keyMomentRow2439 := by decide +kernel

theorem keyMomentRowsAt2440 : keyMomentRows (2440 : Fin 2886) =
    keyMomentRow2440 := by decide +kernel

theorem keyMomentRowsAt2441 : keyMomentRows (2441 : Fin 2886) =
    keyMomentRow2441 := by decide +kernel

theorem keyMomentRowsAt2442 : keyMomentRows (2442 : Fin 2886) =
    keyMomentRow2442 := by decide +kernel

theorem keyMomentRowsAt2443 : keyMomentRows (2443 : Fin 2886) =
    keyMomentRow2443 := by decide +kernel

theorem keyMomentRowsAt2444 : keyMomentRows (2444 : Fin 2886) =
    keyMomentRow2444 := by decide +kernel

theorem keyMomentRowsAt2445 : keyMomentRows (2445 : Fin 2886) =
    keyMomentRow2445 := by decide +kernel

theorem keyMomentRowsAt2446 : keyMomentRows (2446 : Fin 2886) =
    keyMomentRow2446 := by decide +kernel

theorem keyMomentRowsAt2447 : keyMomentRows (2447 : Fin 2886) =
    keyMomentRow2447 := by decide +kernel

theorem keyMomentRowsAt2448 : keyMomentRows (2448 : Fin 2886) =
    keyMomentRow2448 := by decide +kernel

theorem keyMomentRowsAt2449 : keyMomentRows (2449 : Fin 2886) =
    keyMomentRow2449 := by decide +kernel

theorem keyMomentRowsAt2450 : keyMomentRows (2450 : Fin 2886) =
    keyMomentRow2450 := by decide +kernel

theorem keyMomentRowsAt2451 : keyMomentRows (2451 : Fin 2886) =
    keyMomentRow2451 := by decide +kernel

theorem keyMomentRowsAt2452 : keyMomentRows (2452 : Fin 2886) =
    keyMomentRow2452 := by decide +kernel

theorem keyMomentRowsAt2453 : keyMomentRows (2453 : Fin 2886) =
    keyMomentRow2453 := by decide +kernel

theorem keyMomentRowsAt2454 : keyMomentRows (2454 : Fin 2886) =
    keyMomentRow2454 := by decide +kernel

theorem keyMomentRowsAt2455 : keyMomentRows (2455 : Fin 2886) =
    keyMomentRow2455 := by decide +kernel

theorem keyMomentRowsAt2456 : keyMomentRows (2456 : Fin 2886) =
    keyMomentRow2456 := by decide +kernel

theorem keyMomentRowsAt2457 : keyMomentRows (2457 : Fin 2886) =
    keyMomentRow2457 := by decide +kernel

theorem keyMomentRowsAt2458 : keyMomentRows (2458 : Fin 2886) =
    keyMomentRow2458 := by decide +kernel

theorem keyMomentRowsAt2459 : keyMomentRows (2459 : Fin 2886) =
    keyMomentRow2459 := by decide +kernel

theorem keyMomentRowsAt2460 : keyMomentRows (2460 : Fin 2886) =
    keyMomentRow2460 := by decide +kernel

theorem keyMomentRowsAt2461 : keyMomentRows (2461 : Fin 2886) =
    keyMomentRow2461 := by decide +kernel

theorem keyMomentRowsAt2462 : keyMomentRows (2462 : Fin 2886) =
    keyMomentRow2462 := by decide +kernel

theorem keyMomentRowsAt2463 : keyMomentRows (2463 : Fin 2886) =
    keyMomentRow2463 := by decide +kernel

theorem keyMomentChunkSound76_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 76) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2432 ∨ k.val = 2433 ∨ k.val = 2434 ∨ k.val = 2435 ∨ k.val = 2436 ∨ k.val = 2437 ∨ k.val = 2438 ∨ k.val = 2439 ∨ k.val = 2440 ∨ k.val = 2441 ∨ k.val = 2442 ∨ k.val = 2443 ∨ k.val = 2444 ∨ k.val = 2445 ∨ k.val = 2446 ∨ k.val = 2447 ∨ k.val = 2448 ∨ k.val = 2449 ∨ k.val = 2450 ∨ k.val = 2451 ∨ k.val = 2452 ∨ k.val = 2453 ∨ k.val = 2454 ∨ k.val = 2455 ∨ k.val = 2456 ∨ k.val = 2457 ∨ k.val = 2458 ∨ k.val = 2459 ∨ k.val = 2460 ∨ k.val = 2461 ∨ k.val = 2462 ∨ k.val = 2463 := by omega
  rcases heq with h2432 | h2433 | h2434 | h2435 | h2436 | h2437 | h2438 | h2439 | h2440 | h2441 | h2442 | h2443 | h2444 | h2445 | h2446 | h2447 | h2448 | h2449 | h2450 | h2451 | h2452 | h2453 | h2454 | h2455 | h2456 | h2457 | h2458 | h2459 | h2460 | h2461 | h2462 | h2463
  · have he : k = (2432 : Fin 2886) := Fin.ext h2432
    subst k
    rw [keyMomentRowsAt2432]
    exact keyMoment2432 B hB
  · have he : k = (2433 : Fin 2886) := Fin.ext h2433
    subst k
    rw [keyMomentRowsAt2433]
    exact keyMoment2433 B hB
  · have he : k = (2434 : Fin 2886) := Fin.ext h2434
    subst k
    rw [keyMomentRowsAt2434]
    exact keyMoment2434 B hB
  · have he : k = (2435 : Fin 2886) := Fin.ext h2435
    subst k
    rw [keyMomentRowsAt2435]
    exact keyMoment2435 B hB
  · have he : k = (2436 : Fin 2886) := Fin.ext h2436
    subst k
    rw [keyMomentRowsAt2436]
    exact keyMoment2436 B hB
  · have he : k = (2437 : Fin 2886) := Fin.ext h2437
    subst k
    rw [keyMomentRowsAt2437]
    exact keyMoment2437 B hB
  · have he : k = (2438 : Fin 2886) := Fin.ext h2438
    subst k
    rw [keyMomentRowsAt2438]
    exact keyMoment2438 B hB
  · have he : k = (2439 : Fin 2886) := Fin.ext h2439
    subst k
    rw [keyMomentRowsAt2439]
    exact keyMoment2439 B hB
  · have he : k = (2440 : Fin 2886) := Fin.ext h2440
    subst k
    rw [keyMomentRowsAt2440]
    exact keyMoment2440 B hB
  · have he : k = (2441 : Fin 2886) := Fin.ext h2441
    subst k
    rw [keyMomentRowsAt2441]
    exact keyMoment2441 B hB
  · have he : k = (2442 : Fin 2886) := Fin.ext h2442
    subst k
    rw [keyMomentRowsAt2442]
    exact keyMoment2442 B hB
  · have he : k = (2443 : Fin 2886) := Fin.ext h2443
    subst k
    rw [keyMomentRowsAt2443]
    exact keyMoment2443 B hB
  · have he : k = (2444 : Fin 2886) := Fin.ext h2444
    subst k
    rw [keyMomentRowsAt2444]
    exact keyMoment2444 B hB
  · have he : k = (2445 : Fin 2886) := Fin.ext h2445
    subst k
    rw [keyMomentRowsAt2445]
    exact keyMoment2445 B hB
  · have he : k = (2446 : Fin 2886) := Fin.ext h2446
    subst k
    rw [keyMomentRowsAt2446]
    exact keyMoment2446 B hB
  · have he : k = (2447 : Fin 2886) := Fin.ext h2447
    subst k
    rw [keyMomentRowsAt2447]
    exact keyMoment2447 B hB
  · have he : k = (2448 : Fin 2886) := Fin.ext h2448
    subst k
    rw [keyMomentRowsAt2448]
    exact keyMoment2448 B hB
  · have he : k = (2449 : Fin 2886) := Fin.ext h2449
    subst k
    rw [keyMomentRowsAt2449]
    exact keyMoment2449 B hB
  · have he : k = (2450 : Fin 2886) := Fin.ext h2450
    subst k
    rw [keyMomentRowsAt2450]
    exact keyMoment2450 B hB
  · have he : k = (2451 : Fin 2886) := Fin.ext h2451
    subst k
    rw [keyMomentRowsAt2451]
    exact keyMoment2451 B hB
  · have he : k = (2452 : Fin 2886) := Fin.ext h2452
    subst k
    rw [keyMomentRowsAt2452]
    exact keyMoment2452 B hB
  · have he : k = (2453 : Fin 2886) := Fin.ext h2453
    subst k
    rw [keyMomentRowsAt2453]
    exact keyMoment2453 B hB
  · have he : k = (2454 : Fin 2886) := Fin.ext h2454
    subst k
    rw [keyMomentRowsAt2454]
    exact keyMoment2454 B hB
  · have he : k = (2455 : Fin 2886) := Fin.ext h2455
    subst k
    rw [keyMomentRowsAt2455]
    exact keyMoment2455 B hB
  · have he : k = (2456 : Fin 2886) := Fin.ext h2456
    subst k
    rw [keyMomentRowsAt2456]
    exact keyMoment2456 B hB
  · have he : k = (2457 : Fin 2886) := Fin.ext h2457
    subst k
    rw [keyMomentRowsAt2457]
    exact keyMoment2457 B hB
  · have he : k = (2458 : Fin 2886) := Fin.ext h2458
    subst k
    rw [keyMomentRowsAt2458]
    exact keyMoment2458 B hB
  · have he : k = (2459 : Fin 2886) := Fin.ext h2459
    subst k
    rw [keyMomentRowsAt2459]
    exact keyMoment2459 B hB
  · have he : k = (2460 : Fin 2886) := Fin.ext h2460
    subst k
    rw [keyMomentRowsAt2460]
    exact keyMoment2460 B hB
  · have he : k = (2461 : Fin 2886) := Fin.ext h2461
    subst k
    rw [keyMomentRowsAt2461]
    exact keyMoment2461 B hB
  · have he : k = (2462 : Fin 2886) := Fin.ext h2462
    subst k
    rw [keyMomentRowsAt2462]
    exact keyMoment2462 B hB
  · have he : k = (2463 : Fin 2886) := Fin.ext h2463
    subst k
    rw [keyMomentRowsAt2463]
    exact keyMoment2463 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound76_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound76_e_oai
