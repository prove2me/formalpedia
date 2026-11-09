-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound88_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:06:32.746195+00:00
-- url     : https://prove2.me/submissions/5c619750-c223-451b-a155-273806f93024

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical335
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical42944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42944 raw42944Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw42944 raw42944Labels = mixedMoment B raw42944step0 raw42944step0Labels := by
      have hz : ∀ j, raw42944 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42944step0 = (fun i j => raw42944 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42944step0 raw42944; decide +kernel
      have hl : raw42944step0Labels = raw42944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42944 raw42944Labels permutation434 hz
    mixedMoment B raw42944step0 raw42944step0Labels = mixedMoment B raw42944step1 raw42944step1Labels := by
      have ha : raw42944step1 = (fun i j => raw42944step0 (permutation95 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42944step1 raw42944step0; decide +kernel
      have hl : raw42944step1Labels = raw42944step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42944step0 raw42944step0Labels permutation95 permutation4
    mixedMoment B raw42944step1 raw42944step1Labels = mixedMoment B raw42944step2 raw42944step2Labels := by
      have ha : raw42944step2 = raw42944step1 := by apply Matrix.ext; unfold raw42944step2 raw42944step1; decide +kernel
      have hl : raw42944step1Labels = labelEmbedding1 ∘ raw42944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42944step1 raw42944step1Labels raw42944step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

theorem canonical42945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42945 raw42945Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw42945 raw42945Labels = mixedMoment B raw42945step0 raw42945step0Labels := by
      have hz : ∀ j, raw42945 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42945step0 = (fun i j => raw42945 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42945step0 raw42945; decide +kernel
      have hl : raw42945step0Labels = raw42945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42945 raw42945Labels permutation434 hz
    mixedMoment B raw42945step0 raw42945step0Labels = mixedMoment B raw42945step1 raw42945step1Labels := by
      have ha : raw42945step1 = (fun i j => raw42945step0 (permutation88 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42945step1 raw42945step0; decide +kernel
      have hl : raw42945step1Labels = raw42945step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42945step0 raw42945step0Labels permutation88 permutation6
    mixedMoment B raw42945step1 raw42945step1Labels = mixedMoment B raw42945step2 raw42945step2Labels := by
      have ha : raw42945step2 = -raw42945step1 := by apply Matrix.ext; change ∀ i j, raw42945step2 i j = -(raw42945step1 i j); unfold raw42945step2 raw42945step1; decide +kernel
      have hl : raw42945step2Labels = raw42945step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5139 node5139Labels := by rfl

theorem canonical42946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42946 raw42946Labels = mixedMoment B node3842 node3842Labels := by
  calc
    mixedMoment B raw42946 raw42946Labels = mixedMoment B raw42946step0 raw42946step0Labels := by
      have ha : raw42946step0 = (fun i j => raw42946 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42946step0 raw42946; decide +kernel
      have hl : raw42946step0Labels = raw42946Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42946 raw42946Labels permutation683 permutation2
    mixedMoment B raw42946step0 raw42946step0Labels = mixedMoment B raw42946step1 raw42946step1Labels := by
      have ha : raw42946step1 = -raw42946step0 := by apply Matrix.ext; change ∀ i j, raw42946step1 i j = -(raw42946step0 i j); unfold raw42946step1 raw42946step0; decide +kernel
      have hl : raw42946step1Labels = raw42946step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42946step1 raw42946step1Labels = mixedMoment B raw42946step2 raw42946step2Labels := by
      have ha : raw42946step2 = raw42946step1 := by apply Matrix.ext; unfold raw42946step2 raw42946step1; decide +kernel
      have hl : raw42946step1Labels = labelEmbedding1 ∘ raw42946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42946step1 raw42946step1Labels raw42946step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3842 node3842Labels := by rfl

theorem canonical42947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42947 raw42947Labels = mixedMoment B node5419 node5419Labels := by
  calc
    mixedMoment B raw42947 raw42947Labels = mixedMoment B raw42947step0 raw42947step0Labels := by
      have ha : raw42947step0 = (fun i j => raw42947 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42947step0 raw42947; decide +kernel
      have hl : raw42947step0Labels = raw42947Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42947 raw42947Labels permutation650 permutation7
    mixedMoment B raw42947step0 raw42947step0Labels = mixedMoment B raw42947step1 raw42947step1Labels := by
      have ha : raw42947step1 = raw42947step0 := by apply Matrix.ext; unfold raw42947step1 raw42947step0; decide +kernel
      have hl : raw42947step0Labels = labelEmbedding6 ∘ raw42947step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42947step0 raw42947step0Labels raw42947step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5419 node5419Labels := by rfl

theorem canonical42948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42948 raw42948Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw42948 raw42948Labels = mixedMoment B raw42948step0 raw42948step0Labels := by
      have hz : ∀ j, raw42948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42948step0 = (fun i j => raw42948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42948step0 raw42948; decide +kernel
      have hl : raw42948step0Labels = raw42948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42948 raw42948Labels permutation434 hz
    mixedMoment B raw42948step0 raw42948step0Labels = mixedMoment B raw42948step1 raw42948step1Labels := by
      have ha : raw42948step1 = (fun i j => raw42948step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42948step1 raw42948step0; decide +kernel
      have hl : raw42948step1Labels = raw42948step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42948step0 raw42948step0Labels permutation146 permutation2
    mixedMoment B raw42948step1 raw42948step1Labels = mixedMoment B raw42948step2 raw42948step2Labels := by
      have ha : raw42948step2 = -raw42948step1 := by apply Matrix.ext; change ∀ i j, raw42948step2 i j = -(raw42948step1 i j); unfold raw42948step2 raw42948step1; decide +kernel
      have hl : raw42948step2Labels = raw42948step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42948step2 raw42948step2Labels = mixedMoment B raw42948step3 raw42948step3Labels := by
      have ha : raw42948step3 = raw42948step2 := by apply Matrix.ext; unfold raw42948step3 raw42948step2; decide +kernel
      have hl : raw42948step2Labels = labelEmbedding1 ∘ raw42948step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42948step2 raw42948step2Labels raw42948step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

theorem canonical42949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42949 raw42949Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw42949 raw42949Labels = mixedMoment B raw42949step0 raw42949step0Labels := by
      have hz : ∀ j, raw42949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42949step0 = (fun i j => raw42949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42949step0 raw42949; decide +kernel
      have hl : raw42949step0Labels = raw42949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42949 raw42949Labels permutation434 hz
    mixedMoment B raw42949step0 raw42949step0Labels = mixedMoment B raw42949step1 raw42949step1Labels := by
      have ha : raw42949step1 = (fun i j => raw42949step0 (permutation132 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42949step1 raw42949step0; decide +kernel
      have hl : raw42949step1Labels = raw42949step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42949step0 raw42949step0Labels permutation132 permutation7
    mixedMoment B raw42949step1 raw42949step1Labels = mixedMoment B raw42949step2 raw42949step2Labels := by
      have ha : raw42949step2 = raw42949step1 := by apply Matrix.ext; unfold raw42949step2 raw42949step1; decide +kernel
      have hl : raw42949step1Labels = labelEmbedding6 ∘ raw42949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42949step1 raw42949step1Labels raw42949step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5189 node5189Labels := by rfl

theorem canonical42950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42950 raw42950Labels = mixedMoment B node0 node0Labels := by
  calc
    mixedMoment B raw42950 raw42950Labels = mixedMoment B raw42950step0 raw42950step0Labels := by
      have hz : ∀ j, raw42950 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42950step0 = (fun i j => raw42950 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42950step0 raw42950; decide +kernel
      have hl : raw42950step0Labels = raw42950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42950 raw42950Labels permutation520 hz
    mixedMoment B raw42950step0 raw42950step0Labels = mixedMoment B raw42950step1 raw42950step1Labels := by
      have hz : ∀ j, raw42950step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42950step1 = (fun i j => raw42950step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42950step1 raw42950step0; decide +kernel
      have hl : raw42950step1Labels = raw42950step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42950step0 raw42950step0Labels permutation104 hz
    mixedMoment B raw42950step1 raw42950step1Labels = mixedMoment B raw42950step2 raw42950step2Labels := by
      have hz : ∀ i, raw42950step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42950step2 = (fun i j => raw42950step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42950step2 raw42950step1; decide +kernel
      have hl : raw42950step2Labels = (fun j => raw42950step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42950step1 raw42950step1Labels permutation6 hz
    mixedMoment B raw42950step2 raw42950step2Labels = mixedMoment B raw42950step3 raw42950step3Labels := by
      have ha : raw42950step3 = (fun i j => raw42950step2 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw42950step3 raw42950step2; decide +kernel
      have hl : raw42950step3Labels = raw42950step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42950step2 raw42950step2Labels permutation26 permutation0
    mixedMoment B raw42950step3 raw42950step3Labels = mixedMoment B raw42950step4 raw42950step4Labels := by
      have ha : raw42950step4 = -raw42950step3 := by apply Matrix.ext; change ∀ i j, raw42950step4 i j = -(raw42950step3 i j); unfold raw42950step4 raw42950step3; decide +kernel
      have hl : raw42950step4Labels = raw42950step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42950step4 raw42950step4Labels = mixedMoment B raw42950step5 raw42950step5Labels := by
      have ha : raw42950step5 = raw42950step4 := by apply Matrix.ext; unfold raw42950step5 raw42950step4; decide +kernel
      have hl : raw42950step4Labels = labelEmbedding0 ∘ raw42950step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42950step4 raw42950step4Labels raw42950step5Labels labelEmbedding0 hl
    _ = mixedMoment B node0 node0Labels := by rfl

theorem canonical42951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42951 raw42951Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw42951 raw42951Labels = mixedMoment B raw42951step0 raw42951step0Labels := by
      have hz : ∀ j, raw42951 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42951step0 = (fun i j => raw42951 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42951step0 raw42951; decide +kernel
      have hl : raw42951step0Labels = raw42951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42951 raw42951Labels permutation520 hz
    mixedMoment B raw42951step0 raw42951step0Labels = mixedMoment B raw42951step1 raw42951step1Labels := by
      have hz : ∀ j, raw42951step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42951step1 = (fun i j => raw42951step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42951step1 raw42951step0; decide +kernel
      have hl : raw42951step1Labels = raw42951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42951step0 raw42951step0Labels permutation104 hz
    mixedMoment B raw42951step1 raw42951step1Labels = mixedMoment B raw42951step2 raw42951step2Labels := by
      have hz : ∀ i, raw42951step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42951step2 = (fun i j => raw42951step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42951step2 raw42951step1; decide +kernel
      have hl : raw42951step2Labels = (fun j => raw42951step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42951step1 raw42951step1Labels permutation6 hz
    mixedMoment B raw42951step2 raw42951step2Labels = mixedMoment B raw42951step3 raw42951step3Labels := by
      have ha : raw42951step3 = (fun i j => raw42951step2 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw42951step3 raw42951step2; decide +kernel
      have hl : raw42951step3Labels = raw42951step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42951step2 raw42951step2Labels permutation26 permutation0
    mixedMoment B raw42951step3 raw42951step3Labels = mixedMoment B raw42951step4 raw42951step4Labels := by
      have ha : raw42951step4 = -raw42951step3 := by apply Matrix.ext; change ∀ i j, raw42951step4 i j = -(raw42951step3 i j); unfold raw42951step4 raw42951step3; decide +kernel
      have hl : raw42951step4Labels = raw42951step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42951step4 raw42951step4Labels = mixedMoment B raw42951step5 raw42951step5Labels := by
      have ha : raw42951step5 = raw42951step4 := by apply Matrix.ext; unfold raw42951step5 raw42951step4; decide +kernel
      have hl : raw42951step4Labels = labelEmbedding3 ∘ raw42951step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42951step4 raw42951step4Labels raw42951step5Labels labelEmbedding3 hl
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical42952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42952 raw42952Labels = mixedMoment B node3111 node3111Labels := by
  calc
    mixedMoment B raw42952 raw42952Labels = mixedMoment B raw42952step0 raw42952step0Labels := by
      have hz : ∀ j, raw42952 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42952step0 = (fun i j => raw42952 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42952step0 raw42952; decide +kernel
      have hl : raw42952step0Labels = raw42952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42952 raw42952Labels permutation434 hz
    mixedMoment B raw42952step0 raw42952step0Labels = mixedMoment B raw42952step1 raw42952step1Labels := by
      have ha : raw42952step1 = (fun i j => raw42952step0 (permutation146 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42952step1 raw42952step0; decide +kernel
      have hl : raw42952step1Labels = raw42952step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42952step0 raw42952step0Labels permutation146 permutation4
    mixedMoment B raw42952step1 raw42952step1Labels = mixedMoment B raw42952step2 raw42952step2Labels := by
      have ha : raw42952step2 = raw42952step1 := by apply Matrix.ext; unfold raw42952step2 raw42952step1; decide +kernel
      have hl : raw42952step1Labels = labelEmbedding1 ∘ raw42952step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42952step1 raw42952step1Labels raw42952step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3111 node3111Labels := by rfl

theorem canonical42953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42953 raw42953Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw42953 raw42953Labels = mixedMoment B raw42953step0 raw42953step0Labels := by
      have hz : ∀ j, raw42953 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42953step0 = (fun i j => raw42953 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42953step0 raw42953; decide +kernel
      have hl : raw42953step0Labels = raw42953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42953 raw42953Labels permutation434 hz
    mixedMoment B raw42953step0 raw42953step0Labels = mixedMoment B raw42953step1 raw42953step1Labels := by
      have ha : raw42953step1 = (fun i j => raw42953step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42953step1 raw42953step0; decide +kernel
      have hl : raw42953step1Labels = raw42953step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42953step0 raw42953step0Labels permutation146 permutation5
    mixedMoment B raw42953step1 raw42953step1Labels = mixedMoment B raw42953step2 raw42953step2Labels := by
      have ha : raw42953step2 = raw42953step1 := by apply Matrix.ext; unfold raw42953step2 raw42953step1; decide +kernel
      have hl : raw42953step1Labels = labelEmbedding9 ∘ raw42953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42953step1 raw42953step1Labels raw42953step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

theorem canonical42954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42954 raw42954Labels = mixedMoment B node3 node3Labels := by
  calc
    mixedMoment B raw42954 raw42954Labels = mixedMoment B raw42954step0 raw42954step0Labels := by
      have hz : ∀ j, raw42954 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42954step0 = (fun i j => raw42954 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42954step0 raw42954; decide +kernel
      have hl : raw42954step0Labels = raw42954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42954 raw42954Labels permutation434 hz
    mixedMoment B raw42954step0 raw42954step0Labels = mixedMoment B raw42954step1 raw42954step1Labels := by
      have hz : ∀ i, raw42954step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42954step1 = (fun i j => raw42954step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42954step1 raw42954step0; decide +kernel
      have hl : raw42954step1Labels = (fun j => raw42954step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42954step0 raw42954step0Labels permutation6 hz
    mixedMoment B raw42954step1 raw42954step1Labels = mixedMoment B raw42954step2 raw42954step2Labels := by
      have ha : raw42954step2 = (fun i j => raw42954step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw42954step2 raw42954step1; decide +kernel
      have hl : raw42954step2Labels = raw42954step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42954step1 raw42954step1Labels permutation146 permutation0
    mixedMoment B raw42954step2 raw42954step2Labels = mixedMoment B raw42954step3 raw42954step3Labels := by
      have ha : raw42954step3 = -raw42954step2 := by apply Matrix.ext; change ∀ i j, raw42954step3 i j = -(raw42954step2 i j); unfold raw42954step3 raw42954step2; decide +kernel
      have hl : raw42954step3Labels = raw42954step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42954step3 raw42954step3Labels = mixedMoment B raw42954step4 raw42954step4Labels := by
      have ha : raw42954step4 = raw42954step3 := by apply Matrix.ext; unfold raw42954step4 raw42954step3; decide +kernel
      have hl : raw42954step3Labels = labelEmbedding0 ∘ raw42954step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42954step3 raw42954step3Labels raw42954step4Labels labelEmbedding0 hl
    _ = mixedMoment B node3 node3Labels := by rfl

theorem canonical42955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42955 raw42955Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw42955 raw42955Labels = mixedMoment B raw42955step0 raw42955step0Labels := by
      have hz : ∀ j, raw42955 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42955step0 = (fun i j => raw42955 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42955step0 raw42955; decide +kernel
      have hl : raw42955step0Labels = raw42955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42955 raw42955Labels permutation434 hz
    mixedMoment B raw42955step0 raw42955step0Labels = mixedMoment B raw42955step1 raw42955step1Labels := by
      have hz : ∀ i, raw42955step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42955step1 = (fun i j => raw42955step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42955step1 raw42955step0; decide +kernel
      have hl : raw42955step1Labels = (fun j => raw42955step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42955step0 raw42955step0Labels permutation6 hz
    mixedMoment B raw42955step1 raw42955step1Labels = mixedMoment B raw42955step2 raw42955step2Labels := by
      have ha : raw42955step2 = (fun i j => raw42955step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw42955step2 raw42955step1; decide +kernel
      have hl : raw42955step2Labels = raw42955step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42955step1 raw42955step1Labels permutation146 permutation0
    mixedMoment B raw42955step2 raw42955step2Labels = mixedMoment B raw42955step3 raw42955step3Labels := by
      have ha : raw42955step3 = -raw42955step2 := by apply Matrix.ext; change ∀ i j, raw42955step3 i j = -(raw42955step2 i j); unfold raw42955step3 raw42955step2; decide +kernel
      have hl : raw42955step3Labels = raw42955step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42955step3 raw42955step3Labels = mixedMoment B raw42955step4 raw42955step4Labels := by
      have ha : raw42955step4 = raw42955step3 := by apply Matrix.ext; unfold raw42955step4 raw42955step3; decide +kernel
      have hl : raw42955step3Labels = labelEmbedding3 ∘ raw42955step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42955step3 raw42955step3Labels raw42955step4Labels labelEmbedding3 hl
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical42956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42956 raw42956Labels = mixedMoment B node4034 node4034Labels := by
  calc
    mixedMoment B raw42956 raw42956Labels = mixedMoment B raw42956step0 raw42956step0Labels := by
      have ha : raw42956step0 = (fun i j => raw42956 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42956step0 raw42956; decide +kernel
      have hl : raw42956step0Labels = raw42956Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42956 raw42956Labels permutation683 permutation2
    mixedMoment B raw42956step0 raw42956step0Labels = mixedMoment B raw42956step1 raw42956step1Labels := by
      have ha : raw42956step1 = -raw42956step0 := by apply Matrix.ext; change ∀ i j, raw42956step1 i j = -(raw42956step0 i j); unfold raw42956step1 raw42956step0; decide +kernel
      have hl : raw42956step1Labels = raw42956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42956step1 raw42956step1Labels = mixedMoment B raw42956step2 raw42956step2Labels := by
      have ha : raw42956step2 = raw42956step1 := by apply Matrix.ext; unfold raw42956step2 raw42956step1; decide +kernel
      have hl : raw42956step1Labels = labelEmbedding1 ∘ raw42956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42956step1 raw42956step1Labels raw42956step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4034 node4034Labels := by rfl

theorem canonical42957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42957 raw42957Labels = mixedMoment B node5427 node5427Labels := by
  calc
    mixedMoment B raw42957 raw42957Labels = mixedMoment B raw42957step0 raw42957step0Labels := by
      have ha : raw42957step0 = (fun i j => raw42957 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42957step0 raw42957; decide +kernel
      have hl : raw42957step0Labels = raw42957Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42957 raw42957Labels permutation683 permutation3
    mixedMoment B raw42957step0 raw42957step0Labels = mixedMoment B raw42957step1 raw42957step1Labels := by
      have ha : raw42957step1 = -raw42957step0 := by apply Matrix.ext; change ∀ i j, raw42957step1 i j = -(raw42957step0 i j); unfold raw42957step1 raw42957step0; decide +kernel
      have hl : raw42957step1Labels = raw42957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42957step1 raw42957step1Labels = mixedMoment B raw42957step2 raw42957step2Labels := by
      have ha : raw42957step2 = raw42957step1 := by apply Matrix.ext; unfold raw42957step2 raw42957step1; decide +kernel
      have hl : raw42957step1Labels = labelEmbedding7 ∘ raw42957step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42957step1 raw42957step1Labels raw42957step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5427 node5427Labels := by rfl

theorem canonical42958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42958 raw42958Labels = mixedMoment B node3855 node3855Labels := by
  calc
    mixedMoment B raw42958 raw42958Labels = mixedMoment B raw42958step0 raw42958step0Labels := by
      have ha : raw42958step0 = (fun i j => raw42958 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42958step0 raw42958; decide +kernel
      have hl : raw42958step0Labels = raw42958Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42958 raw42958Labels permutation683 permutation2
    mixedMoment B raw42958step0 raw42958step0Labels = mixedMoment B raw42958step1 raw42958step1Labels := by
      have ha : raw42958step1 = -raw42958step0 := by apply Matrix.ext; change ∀ i j, raw42958step1 i j = -(raw42958step0 i j); unfold raw42958step1 raw42958step0; decide +kernel
      have hl : raw42958step1Labels = raw42958step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42958step1 raw42958step1Labels = mixedMoment B raw42958step2 raw42958step2Labels := by
      have ha : raw42958step2 = raw42958step1 := by apply Matrix.ext; unfold raw42958step2 raw42958step1; decide +kernel
      have hl : raw42958step1Labels = labelEmbedding1 ∘ raw42958step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42958step1 raw42958step1Labels raw42958step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3855 node3855Labels := by rfl

theorem canonical42959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42959 raw42959Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw42959 raw42959Labels = mixedMoment B raw42959step0 raw42959step0Labels := by
      have ha : raw42959step0 = (fun i j => raw42959 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42959step0 raw42959; decide +kernel
      have hl : raw42959step0Labels = raw42959Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42959 raw42959Labels permutation683 permutation2
    mixedMoment B raw42959step0 raw42959step0Labels = mixedMoment B raw42959step1 raw42959step1Labels := by
      have ha : raw42959step1 = -raw42959step0 := by apply Matrix.ext; change ∀ i j, raw42959step1 i j = -(raw42959step0 i j); unfold raw42959step1 raw42959step0; decide +kernel
      have hl : raw42959step1Labels = raw42959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42959step1 raw42959step1Labels = mixedMoment B raw42959step2 raw42959step2Labels := by
      have ha : raw42959step2 = raw42959step1 := by apply Matrix.ext; unfold raw42959step2 raw42959step1; decide +kernel
      have hl : raw42959step1Labels = labelEmbedding8 ∘ raw42959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42959step1 raw42959step1Labels raw42959step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5437 node5437Labels := by rfl

theorem canonical42960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42960 raw42960Labels = mixedMoment B node3228 node3228Labels := by
  calc
    mixedMoment B raw42960 raw42960Labels = mixedMoment B raw42960step0 raw42960step0Labels := by
      have hz : ∀ j, raw42960 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42960step0 = (fun i j => raw42960 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42960step0 raw42960; decide +kernel
      have hl : raw42960step0Labels = raw42960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42960 raw42960Labels permutation520 hz
    mixedMoment B raw42960step0 raw42960step0Labels = mixedMoment B raw42960step1 raw42960step1Labels := by
      have ha : raw42960step1 = (fun i j => raw42960step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42960step1 raw42960step0; decide +kernel
      have hl : raw42960step1Labels = raw42960step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42960step0 raw42960step0Labels permutation146 permutation2
    mixedMoment B raw42960step1 raw42960step1Labels = mixedMoment B raw42960step2 raw42960step2Labels := by
      have ha : raw42960step2 = -raw42960step1 := by apply Matrix.ext; change ∀ i j, raw42960step2 i j = -(raw42960step1 i j); unfold raw42960step2 raw42960step1; decide +kernel
      have hl : raw42960step2Labels = raw42960step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42960step2 raw42960step2Labels = mixedMoment B raw42960step3 raw42960step3Labels := by
      have ha : raw42960step3 = raw42960step2 := by apply Matrix.ext; unfold raw42960step3 raw42960step2; decide +kernel
      have hl : raw42960step2Labels = labelEmbedding1 ∘ raw42960step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42960step2 raw42960step2Labels raw42960step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3228 node3228Labels := by rfl

theorem canonical42961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42961 raw42961Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw42961 raw42961Labels = mixedMoment B raw42961step0 raw42961step0Labels := by
      have hz : ∀ j, raw42961 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42961step0 = (fun i j => raw42961 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42961step0 raw42961; decide +kernel
      have hl : raw42961step0Labels = raw42961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42961 raw42961Labels permutation520 hz
    mixedMoment B raw42961step0 raw42961step0Labels = mixedMoment B raw42961step1 raw42961step1Labels := by
      have ha : raw42961step1 = (fun i j => raw42961step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42961step1 raw42961step0; decide +kernel
      have hl : raw42961step1Labels = raw42961step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42961step0 raw42961step0Labels permutation150 permutation3
    mixedMoment B raw42961step1 raw42961step1Labels = mixedMoment B raw42961step2 raw42961step2Labels := by
      have ha : raw42961step2 = -raw42961step1 := by apply Matrix.ext; change ∀ i j, raw42961step2 i j = -(raw42961step1 i j); unfold raw42961step2 raw42961step1; decide +kernel
      have hl : raw42961step2Labels = raw42961step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42961step2 raw42961step2Labels = mixedMoment B raw42961step3 raw42961step3Labels := by
      have ha : raw42961step3 = raw42961step2 := by apply Matrix.ext; unfold raw42961step3 raw42961step2; decide +kernel
      have hl : raw42961step2Labels = labelEmbedding7 ∘ raw42961step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42961step2 raw42961step2Labels raw42961step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4893 node4893Labels := by rfl

theorem canonical42962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42962 raw42962Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw42962 raw42962Labels = mixedMoment B raw42962step0 raw42962step0Labels := by
      have ha : raw42962step0 = (fun i j => raw42962 (permutation641 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42962step0 raw42962; decide +kernel
      have hl : raw42962step0Labels = raw42962Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42962 raw42962Labels permutation641 permutation4
    mixedMoment B raw42962step0 raw42962step0Labels = mixedMoment B raw42962step1 raw42962step1Labels := by
      have ha : raw42962step1 = raw42962step0 := by apply Matrix.ext; unfold raw42962step1 raw42962step0; decide +kernel
      have hl : raw42962step0Labels = labelEmbedding1 ∘ raw42962step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42962step0 raw42962step0Labels raw42962step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3087 node3087Labels := by rfl

theorem canonical42963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42963 raw42963Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw42963 raw42963Labels = mixedMoment B raw42963step0 raw42963step0Labels := by
      have ha : raw42963step0 = (fun i j => raw42963 (permutation681 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42963step0 raw42963; decide +kernel
      have hl : raw42963step0Labels = raw42963Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42963 raw42963Labels permutation681 permutation5
    mixedMoment B raw42963step0 raw42963step0Labels = mixedMoment B raw42963step1 raw42963step1Labels := by
      have ha : raw42963step1 = raw42963step0 := by apply Matrix.ext; unfold raw42963step1 raw42963step0; decide +kernel
      have hl : raw42963step0Labels = labelEmbedding9 ∘ raw42963step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42963step0 raw42963step0Labels raw42963step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical42964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42964 raw42964Labels = mixedMoment B node4038 node4038Labels := by
  calc
    mixedMoment B raw42964 raw42964Labels = mixedMoment B raw42964step0 raw42964step0Labels := by
      have ha : raw42964step0 = (fun i j => raw42964 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42964step0 raw42964; decide +kernel
      have hl : raw42964step0Labels = raw42964Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42964 raw42964Labels permutation683 permutation2
    mixedMoment B raw42964step0 raw42964step0Labels = mixedMoment B raw42964step1 raw42964step1Labels := by
      have ha : raw42964step1 = -raw42964step0 := by apply Matrix.ext; change ∀ i j, raw42964step1 i j = -(raw42964step0 i j); unfold raw42964step1 raw42964step0; decide +kernel
      have hl : raw42964step1Labels = raw42964step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42964step1 raw42964step1Labels = mixedMoment B raw42964step2 raw42964step2Labels := by
      have ha : raw42964step2 = raw42964step1 := by apply Matrix.ext; unfold raw42964step2 raw42964step1; decide +kernel
      have hl : raw42964step1Labels = labelEmbedding1 ∘ raw42964step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42964step1 raw42964step1Labels raw42964step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4038 node4038Labels := by rfl

theorem canonical42965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42965 raw42965Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw42965 raw42965Labels = mixedMoment B raw42965step0 raw42965step0Labels := by
      have ha : raw42965step0 = (fun i j => raw42965 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42965step0 raw42965; decide +kernel
      have hl : raw42965step0Labels = raw42965Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42965 raw42965Labels permutation687 permutation3
    mixedMoment B raw42965step0 raw42965step0Labels = mixedMoment B raw42965step1 raw42965step1Labels := by
      have ha : raw42965step1 = -raw42965step0 := by apply Matrix.ext; change ∀ i j, raw42965step1 i j = -(raw42965step0 i j); unfold raw42965step1 raw42965step0; decide +kernel
      have hl : raw42965step1Labels = raw42965step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42965step1 raw42965step1Labels = mixedMoment B raw42965step2 raw42965step2Labels := by
      have ha : raw42965step2 = raw42965step1 := by apply Matrix.ext; unfold raw42965step2 raw42965step1; decide +kernel
      have hl : raw42965step1Labels = labelEmbedding7 ∘ raw42965step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42965step1 raw42965step1Labels raw42965step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5408 node5408Labels := by rfl

theorem canonical42966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42966 raw42966Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw42966 raw42966Labels = mixedMoment B raw42966step0 raw42966step0Labels := by
      have hz : ∀ j, raw42966 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42966step0 = (fun i j => raw42966 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42966step0 raw42966; decide +kernel
      have hl : raw42966step0Labels = raw42966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42966 raw42966Labels permutation434 hz
    mixedMoment B raw42966step0 raw42966step0Labels = mixedMoment B raw42966step1 raw42966step1Labels := by
      have ha : raw42966step1 = (fun i j => raw42966step0 (permutation140 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42966step1 raw42966step0; decide +kernel
      have hl : raw42966step1Labels = raw42966step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42966step0 raw42966step0Labels permutation140 permutation4
    mixedMoment B raw42966step1 raw42966step1Labels = mixedMoment B raw42966step2 raw42966step2Labels := by
      have ha : raw42966step2 = raw42966step1 := by apply Matrix.ext; unfold raw42966step2 raw42966step1; decide +kernel
      have hl : raw42966step1Labels = labelEmbedding1 ∘ raw42966step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42966step1 raw42966step1Labels raw42966step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3099 node3099Labels := by rfl

theorem canonical42967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42967 raw42967Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw42967 raw42967Labels = mixedMoment B raw42967step0 raw42967step0Labels := by
      have hz : ∀ j, raw42967 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42967step0 = (fun i j => raw42967 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42967step0 raw42967; decide +kernel
      have hl : raw42967step0Labels = raw42967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42967 raw42967Labels permutation434 hz
    mixedMoment B raw42967step0 raw42967step0Labels = mixedMoment B raw42967step1 raw42967step1Labels := by
      have ha : raw42967step1 = (fun i j => raw42967step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42967step1 raw42967step0; decide +kernel
      have hl : raw42967step1Labels = raw42967step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42967step0 raw42967step0Labels permutation144 permutation5
    mixedMoment B raw42967step1 raw42967step1Labels = mixedMoment B raw42967step2 raw42967step2Labels := by
      have ha : raw42967step2 = raw42967step1 := by apply Matrix.ext; unfold raw42967step2 raw42967step1; decide +kernel
      have hl : raw42967step1Labels = labelEmbedding9 ∘ raw42967step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42967step1 raw42967step1Labels raw42967step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical42968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42968 raw42968Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw42968 raw42968Labels = mixedMoment B raw42968step0 raw42968step0Labels := by
      have ha : raw42968step0 = (fun i j => raw42968 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42968step0 raw42968; decide +kernel
      have hl : raw42968step0Labels = raw42968Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42968 raw42968Labels permutation683 permutation2
    mixedMoment B raw42968step0 raw42968step0Labels = mixedMoment B raw42968step1 raw42968step1Labels := by
      have ha : raw42968step1 = -raw42968step0 := by apply Matrix.ext; change ∀ i j, raw42968step1 i j = -(raw42968step0 i j); unfold raw42968step1 raw42968step0; decide +kernel
      have hl : raw42968step1Labels = raw42968step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42968step1 raw42968step1Labels = mixedMoment B raw42968step2 raw42968step2Labels := by
      have ha : raw42968step2 = raw42968step1 := by apply Matrix.ext; unfold raw42968step2 raw42968step1; decide +kernel
      have hl : raw42968step1Labels = labelEmbedding1 ∘ raw42968step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42968step1 raw42968step1Labels raw42968step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

theorem canonical42969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42969 raw42969Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw42969 raw42969Labels = mixedMoment B raw42969step0 raw42969step0Labels := by
      have ha : raw42969step0 = (fun i j => raw42969 (permutation657 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42969step0 raw42969; decide +kernel
      have hl : raw42969step0Labels = raw42969Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42969 raw42969Labels permutation657 permutation5
    mixedMoment B raw42969step0 raw42969step0Labels = mixedMoment B raw42969step1 raw42969step1Labels := by
      have ha : raw42969step1 = raw42969step0 := by apply Matrix.ext; unfold raw42969step1 raw42969step0; decide +kernel
      have hl : raw42969step0Labels = labelEmbedding9 ∘ raw42969step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42969step0 raw42969step0Labels raw42969step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical42970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42970 raw42970Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw42970 raw42970Labels = mixedMoment B raw42970step0 raw42970step0Labels := by
      have ha : raw42970step0 = (fun i j => raw42970 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42970step0 raw42970; decide +kernel
      have hl : raw42970step0Labels = raw42970Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42970 raw42970Labels permutation683 permutation2
    mixedMoment B raw42970step0 raw42970step0Labels = mixedMoment B raw42970step1 raw42970step1Labels := by
      have ha : raw42970step1 = -raw42970step0 := by apply Matrix.ext; change ∀ i j, raw42970step1 i j = -(raw42970step0 i j); unfold raw42970step1 raw42970step0; decide +kernel
      have hl : raw42970step1Labels = raw42970step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42970step1 raw42970step1Labels = mixedMoment B raw42970step2 raw42970step2Labels := by
      have ha : raw42970step2 = raw42970step1 := by apply Matrix.ext; unfold raw42970step2 raw42970step1; decide +kernel
      have hl : raw42970step1Labels = labelEmbedding1 ∘ raw42970step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42970step1 raw42970step1Labels raw42970step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

theorem canonical42971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42971 raw42971Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw42971 raw42971Labels = mixedMoment B raw42971step0 raw42971step0Labels := by
      have ha : raw42971step0 = (fun i j => raw42971 (permutation665 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42971step0 raw42971; decide +kernel
      have hl : raw42971step0Labels = raw42971Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42971 raw42971Labels permutation665 permutation7
    mixedMoment B raw42971step0 raw42971step0Labels = mixedMoment B raw42971step1 raw42971step1Labels := by
      have ha : raw42971step1 = raw42971step0 := by apply Matrix.ext; unfold raw42971step1 raw42971step0; decide +kernel
      have hl : raw42971step0Labels = labelEmbedding6 ∘ raw42971step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42971step0 raw42971step0Labels raw42971step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical42972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42972 raw42972Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw42972 raw42972Labels = mixedMoment B raw42972step0 raw42972step0Labels := by
      have ha : raw42972step0 = (fun i j => raw42972 (permutation641 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42972step0 raw42972; decide +kernel
      have hl : raw42972step0Labels = raw42972Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42972 raw42972Labels permutation641 permutation4
    mixedMoment B raw42972step0 raw42972step0Labels = mixedMoment B raw42972step1 raw42972step1Labels := by
      have ha : raw42972step1 = raw42972step0 := by apply Matrix.ext; unfold raw42972step1 raw42972step0; decide +kernel
      have hl : raw42972step0Labels = labelEmbedding1 ∘ raw42972step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42972step0 raw42972step0Labels raw42972step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

theorem canonical42973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42973 raw42973Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw42973 raw42973Labels = mixedMoment B raw42973step0 raw42973step0Labels := by
      have ha : raw42973step0 = (fun i j => raw42973 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42973step0 raw42973; decide +kernel
      have hl : raw42973step0Labels = raw42973Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42973 raw42973Labels permutation687 permutation3
    mixedMoment B raw42973step0 raw42973step0Labels = mixedMoment B raw42973step1 raw42973step1Labels := by
      have ha : raw42973step1 = -raw42973step0 := by apply Matrix.ext; change ∀ i j, raw42973step1 i j = -(raw42973step0 i j); unfold raw42973step1 raw42973step0; decide +kernel
      have hl : raw42973step1Labels = raw42973step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42973step1 raw42973step1Labels = mixedMoment B raw42973step2 raw42973step2Labels := by
      have ha : raw42973step2 = raw42973step1 := by apply Matrix.ext; unfold raw42973step2 raw42973step1; decide +kernel
      have hl : raw42973step1Labels = labelEmbedding7 ∘ raw42973step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42973step1 raw42973step1Labels raw42973step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical42974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42974 raw42974Labels = mixedMoment B node4028 node4028Labels := by
  calc
    mixedMoment B raw42974 raw42974Labels = mixedMoment B raw42974step0 raw42974step0Labels := by
      have hz : ∀ j, raw42974 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42974step0 = (fun i j => raw42974 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42974step0 raw42974; decide +kernel
      have hl : raw42974step0Labels = raw42974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42974 raw42974Labels permutation434 hz
    mixedMoment B raw42974step0 raw42974step0Labels = mixedMoment B raw42974step1 raw42974step1Labels := by
      have ha : raw42974step1 = (fun i j => raw42974step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42974step1 raw42974step0; decide +kernel
      have hl : raw42974step1Labels = raw42974step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42974step0 raw42974step0Labels permutation146 permutation2
    mixedMoment B raw42974step1 raw42974step1Labels = mixedMoment B raw42974step2 raw42974step2Labels := by
      have ha : raw42974step2 = -raw42974step1 := by apply Matrix.ext; change ∀ i j, raw42974step2 i j = -(raw42974step1 i j); unfold raw42974step2 raw42974step1; decide +kernel
      have hl : raw42974step2Labels = raw42974step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42974step2 raw42974step2Labels = mixedMoment B raw42974step3 raw42974step3Labels := by
      have ha : raw42974step3 = raw42974step2 := by apply Matrix.ext; unfold raw42974step3 raw42974step2; decide +kernel
      have hl : raw42974step2Labels = labelEmbedding1 ∘ raw42974step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42974step2 raw42974step2Labels raw42974step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4028 node4028Labels := by rfl

theorem canonical42975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42975 raw42975Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw42975 raw42975Labels = mixedMoment B raw42975step0 raw42975step0Labels := by
      have hz : ∀ j, raw42975 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42975step0 = (fun i j => raw42975 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42975step0 raw42975; decide +kernel
      have hl : raw42975step0Labels = raw42975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42975 raw42975Labels permutation434 hz
    mixedMoment B raw42975step0 raw42975step0Labels = mixedMoment B raw42975step1 raw42975step1Labels := by
      have ha : raw42975step1 = (fun i j => raw42975step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42975step1 raw42975step0; decide +kernel
      have hl : raw42975step1Labels = raw42975step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42975step0 raw42975step0Labels permutation150 permutation3
    mixedMoment B raw42975step1 raw42975step1Labels = mixedMoment B raw42975step2 raw42975step2Labels := by
      have ha : raw42975step2 = -raw42975step1 := by apply Matrix.ext; change ∀ i j, raw42975step2 i j = -(raw42975step1 i j); unfold raw42975step2 raw42975step1; decide +kernel
      have hl : raw42975step2Labels = raw42975step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42975step2 raw42975step2Labels = mixedMoment B raw42975step3 raw42975step3Labels := by
      have ha : raw42975step3 = raw42975step2 := by apply Matrix.ext; unfold raw42975step3 raw42975step2; decide +kernel
      have hl : raw42975step2Labels = labelEmbedding7 ∘ raw42975step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42975step2 raw42975step2Labels raw42975step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

theorem canonical42976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42976 raw42976Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw42976 raw42976Labels = mixedMoment B raw42976step0 raw42976step0Labels := by
      have ha : raw42976step0 = (fun i j => raw42976 (permutation409 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42976step0 raw42976; decide +kernel
      have hl : raw42976step0Labels = raw42976Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42976 raw42976Labels permutation409 permutation4
    mixedMoment B raw42976step0 raw42976step0Labels = mixedMoment B raw42976step1 raw42976step1Labels := by
      have ha : raw42976step1 = raw42976step0 := by apply Matrix.ext; unfold raw42976step1 raw42976step0; decide +kernel
      have hl : raw42976step0Labels = labelEmbedding1 ∘ raw42976step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42976step0 raw42976step0Labels raw42976step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

theorem canonical42977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42977 raw42977Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw42977 raw42977Labels = mixedMoment B raw42977step0 raw42977step0Labels := by
      have ha : raw42977step0 = (fun i j => raw42977 (permutation399 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42977step0 raw42977; decide +kernel
      have hl : raw42977step0Labels = raw42977Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42977 raw42977Labels permutation399 permutation6
    mixedMoment B raw42977step0 raw42977step0Labels = mixedMoment B raw42977step1 raw42977step1Labels := by
      have ha : raw42977step1 = -raw42977step0 := by apply Matrix.ext; change ∀ i j, raw42977step1 i j = -(raw42977step0 i j); unfold raw42977step1 raw42977step0; decide +kernel
      have hl : raw42977step1Labels = raw42977step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical42978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42978 raw42978Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw42978 raw42978Labels = mixedMoment B raw42978step0 raw42978step0Labels := by
      have hz : ∀ j, raw42978 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42978step0 = (fun i j => raw42978 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42978step0 raw42978; decide +kernel
      have hl : raw42978step0Labels = raw42978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42978 raw42978Labels permutation434 hz
    mixedMoment B raw42978step0 raw42978step0Labels = mixedMoment B raw42978step1 raw42978step1Labels := by
      have ha : raw42978step1 = (fun i j => raw42978step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42978step1 raw42978step0; decide +kernel
      have hl : raw42978step1Labels = raw42978step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42978step0 raw42978step0Labels permutation146 permutation2
    mixedMoment B raw42978step1 raw42978step1Labels = mixedMoment B raw42978step2 raw42978step2Labels := by
      have ha : raw42978step2 = -raw42978step1 := by apply Matrix.ext; change ∀ i j, raw42978step2 i j = -(raw42978step1 i j); unfold raw42978step2 raw42978step1; decide +kernel
      have hl : raw42978step2Labels = raw42978step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42978step2 raw42978step2Labels = mixedMoment B raw42978step3 raw42978step3Labels := by
      have ha : raw42978step3 = raw42978step2 := by apply Matrix.ext; unfold raw42978step3 raw42978step2; decide +kernel
      have hl : raw42978step2Labels = labelEmbedding1 ∘ raw42978step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42978step2 raw42978step2Labels raw42978step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3543 node3543Labels := by rfl

theorem canonical42979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42979 raw42979Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw42979 raw42979Labels = mixedMoment B raw42979step0 raw42979step0Labels := by
      have hz : ∀ j, raw42979 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42979step0 = (fun i j => raw42979 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42979step0 raw42979; decide +kernel
      have hl : raw42979step0Labels = raw42979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42979 raw42979Labels permutation434 hz
    mixedMoment B raw42979step0 raw42979step0Labels = mixedMoment B raw42979step1 raw42979step1Labels := by
      have ha : raw42979step1 = (fun i j => raw42979step0 (permutation92 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42979step1 raw42979step0; decide +kernel
      have hl : raw42979step1Labels = raw42979step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42979step0 raw42979step0Labels permutation92 permutation6
    mixedMoment B raw42979step1 raw42979step1Labels = mixedMoment B raw42979step2 raw42979step2Labels := by
      have ha : raw42979step2 = -raw42979step1 := by apply Matrix.ext; change ∀ i j, raw42979step2 i j = -(raw42979step1 i j); unfold raw42979step2 raw42979step1; decide +kernel
      have hl : raw42979step2Labels = raw42979step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5252 node5252Labels := by rfl

theorem canonical42980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42980 raw42980Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw42980 raw42980Labels = mixedMoment B raw42980step0 raw42980step0Labels := by
      have hz : ∀ j, raw42980 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42980step0 = (fun i j => raw42980 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42980step0 raw42980; decide +kernel
      have hl : raw42980step0Labels = raw42980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42980 raw42980Labels permutation520 hz
    mixedMoment B raw42980step0 raw42980step0Labels = mixedMoment B raw42980step1 raw42980step1Labels := by
      have ha : raw42980step1 = (fun i j => raw42980step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42980step1 raw42980step0; decide +kernel
      have hl : raw42980step1Labels = raw42980step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42980step0 raw42980step0Labels permutation146 permutation2
    mixedMoment B raw42980step1 raw42980step1Labels = mixedMoment B raw42980step2 raw42980step2Labels := by
      have ha : raw42980step2 = -raw42980step1 := by apply Matrix.ext; change ∀ i j, raw42980step2 i j = -(raw42980step1 i j); unfold raw42980step2 raw42980step1; decide +kernel
      have hl : raw42980step2Labels = raw42980step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42980step2 raw42980step2Labels = mixedMoment B raw42980step3 raw42980step3Labels := by
      have ha : raw42980step3 = raw42980step2 := by apply Matrix.ext; unfold raw42980step3 raw42980step2; decide +kernel
      have hl : raw42980step2Labels = labelEmbedding1 ∘ raw42980step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42980step2 raw42980step2Labels raw42980step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

theorem canonical42981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42981 raw42981Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw42981 raw42981Labels = mixedMoment B raw42981step0 raw42981step0Labels := by
      have hz : ∀ j, raw42981 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42981step0 = (fun i j => raw42981 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42981step0 raw42981; decide +kernel
      have hl : raw42981step0Labels = raw42981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42981 raw42981Labels permutation520 hz
    mixedMoment B raw42981step0 raw42981step0Labels = mixedMoment B raw42981step1 raw42981step1Labels := by
      have ha : raw42981step1 = (fun i j => raw42981step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42981step1 raw42981step0; decide +kernel
      have hl : raw42981step1Labels = raw42981step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42981step0 raw42981step0Labels permutation136 permutation5
    mixedMoment B raw42981step1 raw42981step1Labels = mixedMoment B raw42981step2 raw42981step2Labels := by
      have ha : raw42981step2 = raw42981step1 := by apply Matrix.ext; unfold raw42981step2 raw42981step1; decide +kernel
      have hl : raw42981step1Labels = labelEmbedding9 ∘ raw42981step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42981step1 raw42981step1Labels raw42981step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical42982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42982 raw42982Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw42982 raw42982Labels = mixedMoment B raw42982step0 raw42982step0Labels := by
      have ha : raw42982step0 = (fun i j => raw42982 (permutation610 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42982step0 raw42982; decide +kernel
      have hl : raw42982step0Labels = raw42982Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42982 raw42982Labels permutation610 permutation4
    mixedMoment B raw42982step0 raw42982step0Labels = mixedMoment B raw42982step1 raw42982step1Labels := by
      have ha : raw42982step1 = raw42982step0 := by apply Matrix.ext; unfold raw42982step1 raw42982step0; decide +kernel
      have hl : raw42982step0Labels = labelEmbedding1 ∘ raw42982step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42982step0 raw42982step0Labels raw42982step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3064 node3064Labels := by rfl

theorem canonical42983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42983 raw42983Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw42983 raw42983Labels = mixedMoment B raw42983step0 raw42983step0Labels := by
      have ha : raw42983step0 = (fun i j => raw42983 (permutation673 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42983step0 raw42983; decide +kernel
      have hl : raw42983step0Labels = raw42983Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42983 raw42983Labels permutation673 permutation5
    mixedMoment B raw42983step0 raw42983step0Labels = mixedMoment B raw42983step1 raw42983step1Labels := by
      have ha : raw42983step1 = raw42983step0 := by apply Matrix.ext; unfold raw42983step1 raw42983step0; decide +kernel
      have hl : raw42983step0Labels = labelEmbedding9 ∘ raw42983step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42983step0 raw42983step0Labels raw42983step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical42984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42984 raw42984Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw42984 raw42984Labels = mixedMoment B raw42984step0 raw42984step0Labels := by
      have ha : raw42984step0 = (fun i j => raw42984 (permutation434 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42984step0 raw42984; decide +kernel
      have hl : raw42984step0Labels = raw42984Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42984 raw42984Labels permutation434 permutation4
    mixedMoment B raw42984step0 raw42984step0Labels = mixedMoment B raw42984step1 raw42984step1Labels := by
      have ha : raw42984step1 = -raw42984step0 := by apply Matrix.ext; change ∀ i j, raw42984step1 i j = -(raw42984step0 i j); unfold raw42984step1 raw42984step0; decide +kernel
      have hl : raw42984step1Labels = raw42984step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42984step1 raw42984step1Labels = mixedMoment B raw42984step2 raw42984step2Labels := by
      have ha : raw42984step2 = raw42984step1 := by apply Matrix.ext; unfold raw42984step2 raw42984step1; decide +kernel
      have hl : raw42984step1Labels = labelEmbedding1 ∘ raw42984step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42984step1 raw42984step1Labels raw42984step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

theorem canonical42985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42985 raw42985Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw42985 raw42985Labels = mixedMoment B raw42985step0 raw42985step0Labels := by
      have ha : raw42985step0 = (fun i j => raw42985 (permutation673 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42985step0 raw42985; decide +kernel
      have hl : raw42985step0Labels = raw42985Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42985 raw42985Labels permutation673 permutation5
    mixedMoment B raw42985step0 raw42985step0Labels = mixedMoment B raw42985step1 raw42985step1Labels := by
      have ha : raw42985step1 = raw42985step0 := by apply Matrix.ext; unfold raw42985step1 raw42985step0; decide +kernel
      have hl : raw42985step0Labels = labelEmbedding9 ∘ raw42985step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42985step0 raw42985step0Labels raw42985step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical42986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42986 raw42986Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw42986 raw42986Labels = mixedMoment B raw42986step0 raw42986step0Labels := by
      have ha : raw42986step0 = (fun i j => raw42986 (permutation435 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42986step0 raw42986; decide +kernel
      have hl : raw42986step0Labels = raw42986Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42986 raw42986Labels permutation435 permutation4
    mixedMoment B raw42986step0 raw42986step0Labels = mixedMoment B raw42986step1 raw42986step1Labels := by
      have ha : raw42986step1 = -raw42986step0 := by apply Matrix.ext; change ∀ i j, raw42986step1 i j = -(raw42986step0 i j); unfold raw42986step1 raw42986step0; decide +kernel
      have hl : raw42986step1Labels = raw42986step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42986step1 raw42986step1Labels = mixedMoment B raw42986step2 raw42986step2Labels := by
      have ha : raw42986step2 = raw42986step1 := by apply Matrix.ext; unfold raw42986step2 raw42986step1; decide +kernel
      have hl : raw42986step1Labels = labelEmbedding1 ∘ raw42986step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42986step1 raw42986step1Labels raw42986step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

theorem canonical42987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42987 raw42987Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42987 raw42987Labels = mixedMoment B raw42987step0 raw42987step0Labels := by
      have ha : raw42987step0 = (fun i j => raw42987 (permutation435 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42987step0 raw42987; decide +kernel
      have hl : raw42987step0Labels = raw42987Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42987 raw42987Labels permutation435 permutation4
    mixedMoment B raw42987step0 raw42987step0Labels = mixedMoment B raw42987step1 raw42987step1Labels := by
      have ha : raw42987step1 = -raw42987step0 := by apply Matrix.ext; change ∀ i j, raw42987step1 i j = -(raw42987step0 i j); unfold raw42987step1 raw42987step0; decide +kernel
      have hl : raw42987step1Labels = raw42987step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42987step1 raw42987step1Labels = mixedMoment B raw42987step2 raw42987step2Labels := by
      have ha : raw42987step2 = raw42987step1 := by apply Matrix.ext; unfold raw42987step2 raw42987step1; decide +kernel
      have hl : raw42987step1Labels = labelEmbedding10 ∘ raw42987step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42987step1 raw42987step1Labels raw42987step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical42988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42988 raw42988Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw42988 raw42988Labels = mixedMoment B raw42988step0 raw42988step0Labels := by
      have ha : raw42988step0 = (fun i j => raw42988 (permutation534 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42988step0 raw42988; decide +kernel
      have hl : raw42988step0Labels = raw42988Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42988 raw42988Labels permutation534 permutation4
    mixedMoment B raw42988step0 raw42988step0Labels = mixedMoment B raw42988step1 raw42988step1Labels := by
      have ha : raw42988step1 = raw42988step0 := by apply Matrix.ext; unfold raw42988step1 raw42988step0; decide +kernel
      have hl : raw42988step0Labels = labelEmbedding1 ∘ raw42988step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42988step0 raw42988step0Labels raw42988step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2697 node2697Labels := by rfl

theorem canonical42989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42989 raw42989Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw42989 raw42989Labels = mixedMoment B raw42989step0 raw42989step0Labels := by
      have ha : raw42989step0 = (fun i j => raw42989 (permutation534 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42989step0 raw42989; decide +kernel
      have hl : raw42989step0Labels = raw42989Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42989 raw42989Labels permutation534 permutation4
    mixedMoment B raw42989step0 raw42989step0Labels = mixedMoment B raw42989step1 raw42989step1Labels := by
      have ha : raw42989step1 = raw42989step0 := by apply Matrix.ext; unfold raw42989step1 raw42989step0; decide +kernel
      have hl : raw42989step0Labels = labelEmbedding10 ∘ raw42989step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42989step0 raw42989step0Labels raw42989step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

theorem canonical42990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42990 raw42990Labels = mixedMoment B node3226 node3226Labels := by
  calc
    mixedMoment B raw42990 raw42990Labels = mixedMoment B raw42990step0 raw42990step0Labels := by
      have ha : raw42990step0 = (fun i j => raw42990 (permutation659 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42990step0 raw42990; decide +kernel
      have hl : raw42990step0Labels = raw42990Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42990 raw42990Labels permutation659 permutation2
    mixedMoment B raw42990step0 raw42990step0Labels = mixedMoment B raw42990step1 raw42990step1Labels := by
      have ha : raw42990step1 = -raw42990step0 := by apply Matrix.ext; change ∀ i j, raw42990step1 i j = -(raw42990step0 i j); unfold raw42990step1 raw42990step0; decide +kernel
      have hl : raw42990step1Labels = raw42990step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42990step1 raw42990step1Labels = mixedMoment B raw42990step2 raw42990step2Labels := by
      have ha : raw42990step2 = raw42990step1 := by apply Matrix.ext; unfold raw42990step2 raw42990step1; decide +kernel
      have hl : raw42990step1Labels = labelEmbedding1 ∘ raw42990step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42990step1 raw42990step1Labels raw42990step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3226 node3226Labels := by rfl

theorem canonical42991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42991 raw42991Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw42991 raw42991Labels = mixedMoment B raw42991step0 raw42991step0Labels := by
      have ha : raw42991step0 = (fun i j => raw42991 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42991step0 raw42991; decide +kernel
      have hl : raw42991step0Labels = raw42991Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42991 raw42991Labels permutation662 permutation3
    mixedMoment B raw42991step0 raw42991step0Labels = mixedMoment B raw42991step1 raw42991step1Labels := by
      have ha : raw42991step1 = -raw42991step0 := by apply Matrix.ext; change ∀ i j, raw42991step1 i j = -(raw42991step0 i j); unfold raw42991step1 raw42991step0; decide +kernel
      have hl : raw42991step1Labels = raw42991step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42991step1 raw42991step1Labels = mixedMoment B raw42991step2 raw42991step2Labels := by
      have ha : raw42991step2 = raw42991step1 := by apply Matrix.ext; unfold raw42991step2 raw42991step1; decide +kernel
      have hl : raw42991step1Labels = labelEmbedding7 ∘ raw42991step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42991step1 raw42991step1Labels raw42991step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

theorem canonical42992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42992 raw42992Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw42992 raw42992Labels = mixedMoment B raw42992step0 raw42992step0Labels := by
      have ha : raw42992step0 = (fun i j => raw42992 (permutation607 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42992step0 raw42992; decide +kernel
      have hl : raw42992step0Labels = raw42992Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42992 raw42992Labels permutation607 permutation4
    mixedMoment B raw42992step0 raw42992step0Labels = mixedMoment B raw42992step1 raw42992step1Labels := by
      have ha : raw42992step1 = raw42992step0 := by apply Matrix.ext; unfold raw42992step1 raw42992step0; decide +kernel
      have hl : raw42992step0Labels = labelEmbedding1 ∘ raw42992step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42992step0 raw42992step0Labels raw42992step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

theorem canonical42993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42993 raw42993Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw42993 raw42993Labels = mixedMoment B raw42993step0 raw42993step0Labels := by
      have ha : raw42993step0 = (fun i j => raw42993 (permutation611 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42993step0 raw42993; decide +kernel
      have hl : raw42993step0Labels = raw42993Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42993 raw42993Labels permutation611 permutation5
    mixedMoment B raw42993step0 raw42993step0Labels = mixedMoment B raw42993step1 raw42993step1Labels := by
      have ha : raw42993step1 = raw42993step0 := by apply Matrix.ext; unfold raw42993step1 raw42993step0; decide +kernel
      have hl : raw42993step0Labels = labelEmbedding9 ∘ raw42993step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42993step0 raw42993step0Labels raw42993step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical42994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42994 raw42994Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw42994 raw42994Labels = mixedMoment B raw42994step0 raw42994step0Labels := by
      have hz : ∀ j, raw42994 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42994step0 = (fun i j => raw42994 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42994step0 raw42994; decide +kernel
      have hl : raw42994step0Labels = raw42994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42994 raw42994Labels permutation434 hz
    mixedMoment B raw42994step0 raw42994step0Labels = mixedMoment B raw42994step1 raw42994step1Labels := by
      have ha : raw42994step1 = (fun i j => raw42994step0 (permutation136 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42994step1 raw42994step0; decide +kernel
      have hl : raw42994step1Labels = raw42994step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42994step0 raw42994step0Labels permutation136 permutation4
    mixedMoment B raw42994step1 raw42994step1Labels = mixedMoment B raw42994step2 raw42994step2Labels := by
      have ha : raw42994step2 = raw42994step1 := by apply Matrix.ext; unfold raw42994step2 raw42994step1; decide +kernel
      have hl : raw42994step1Labels = labelEmbedding1 ∘ raw42994step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42994step1 raw42994step1Labels raw42994step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

theorem canonical42995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42995 raw42995Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw42995 raw42995Labels = mixedMoment B raw42995step0 raw42995step0Labels := by
      have hz : ∀ j, raw42995 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42995step0 = (fun i j => raw42995 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42995step0 raw42995; decide +kernel
      have hl : raw42995step0Labels = raw42995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42995 raw42995Labels permutation434 hz
    mixedMoment B raw42995step0 raw42995step0Labels = mixedMoment B raw42995step1 raw42995step1Labels := by
      have ha : raw42995step1 = (fun i j => raw42995step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42995step1 raw42995step0; decide +kernel
      have hl : raw42995step1Labels = raw42995step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42995step0 raw42995step0Labels permutation104 permutation6
    _ = mixedMoment B node5270 node5270Labels := by rfl

theorem canonical42996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42996 raw42996Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw42996 raw42996Labels = mixedMoment B raw42996step0 raw42996step0Labels := by
      have hz : ∀ j, raw42996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42996step0 = (fun i j => raw42996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42996step0 raw42996; decide +kernel
      have hl : raw42996step0Labels = raw42996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42996 raw42996Labels permutation434 hz
    mixedMoment B raw42996step0 raw42996step0Labels = mixedMoment B raw42996step1 raw42996step1Labels := by
      have ha : raw42996step1 = (fun i j => raw42996step0 (permutation112 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42996step1 raw42996step0; decide +kernel
      have hl : raw42996step1Labels = raw42996step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42996step0 raw42996step0Labels permutation112 permutation4
    mixedMoment B raw42996step1 raw42996step1Labels = mixedMoment B raw42996step2 raw42996step2Labels := by
      have ha : raw42996step2 = raw42996step1 := by apply Matrix.ext; unfold raw42996step2 raw42996step1; decide +kernel
      have hl : raw42996step1Labels = labelEmbedding1 ∘ raw42996step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42996step1 raw42996step1Labels raw42996step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

theorem canonical42997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42997 raw42997Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw42997 raw42997Labels = mixedMoment B raw42997step0 raw42997step0Labels := by
      have hz : ∀ j, raw42997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42997step0 = (fun i j => raw42997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42997step0 raw42997; decide +kernel
      have hl : raw42997step0Labels = raw42997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42997 raw42997Labels permutation434 hz
    mixedMoment B raw42997step0 raw42997step0Labels = mixedMoment B raw42997step1 raw42997step1Labels := by
      have ha : raw42997step1 = (fun i j => raw42997step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42997step1 raw42997step0; decide +kernel
      have hl : raw42997step1Labels = raw42997step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42997step0 raw42997step0Labels permutation128 permutation6
    _ = mixedMoment B node4600 node4600Labels := by rfl

theorem canonical42998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42998 raw42998Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw42998 raw42998Labels = mixedMoment B raw42998step0 raw42998step0Labels := by
      have ha : raw42998step0 = (fun i j => raw42998 (permutation520 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42998step0 raw42998; decide +kernel
      have hl : raw42998step0Labels = raw42998Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42998 raw42998Labels permutation520 permutation4
    mixedMoment B raw42998step0 raw42998step0Labels = mixedMoment B raw42998step1 raw42998step1Labels := by
      have ha : raw42998step1 = -raw42998step0 := by apply Matrix.ext; change ∀ i j, raw42998step1 i j = -(raw42998step0 i j); unfold raw42998step1 raw42998step0; decide +kernel
      have hl : raw42998step1Labels = raw42998step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42998step1 raw42998step1Labels = mixedMoment B raw42998step2 raw42998step2Labels := by
      have ha : raw42998step2 = raw42998step1 := by apply Matrix.ext; unfold raw42998step2 raw42998step1; decide +kernel
      have hl : raw42998step1Labels = labelEmbedding1 ∘ raw42998step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42998step1 raw42998step1Labels raw42998step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

theorem canonical42999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42999 raw42999Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw42999 raw42999Labels = mixedMoment B raw42999step0 raw42999step0Labels := by
      have ha : raw42999step0 = (fun i j => raw42999 (permutation526 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42999step0 raw42999; decide +kernel
      have hl : raw42999step0Labels = raw42999Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42999 raw42999Labels permutation526 permutation6
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical43000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43000 raw43000Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw43000 raw43000Labels = mixedMoment B raw43000step0 raw43000step0Labels := by
      have ha : raw43000step0 = (fun i j => raw43000 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43000step0 raw43000; decide +kernel
      have hl : raw43000step0Labels = raw43000Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43000 raw43000Labels permutation590 permutation4
    mixedMoment B raw43000step0 raw43000step0Labels = mixedMoment B raw43000step1 raw43000step1Labels := by
      have ha : raw43000step1 = -raw43000step0 := by apply Matrix.ext; change ∀ i j, raw43000step1 i j = -(raw43000step0 i j); unfold raw43000step1 raw43000step0; decide +kernel
      have hl : raw43000step1Labels = raw43000step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43000step1 raw43000step1Labels = mixedMoment B raw43000step2 raw43000step2Labels := by
      have ha : raw43000step2 = raw43000step1 := by apply Matrix.ext; unfold raw43000step2 raw43000step1; decide +kernel
      have hl : raw43000step1Labels = labelEmbedding1 ∘ raw43000step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43000step1 raw43000step1Labels raw43000step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical43001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43001 raw43001Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw43001 raw43001Labels = mixedMoment B raw43001step0 raw43001step0Labels := by
      have ha : raw43001step0 = (fun i j => raw43001 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43001step0 raw43001; decide +kernel
      have hl : raw43001step0Labels = raw43001Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43001 raw43001Labels permutation590 permutation6
    _ = mixedMoment B node4599 node4599Labels := by rfl

theorem canonical43002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43002 raw43002Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw43002 raw43002Labels = mixedMoment B raw43002step0 raw43002step0Labels := by
      have ha : raw43002step0 = (fun i j => raw43002 (permutation591 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43002step0 raw43002; decide +kernel
      have hl : raw43002step0Labels = raw43002Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43002 raw43002Labels permutation591 permutation4
    mixedMoment B raw43002step0 raw43002step0Labels = mixedMoment B raw43002step1 raw43002step1Labels := by
      have ha : raw43002step1 = -raw43002step0 := by apply Matrix.ext; change ∀ i j, raw43002step1 i j = -(raw43002step0 i j); unfold raw43002step1 raw43002step0; decide +kernel
      have hl : raw43002step1Labels = raw43002step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43002step1 raw43002step1Labels = mixedMoment B raw43002step2 raw43002step2Labels := by
      have ha : raw43002step2 = raw43002step1 := by apply Matrix.ext; unfold raw43002step2 raw43002step1; decide +kernel
      have hl : raw43002step1Labels = labelEmbedding1 ∘ raw43002step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43002step1 raw43002step1Labels raw43002step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

theorem canonical43003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43003 raw43003Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw43003 raw43003Labels = mixedMoment B raw43003step0 raw43003step0Labels := by
      have ha : raw43003step0 = (fun i j => raw43003 (permutation599 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43003step0 raw43003; decide +kernel
      have hl : raw43003step0Labels = raw43003Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43003 raw43003Labels permutation599 permutation6
    _ = mixedMoment B node4589 node4589Labels := by rfl

theorem canonical43004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43004 raw43004Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw43004 raw43004Labels = mixedMoment B raw43004step0 raw43004step0Labels := by
      have ha : raw43004step0 = (fun i j => raw43004 (permutation443 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43004step0 raw43004; decide +kernel
      have hl : raw43004step0Labels = raw43004Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43004 raw43004Labels permutation443 permutation4
    mixedMoment B raw43004step0 raw43004step0Labels = mixedMoment B raw43004step1 raw43004step1Labels := by
      have ha : raw43004step1 = -raw43004step0 := by apply Matrix.ext; change ∀ i j, raw43004step1 i j = -(raw43004step0 i j); unfold raw43004step1 raw43004step0; decide +kernel
      have hl : raw43004step1Labels = raw43004step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43004step1 raw43004step1Labels = mixedMoment B raw43004step2 raw43004step2Labels := by
      have ha : raw43004step2 = raw43004step1 := by apply Matrix.ext; unfold raw43004step2 raw43004step1; decide +kernel
      have hl : raw43004step1Labels = labelEmbedding1 ∘ raw43004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43004step1 raw43004step1Labels raw43004step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3839 node3839Labels := by rfl

theorem canonical43005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43005 raw43005Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw43005 raw43005Labels = mixedMoment B raw43005step0 raw43005step0Labels := by
      have ha : raw43005step0 = (fun i j => raw43005 (permutation443 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43005step0 raw43005; decide +kernel
      have hl : raw43005step0Labels = raw43005Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43005 raw43005Labels permutation443 permutation4
    mixedMoment B raw43005step0 raw43005step0Labels = mixedMoment B raw43005step1 raw43005step1Labels := by
      have ha : raw43005step1 = -raw43005step0 := by apply Matrix.ext; change ∀ i j, raw43005step1 i j = -(raw43005step0 i j); unfold raw43005step1 raw43005step0; decide +kernel
      have hl : raw43005step1Labels = raw43005step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43005step1 raw43005step1Labels = mixedMoment B raw43005step2 raw43005step2Labels := by
      have ha : raw43005step2 = raw43005step1 := by apply Matrix.ext; unfold raw43005step2 raw43005step1; decide +kernel
      have hl : raw43005step1Labels = labelEmbedding10 ∘ raw43005step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43005step1 raw43005step1Labels raw43005step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical43006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43006 raw43006Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw43006 raw43006Labels = mixedMoment B raw43006step0 raw43006step0Labels := by
      have ha : raw43006step0 = (fun i j => raw43006 (permutation439 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43006step0 raw43006; decide +kernel
      have hl : raw43006step0Labels = raw43006Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43006 raw43006Labels permutation439 permutation4
    mixedMoment B raw43006step0 raw43006step0Labels = mixedMoment B raw43006step1 raw43006step1Labels := by
      have ha : raw43006step1 = -raw43006step0 := by apply Matrix.ext; change ∀ i j, raw43006step1 i j = -(raw43006step0 i j); unfold raw43006step1 raw43006step0; decide +kernel
      have hl : raw43006step1Labels = raw43006step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43006step1 raw43006step1Labels = mixedMoment B raw43006step2 raw43006step2Labels := by
      have ha : raw43006step2 = raw43006step1 := by apply Matrix.ext; unfold raw43006step2 raw43006step1; decide +kernel
      have hl : raw43006step1Labels = labelEmbedding1 ∘ raw43006step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43006step1 raw43006step1Labels raw43006step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

theorem canonical43007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43007 raw43007Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw43007 raw43007Labels = mixedMoment B raw43007step0 raw43007step0Labels := by
      have ha : raw43007step0 = (fun i j => raw43007 (permutation439 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43007step0 raw43007; decide +kernel
      have hl : raw43007step0Labels = raw43007Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43007 raw43007Labels permutation439 permutation4
    mixedMoment B raw43007step0 raw43007step0Labels = mixedMoment B raw43007step1 raw43007step1Labels := by
      have ha : raw43007step1 = -raw43007step0 := by apply Matrix.ext; change ∀ i j, raw43007step1 i j = -(raw43007step0 i j); unfold raw43007step1 raw43007step0; decide +kernel
      have hl : raw43007step1Labels = raw43007step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43007step1 raw43007step1Labels = mixedMoment B raw43007step2 raw43007step2Labels := by
      have ha : raw43007step2 = raw43007step1 := by apply Matrix.ext; unfold raw43007step2 raw43007step1; decide +kernel
      have hl : raw43007step1Labels = labelEmbedding10 ∘ raw43007step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43007step1 raw43007step1Labels raw43007step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2816 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2816) =
      Integer.Sparse.eval keyMomentRow2816 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2816).leftCharge (GramAssembly.key 2816).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3523) := by
    have ha : gramCharges (GramAssembly.key 2816).leftCharge (GramAssembly.key 2816).rightCharge = raw42944 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42944Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42944 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2816).leftCharge (GramAssembly.key 2816).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5139) := by
    have ha : gramCharges (GramAssembly.key 2816).leftCharge (GramAssembly.key 2816).rightCharge = raw42945 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42945Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42945 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2816).leftCharge (GramAssembly.key 2816).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2816).leftCharge (GramAssembly.key 2816).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2816, Integer.Sparse.eval] <;> ring

theorem keyMoment2817 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2817) =
      Integer.Sparse.eval keyMomentRow2817 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2817).leftCharge (GramAssembly.key 2817).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3842) := by
    have ha : gramCharges (GramAssembly.key 2817).leftCharge (GramAssembly.key 2817).rightCharge = raw42946 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42946Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42946 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2817).leftCharge (GramAssembly.key 2817).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5419) := by
    have ha : gramCharges (GramAssembly.key 2817).leftCharge (GramAssembly.key 2817).rightCharge = raw42947 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42947Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42947 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2817).leftCharge (GramAssembly.key 2817).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2817).leftCharge (GramAssembly.key 2817).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2817, Integer.Sparse.eval] <;> ring

theorem keyMoment2818 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2818) =
      Integer.Sparse.eval keyMomentRow2818 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2818).leftCharge (GramAssembly.key 2818).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3542) := by
    have ha : gramCharges (GramAssembly.key 2818).leftCharge (GramAssembly.key 2818).rightCharge = raw42948 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42948Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42948 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2818).leftCharge (GramAssembly.key 2818).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5189) := by
    have ha : gramCharges (GramAssembly.key 2818).leftCharge (GramAssembly.key 2818).rightCharge = raw42949 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42949Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42949 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2818).leftCharge (GramAssembly.key 2818).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2818).leftCharge (GramAssembly.key 2818).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2818, Integer.Sparse.eval] <;> ring

theorem keyMoment2819 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2819) =
      Integer.Sparse.eval keyMomentRow2819 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2819).leftCharge (GramAssembly.key 2819).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 0) := by
    have ha : gramCharges (GramAssembly.key 2819).leftCharge (GramAssembly.key 2819).rightCharge = raw42950 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42950Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42950 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2819).leftCharge (GramAssembly.key 2819).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4083) := by
    have ha : gramCharges (GramAssembly.key 2819).leftCharge (GramAssembly.key 2819).rightCharge = raw42951 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42951Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42951 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2819).leftCharge (GramAssembly.key 2819).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2819).leftCharge (GramAssembly.key 2819).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2819, Integer.Sparse.eval] <;> ring

theorem keyMoment2820 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2820) =
      Integer.Sparse.eval keyMomentRow2820 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2820).leftCharge (GramAssembly.key 2820).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3111) := by
    have ha : gramCharges (GramAssembly.key 2820).leftCharge (GramAssembly.key 2820).rightCharge = raw42952 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42952Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42952 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2820).leftCharge (GramAssembly.key 2820).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5273) := by
    have ha : gramCharges (GramAssembly.key 2820).leftCharge (GramAssembly.key 2820).rightCharge = raw42953 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42953Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42953 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2820).leftCharge (GramAssembly.key 2820).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2820).leftCharge (GramAssembly.key 2820).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2820, Integer.Sparse.eval] <;> ring

theorem keyMoment2821 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2821) =
      Integer.Sparse.eval keyMomentRow2821 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2821).leftCharge (GramAssembly.key 2821).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3) := by
    have ha : gramCharges (GramAssembly.key 2821).leftCharge (GramAssembly.key 2821).rightCharge = raw42954 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42954Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42954 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2821).leftCharge (GramAssembly.key 2821).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4091) := by
    have ha : gramCharges (GramAssembly.key 2821).leftCharge (GramAssembly.key 2821).rightCharge = raw42955 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42955Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42955 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2821).leftCharge (GramAssembly.key 2821).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2821).leftCharge (GramAssembly.key 2821).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2821, Integer.Sparse.eval] <;> ring

theorem keyMoment2822 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2822) =
      Integer.Sparse.eval keyMomentRow2822 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2822).leftCharge (GramAssembly.key 2822).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4034) := by
    have ha : gramCharges (GramAssembly.key 2822).leftCharge (GramAssembly.key 2822).rightCharge = raw42956 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42956Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42956 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2822).leftCharge (GramAssembly.key 2822).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5427) := by
    have ha : gramCharges (GramAssembly.key 2822).leftCharge (GramAssembly.key 2822).rightCharge = raw42957 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42957Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42957 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2822).leftCharge (GramAssembly.key 2822).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2822).leftCharge (GramAssembly.key 2822).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2822, Integer.Sparse.eval] <;> ring

theorem keyMoment2823 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2823) =
      Integer.Sparse.eval keyMomentRow2823 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2823).leftCharge (GramAssembly.key 2823).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3855) := by
    have ha : gramCharges (GramAssembly.key 2823).leftCharge (GramAssembly.key 2823).rightCharge = raw42958 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42958Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42958 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2823).leftCharge (GramAssembly.key 2823).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5437) := by
    have ha : gramCharges (GramAssembly.key 2823).leftCharge (GramAssembly.key 2823).rightCharge = raw42959 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42959Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42959 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2823).leftCharge (GramAssembly.key 2823).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2823).leftCharge (GramAssembly.key 2823).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2823, Integer.Sparse.eval] <;> ring

theorem keyMoment2824 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2824) =
      Integer.Sparse.eval keyMomentRow2824 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2824).leftCharge (GramAssembly.key 2824).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3228) := by
    have ha : gramCharges (GramAssembly.key 2824).leftCharge (GramAssembly.key 2824).rightCharge = raw42960 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42960Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42960 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2824).leftCharge (GramAssembly.key 2824).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4893) := by
    have ha : gramCharges (GramAssembly.key 2824).leftCharge (GramAssembly.key 2824).rightCharge = raw42961 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42961Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42961 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2824).leftCharge (GramAssembly.key 2824).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2824).leftCharge (GramAssembly.key 2824).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2824, Integer.Sparse.eval] <;> ring

theorem keyMoment2825 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2825) =
      Integer.Sparse.eval keyMomentRow2825 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2825).leftCharge (GramAssembly.key 2825).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3087) := by
    have ha : gramCharges (GramAssembly.key 2825).leftCharge (GramAssembly.key 2825).rightCharge = raw42962 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42962Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42962 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2825).leftCharge (GramAssembly.key 2825).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5257) := by
    have ha : gramCharges (GramAssembly.key 2825).leftCharge (GramAssembly.key 2825).rightCharge = raw42963 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42963Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42963 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2825).leftCharge (GramAssembly.key 2825).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2825).leftCharge (GramAssembly.key 2825).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2825, Integer.Sparse.eval] <;> ring

theorem keyMoment2826 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2826) =
      Integer.Sparse.eval keyMomentRow2826 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2826).leftCharge (GramAssembly.key 2826).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4038) := by
    have ha : gramCharges (GramAssembly.key 2826).leftCharge (GramAssembly.key 2826).rightCharge = raw42964 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42964Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42964 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2826).leftCharge (GramAssembly.key 2826).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5408) := by
    have ha : gramCharges (GramAssembly.key 2826).leftCharge (GramAssembly.key 2826).rightCharge = raw42965 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42965Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42965 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2826).leftCharge (GramAssembly.key 2826).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2826).leftCharge (GramAssembly.key 2826).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2826, Integer.Sparse.eval] <;> ring

theorem keyMoment2827 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2827) =
      Integer.Sparse.eval keyMomentRow2827 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2827).leftCharge (GramAssembly.key 2827).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3099) := by
    have ha : gramCharges (GramAssembly.key 2827).leftCharge (GramAssembly.key 2827).rightCharge = raw42966 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42966Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42966 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2827).leftCharge (GramAssembly.key 2827).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5290) := by
    have ha : gramCharges (GramAssembly.key 2827).leftCharge (GramAssembly.key 2827).rightCharge = raw42967 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42967Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42967 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2827).leftCharge (GramAssembly.key 2827).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2827).leftCharge (GramAssembly.key 2827).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2827, Integer.Sparse.eval] <;> ring

theorem keyMoment2828 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2828) =
      Integer.Sparse.eval keyMomentRow2828 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2828).leftCharge (GramAssembly.key 2828).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4026) := by
    have ha : gramCharges (GramAssembly.key 2828).leftCharge (GramAssembly.key 2828).rightCharge = raw42968 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42968Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42968 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2828).leftCharge (GramAssembly.key 2828).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5431) := by
    have ha : gramCharges (GramAssembly.key 2828).leftCharge (GramAssembly.key 2828).rightCharge = raw42969 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42969Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42969 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2828).leftCharge (GramAssembly.key 2828).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2828).leftCharge (GramAssembly.key 2828).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2828, Integer.Sparse.eval] <;> ring

theorem keyMoment2829 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2829) =
      Integer.Sparse.eval keyMomentRow2829 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2829).leftCharge (GramAssembly.key 2829).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3539) := by
    have ha : gramCharges (GramAssembly.key 2829).leftCharge (GramAssembly.key 2829).rightCharge = raw42970 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42970Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42970 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2829).leftCharge (GramAssembly.key 2829).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2829).leftCharge (GramAssembly.key 2829).rightCharge = raw42971 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42971Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42971 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2829).leftCharge (GramAssembly.key 2829).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2829).leftCharge (GramAssembly.key 2829).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2829, Integer.Sparse.eval] <;> ring

theorem keyMoment2830 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2830) =
      Integer.Sparse.eval keyMomentRow2830 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2830).leftCharge (GramAssembly.key 2830).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4026) := by
    have ha : gramCharges (GramAssembly.key 2830).leftCharge (GramAssembly.key 2830).rightCharge = raw42972 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42972Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42972 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2830).leftCharge (GramAssembly.key 2830).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5431) := by
    have ha : gramCharges (GramAssembly.key 2830).leftCharge (GramAssembly.key 2830).rightCharge = raw42973 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42973Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42973 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2830).leftCharge (GramAssembly.key 2830).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2830).leftCharge (GramAssembly.key 2830).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2830, Integer.Sparse.eval] <;> ring

theorem keyMoment2831 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2831) =
      Integer.Sparse.eval keyMomentRow2831 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2831).leftCharge (GramAssembly.key 2831).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4028) := by
    have ha : gramCharges (GramAssembly.key 2831).leftCharge (GramAssembly.key 2831).rightCharge = raw42974 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42974Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42974 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2831).leftCharge (GramAssembly.key 2831).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5448) := by
    have ha : gramCharges (GramAssembly.key 2831).leftCharge (GramAssembly.key 2831).rightCharge = raw42975 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42975Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42975 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2831).leftCharge (GramAssembly.key 2831).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2831).leftCharge (GramAssembly.key 2831).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2831, Integer.Sparse.eval] <;> ring

theorem keyMoment2832 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2832) =
      Integer.Sparse.eval keyMomentRow2832 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2832).leftCharge (GramAssembly.key 2832).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3539) := by
    have ha : gramCharges (GramAssembly.key 2832).leftCharge (GramAssembly.key 2832).rightCharge = raw42976 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42976Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42976 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2832).leftCharge (GramAssembly.key 2832).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2832).leftCharge (GramAssembly.key 2832).rightCharge = raw42977 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42977Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42977 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2832).leftCharge (GramAssembly.key 2832).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2832).leftCharge (GramAssembly.key 2832).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2832, Integer.Sparse.eval] <;> ring

theorem keyMoment2833 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2833) =
      Integer.Sparse.eval keyMomentRow2833 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2833).leftCharge (GramAssembly.key 2833).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3543) := by
    have ha : gramCharges (GramAssembly.key 2833).leftCharge (GramAssembly.key 2833).rightCharge = raw42978 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42978Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42978 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2833).leftCharge (GramAssembly.key 2833).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5252) := by
    have ha : gramCharges (GramAssembly.key 2833).leftCharge (GramAssembly.key 2833).rightCharge = raw42979 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42979Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42979 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2833).leftCharge (GramAssembly.key 2833).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2833).leftCharge (GramAssembly.key 2833).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2833, Integer.Sparse.eval] <;> ring

theorem keyMoment2834 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2834) =
      Integer.Sparse.eval keyMomentRow2834 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2834).leftCharge (GramAssembly.key 2834).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3223) := by
    have ha : gramCharges (GramAssembly.key 2834).leftCharge (GramAssembly.key 2834).rightCharge = raw42980 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42980Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42980 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2834).leftCharge (GramAssembly.key 2834).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4889) := by
    have ha : gramCharges (GramAssembly.key 2834).leftCharge (GramAssembly.key 2834).rightCharge = raw42981 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42981Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42981 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2834).leftCharge (GramAssembly.key 2834).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2834).leftCharge (GramAssembly.key 2834).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2834, Integer.Sparse.eval] <;> ring

theorem keyMoment2835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2835) =
      Integer.Sparse.eval keyMomentRow2835 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2835).leftCharge (GramAssembly.key 2835).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3064) := by
    have ha : gramCharges (GramAssembly.key 2835).leftCharge (GramAssembly.key 2835).rightCharge = raw42982 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42982Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42982 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2835).leftCharge (GramAssembly.key 2835).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2835).leftCharge (GramAssembly.key 2835).rightCharge = raw42983 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42983Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42983 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2835).leftCharge (GramAssembly.key 2835).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2835).leftCharge (GramAssembly.key 2835).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2835, Integer.Sparse.eval] <;> ring

theorem keyMoment2836 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2836) =
      Integer.Sparse.eval keyMomentRow2836 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2836).leftCharge (GramAssembly.key 2836).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3847) := by
    have ha : gramCharges (GramAssembly.key 2836).leftCharge (GramAssembly.key 2836).rightCharge = raw42984 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42984Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42984 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2836).leftCharge (GramAssembly.key 2836).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5406) := by
    have ha : gramCharges (GramAssembly.key 2836).leftCharge (GramAssembly.key 2836).rightCharge = raw42985 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42985Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42985 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2836).leftCharge (GramAssembly.key 2836).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2836).leftCharge (GramAssembly.key 2836).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2836, Integer.Sparse.eval] <;> ring

theorem keyMoment2837 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2837) =
      Integer.Sparse.eval keyMomentRow2837 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2837).leftCharge (GramAssembly.key 2837).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3846) := by
    have ha : gramCharges (GramAssembly.key 2837).leftCharge (GramAssembly.key 2837).rightCharge = raw42986 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42986Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42986 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2837).leftCharge (GramAssembly.key 2837).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2837).leftCharge (GramAssembly.key 2837).rightCharge = raw42987 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42987Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42987 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2837).leftCharge (GramAssembly.key 2837).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2837).leftCharge (GramAssembly.key 2837).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2837, Integer.Sparse.eval] <;> ring

theorem keyMoment2838 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2838) =
      Integer.Sparse.eval keyMomentRow2838 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2838).leftCharge (GramAssembly.key 2838).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2697) := by
    have ha : gramCharges (GramAssembly.key 2838).leftCharge (GramAssembly.key 2838).rightCharge = raw42988 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42988Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42988 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2838).leftCharge (GramAssembly.key 2838).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5243) := by
    have ha : gramCharges (GramAssembly.key 2838).leftCharge (GramAssembly.key 2838).rightCharge = raw42989 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42989Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42989 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2838).leftCharge (GramAssembly.key 2838).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2838).leftCharge (GramAssembly.key 2838).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2838, Integer.Sparse.eval] <;> ring

theorem keyMoment2839 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2839) =
      Integer.Sparse.eval keyMomentRow2839 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2839).leftCharge (GramAssembly.key 2839).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3226) := by
    have ha : gramCharges (GramAssembly.key 2839).leftCharge (GramAssembly.key 2839).rightCharge = raw42990 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42990Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42990 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2839).leftCharge (GramAssembly.key 2839).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4887) := by
    have ha : gramCharges (GramAssembly.key 2839).leftCharge (GramAssembly.key 2839).rightCharge = raw42991 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42991Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42991 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2839).leftCharge (GramAssembly.key 2839).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2839).leftCharge (GramAssembly.key 2839).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2839, Integer.Sparse.eval] <;> ring

theorem keyMoment2840 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2840) =
      Integer.Sparse.eval keyMomentRow2840 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2840).leftCharge (GramAssembly.key 2840).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3074) := by
    have ha : gramCharges (GramAssembly.key 2840).leftCharge (GramAssembly.key 2840).rightCharge = raw42992 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42992Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42992 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2840).leftCharge (GramAssembly.key 2840).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5281) := by
    have ha : gramCharges (GramAssembly.key 2840).leftCharge (GramAssembly.key 2840).rightCharge = raw42993 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42993Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42993 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2840).leftCharge (GramAssembly.key 2840).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2840).leftCharge (GramAssembly.key 2840).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2840, Integer.Sparse.eval] <;> ring

theorem keyMoment2841 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2841) =
      Integer.Sparse.eval keyMomentRow2841 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2841).leftCharge (GramAssembly.key 2841).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3075) := by
    have ha : gramCharges (GramAssembly.key 2841).leftCharge (GramAssembly.key 2841).rightCharge = raw42994 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42994Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42994 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2841).leftCharge (GramAssembly.key 2841).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5270) := by
    have ha : gramCharges (GramAssembly.key 2841).leftCharge (GramAssembly.key 2841).rightCharge = raw42995 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42995Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42995 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2841).leftCharge (GramAssembly.key 2841).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2841).leftCharge (GramAssembly.key 2841).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2841, Integer.Sparse.eval] <;> ring

theorem keyMoment2842 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2842) =
      Integer.Sparse.eval keyMomentRow2842 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2842).leftCharge (GramAssembly.key 2842).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2702) := by
    have ha : gramCharges (GramAssembly.key 2842).leftCharge (GramAssembly.key 2842).rightCharge = raw42996 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42996Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42996 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2842).leftCharge (GramAssembly.key 2842).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4600) := by
    have ha : gramCharges (GramAssembly.key 2842).leftCharge (GramAssembly.key 2842).rightCharge = raw42997 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42997Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42997 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2842).leftCharge (GramAssembly.key 2842).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2842).leftCharge (GramAssembly.key 2842).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2842, Integer.Sparse.eval] <;> ring

theorem keyMoment2843 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2843) =
      Integer.Sparse.eval keyMomentRow2843 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2843).leftCharge (GramAssembly.key 2843).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3526) := by
    have ha : gramCharges (GramAssembly.key 2843).leftCharge (GramAssembly.key 2843).rightCharge = raw42998 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42998Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42998 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2843).leftCharge (GramAssembly.key 2843).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2843).leftCharge (GramAssembly.key 2843).rightCharge = raw42999 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42999Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42999 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2843).leftCharge (GramAssembly.key 2843).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2843).leftCharge (GramAssembly.key 2843).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2843, Integer.Sparse.eval] <;> ring

theorem keyMoment2844 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2844) =
      Integer.Sparse.eval keyMomentRow2844 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2844).leftCharge (GramAssembly.key 2844).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3289) := by
    have ha : gramCharges (GramAssembly.key 2844).leftCharge (GramAssembly.key 2844).rightCharge = raw43000 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43000Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43000 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2844).leftCharge (GramAssembly.key 2844).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4599) := by
    have ha : gramCharges (GramAssembly.key 2844).leftCharge (GramAssembly.key 2844).rightCharge = raw43001 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43001Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43001 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2844).leftCharge (GramAssembly.key 2844).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2844).leftCharge (GramAssembly.key 2844).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2844, Integer.Sparse.eval] <;> ring

theorem keyMoment2845 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2845) =
      Integer.Sparse.eval keyMomentRow2845 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2845).leftCharge (GramAssembly.key 2845).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3288) := by
    have ha : gramCharges (GramAssembly.key 2845).leftCharge (GramAssembly.key 2845).rightCharge = raw43002 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43002Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43002 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2845).leftCharge (GramAssembly.key 2845).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4589) := by
    have ha : gramCharges (GramAssembly.key 2845).leftCharge (GramAssembly.key 2845).rightCharge = raw43003 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43003Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43003 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2845).leftCharge (GramAssembly.key 2845).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2845).leftCharge (GramAssembly.key 2845).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2845, Integer.Sparse.eval] <;> ring

theorem keyMoment2846 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2846) =
      Integer.Sparse.eval keyMomentRow2846 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2846).leftCharge (GramAssembly.key 2846).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3839) := by
    have ha : gramCharges (GramAssembly.key 2846).leftCharge (GramAssembly.key 2846).rightCharge = raw43004 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43004Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43004 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2846).leftCharge (GramAssembly.key 2846).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2846).leftCharge (GramAssembly.key 2846).rightCharge = raw43005 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43005Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43005 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2846).leftCharge (GramAssembly.key 2846).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2846).leftCharge (GramAssembly.key 2846).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2846, Integer.Sparse.eval] <;> ring

theorem keyMoment2847 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2847) =
      Integer.Sparse.eval keyMomentRow2847 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2847).leftCharge (GramAssembly.key 2847).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3848) := by
    have ha : gramCharges (GramAssembly.key 2847).leftCharge (GramAssembly.key 2847).rightCharge = raw43006 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43006Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43006 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2847).leftCharge (GramAssembly.key 2847).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2847).leftCharge (GramAssembly.key 2847).rightCharge = raw43007 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43007Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43007 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2847).leftCharge (GramAssembly.key 2847).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2847).leftCharge (GramAssembly.key 2847).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2847, Integer.Sparse.eval] <;> ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2816 : keyMomentRows (2816 : Fin 2886) =
    keyMomentRow2816 := by decide +kernel

theorem keyMomentRowsAt2817 : keyMomentRows (2817 : Fin 2886) =
    keyMomentRow2817 := by decide +kernel

theorem keyMomentRowsAt2818 : keyMomentRows (2818 : Fin 2886) =
    keyMomentRow2818 := by decide +kernel

theorem keyMomentRowsAt2819 : keyMomentRows (2819 : Fin 2886) =
    keyMomentRow2819 := by decide +kernel

theorem keyMomentRowsAt2820 : keyMomentRows (2820 : Fin 2886) =
    keyMomentRow2820 := by decide +kernel

theorem keyMomentRowsAt2821 : keyMomentRows (2821 : Fin 2886) =
    keyMomentRow2821 := by decide +kernel

theorem keyMomentRowsAt2822 : keyMomentRows (2822 : Fin 2886) =
    keyMomentRow2822 := by decide +kernel

theorem keyMomentRowsAt2823 : keyMomentRows (2823 : Fin 2886) =
    keyMomentRow2823 := by decide +kernel

theorem keyMomentRowsAt2824 : keyMomentRows (2824 : Fin 2886) =
    keyMomentRow2824 := by decide +kernel

theorem keyMomentRowsAt2825 : keyMomentRows (2825 : Fin 2886) =
    keyMomentRow2825 := by decide +kernel

theorem keyMomentRowsAt2826 : keyMomentRows (2826 : Fin 2886) =
    keyMomentRow2826 := by decide +kernel

theorem keyMomentRowsAt2827 : keyMomentRows (2827 : Fin 2886) =
    keyMomentRow2827 := by decide +kernel

theorem keyMomentRowsAt2828 : keyMomentRows (2828 : Fin 2886) =
    keyMomentRow2828 := by decide +kernel

theorem keyMomentRowsAt2829 : keyMomentRows (2829 : Fin 2886) =
    keyMomentRow2829 := by decide +kernel

theorem keyMomentRowsAt2830 : keyMomentRows (2830 : Fin 2886) =
    keyMomentRow2830 := by decide +kernel

theorem keyMomentRowsAt2831 : keyMomentRows (2831 : Fin 2886) =
    keyMomentRow2831 := by decide +kernel

theorem keyMomentRowsAt2832 : keyMomentRows (2832 : Fin 2886) =
    keyMomentRow2832 := by decide +kernel

theorem keyMomentRowsAt2833 : keyMomentRows (2833 : Fin 2886) =
    keyMomentRow2833 := by decide +kernel

theorem keyMomentRowsAt2834 : keyMomentRows (2834 : Fin 2886) =
    keyMomentRow2834 := by decide +kernel

theorem keyMomentRowsAt2835 : keyMomentRows (2835 : Fin 2886) =
    keyMomentRow2835 := by decide +kernel

theorem keyMomentRowsAt2836 : keyMomentRows (2836 : Fin 2886) =
    keyMomentRow2836 := by decide +kernel

theorem keyMomentRowsAt2837 : keyMomentRows (2837 : Fin 2886) =
    keyMomentRow2837 := by decide +kernel

theorem keyMomentRowsAt2838 : keyMomentRows (2838 : Fin 2886) =
    keyMomentRow2838 := by decide +kernel

theorem keyMomentRowsAt2839 : keyMomentRows (2839 : Fin 2886) =
    keyMomentRow2839 := by decide +kernel

theorem keyMomentRowsAt2840 : keyMomentRows (2840 : Fin 2886) =
    keyMomentRow2840 := by decide +kernel

theorem keyMomentRowsAt2841 : keyMomentRows (2841 : Fin 2886) =
    keyMomentRow2841 := by decide +kernel

theorem keyMomentRowsAt2842 : keyMomentRows (2842 : Fin 2886) =
    keyMomentRow2842 := by decide +kernel

theorem keyMomentRowsAt2843 : keyMomentRows (2843 : Fin 2886) =
    keyMomentRow2843 := by decide +kernel

theorem keyMomentRowsAt2844 : keyMomentRows (2844 : Fin 2886) =
    keyMomentRow2844 := by decide +kernel

theorem keyMomentRowsAt2845 : keyMomentRows (2845 : Fin 2886) =
    keyMomentRow2845 := by decide +kernel

theorem keyMomentRowsAt2846 : keyMomentRows (2846 : Fin 2886) =
    keyMomentRow2846 := by decide +kernel

theorem keyMomentRowsAt2847 : keyMomentRows (2847 : Fin 2886) =
    keyMomentRow2847 := by decide +kernel

theorem keyMomentChunkSound88_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 88) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2816 ∨ k.val = 2817 ∨ k.val = 2818 ∨ k.val = 2819 ∨ k.val = 2820 ∨ k.val = 2821 ∨ k.val = 2822 ∨ k.val = 2823 ∨ k.val = 2824 ∨ k.val = 2825 ∨ k.val = 2826 ∨ k.val = 2827 ∨ k.val = 2828 ∨ k.val = 2829 ∨ k.val = 2830 ∨ k.val = 2831 ∨ k.val = 2832 ∨ k.val = 2833 ∨ k.val = 2834 ∨ k.val = 2835 ∨ k.val = 2836 ∨ k.val = 2837 ∨ k.val = 2838 ∨ k.val = 2839 ∨ k.val = 2840 ∨ k.val = 2841 ∨ k.val = 2842 ∨ k.val = 2843 ∨ k.val = 2844 ∨ k.val = 2845 ∨ k.val = 2846 ∨ k.val = 2847 := by omega
  rcases heq with h2816 | h2817 | h2818 | h2819 | h2820 | h2821 | h2822 | h2823 | h2824 | h2825 | h2826 | h2827 | h2828 | h2829 | h2830 | h2831 | h2832 | h2833 | h2834 | h2835 | h2836 | h2837 | h2838 | h2839 | h2840 | h2841 | h2842 | h2843 | h2844 | h2845 | h2846 | h2847
  · have he : k = (2816 : Fin 2886) := Fin.ext h2816
    subst k
    rw [keyMomentRowsAt2816]
    exact keyMoment2816 B hB
  · have he : k = (2817 : Fin 2886) := Fin.ext h2817
    subst k
    rw [keyMomentRowsAt2817]
    exact keyMoment2817 B hB
  · have he : k = (2818 : Fin 2886) := Fin.ext h2818
    subst k
    rw [keyMomentRowsAt2818]
    exact keyMoment2818 B hB
  · have he : k = (2819 : Fin 2886) := Fin.ext h2819
    subst k
    rw [keyMomentRowsAt2819]
    exact keyMoment2819 B hB
  · have he : k = (2820 : Fin 2886) := Fin.ext h2820
    subst k
    rw [keyMomentRowsAt2820]
    exact keyMoment2820 B hB
  · have he : k = (2821 : Fin 2886) := Fin.ext h2821
    subst k
    rw [keyMomentRowsAt2821]
    exact keyMoment2821 B hB
  · have he : k = (2822 : Fin 2886) := Fin.ext h2822
    subst k
    rw [keyMomentRowsAt2822]
    exact keyMoment2822 B hB
  · have he : k = (2823 : Fin 2886) := Fin.ext h2823
    subst k
    rw [keyMomentRowsAt2823]
    exact keyMoment2823 B hB
  · have he : k = (2824 : Fin 2886) := Fin.ext h2824
    subst k
    rw [keyMomentRowsAt2824]
    exact keyMoment2824 B hB
  · have he : k = (2825 : Fin 2886) := Fin.ext h2825
    subst k
    rw [keyMomentRowsAt2825]
    exact keyMoment2825 B hB
  · have he : k = (2826 : Fin 2886) := Fin.ext h2826
    subst k
    rw [keyMomentRowsAt2826]
    exact keyMoment2826 B hB
  · have he : k = (2827 : Fin 2886) := Fin.ext h2827
    subst k
    rw [keyMomentRowsAt2827]
    exact keyMoment2827 B hB
  · have he : k = (2828 : Fin 2886) := Fin.ext h2828
    subst k
    rw [keyMomentRowsAt2828]
    exact keyMoment2828 B hB
  · have he : k = (2829 : Fin 2886) := Fin.ext h2829
    subst k
    rw [keyMomentRowsAt2829]
    exact keyMoment2829 B hB
  · have he : k = (2830 : Fin 2886) := Fin.ext h2830
    subst k
    rw [keyMomentRowsAt2830]
    exact keyMoment2830 B hB
  · have he : k = (2831 : Fin 2886) := Fin.ext h2831
    subst k
    rw [keyMomentRowsAt2831]
    exact keyMoment2831 B hB
  · have he : k = (2832 : Fin 2886) := Fin.ext h2832
    subst k
    rw [keyMomentRowsAt2832]
    exact keyMoment2832 B hB
  · have he : k = (2833 : Fin 2886) := Fin.ext h2833
    subst k
    rw [keyMomentRowsAt2833]
    exact keyMoment2833 B hB
  · have he : k = (2834 : Fin 2886) := Fin.ext h2834
    subst k
    rw [keyMomentRowsAt2834]
    exact keyMoment2834 B hB
  · have he : k = (2835 : Fin 2886) := Fin.ext h2835
    subst k
    rw [keyMomentRowsAt2835]
    exact keyMoment2835 B hB
  · have he : k = (2836 : Fin 2886) := Fin.ext h2836
    subst k
    rw [keyMomentRowsAt2836]
    exact keyMoment2836 B hB
  · have he : k = (2837 : Fin 2886) := Fin.ext h2837
    subst k
    rw [keyMomentRowsAt2837]
    exact keyMoment2837 B hB
  · have he : k = (2838 : Fin 2886) := Fin.ext h2838
    subst k
    rw [keyMomentRowsAt2838]
    exact keyMoment2838 B hB
  · have he : k = (2839 : Fin 2886) := Fin.ext h2839
    subst k
    rw [keyMomentRowsAt2839]
    exact keyMoment2839 B hB
  · have he : k = (2840 : Fin 2886) := Fin.ext h2840
    subst k
    rw [keyMomentRowsAt2840]
    exact keyMoment2840 B hB
  · have he : k = (2841 : Fin 2886) := Fin.ext h2841
    subst k
    rw [keyMomentRowsAt2841]
    exact keyMoment2841 B hB
  · have he : k = (2842 : Fin 2886) := Fin.ext h2842
    subst k
    rw [keyMomentRowsAt2842]
    exact keyMoment2842 B hB
  · have he : k = (2843 : Fin 2886) := Fin.ext h2843
    subst k
    rw [keyMomentRowsAt2843]
    exact keyMoment2843 B hB
  · have he : k = (2844 : Fin 2886) := Fin.ext h2844
    subst k
    rw [keyMomentRowsAt2844]
    exact keyMoment2844 B hB
  · have he : k = (2845 : Fin 2886) := Fin.ext h2845
    subst k
    rw [keyMomentRowsAt2845]
    exact keyMoment2845 B hB
  · have he : k = (2846 : Fin 2886) := Fin.ext h2846
    subst k
    rw [keyMomentRowsAt2846]
    exact keyMoment2846 B hB
  · have he : k = (2847 : Fin 2886) := Fin.ext h2847
    subst k
    rw [keyMomentRowsAt2847]
    exact keyMoment2847 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound88_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound88_e_oai
