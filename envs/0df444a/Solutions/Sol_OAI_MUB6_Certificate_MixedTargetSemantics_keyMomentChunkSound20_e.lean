-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound20_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:48:20.880206+00:00
-- url     : https://prove2.me/submissions/61299d97-3dd5-422b-aedb-d647ba6acf7c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E111
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical313
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40088 raw40088Labels = mixedMoment B node479 node479Labels := by
  calc
    mixedMoment B raw40088 raw40088Labels = mixedMoment B raw40088step0 raw40088step0Labels := by
      have ha : raw40088step0 = (fun i j => raw40088 (permutation511 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40088step0 raw40088; decide +kernel
      have hl : raw40088step0Labels = raw40088Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40088 raw40088Labels permutation511 permutation4
    _ = mixedMoment B node479 node479Labels := by rfl

theorem canonical40089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40089 raw40089Labels = mixedMoment B node5507 node5507Labels := by
  calc
    mixedMoment B raw40089 raw40089Labels = mixedMoment B raw40089step0 raw40089step0Labels := by
      have hz : ∀ j, raw40089 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40089step0 = (fun i j => raw40089 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40089step0 raw40089; decide +kernel
      have hl : raw40089step0Labels = raw40089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40089 raw40089Labels permutation520 hz
    mixedMoment B raw40089step0 raw40089step0Labels = mixedMoment B raw40089step1 raw40089step1Labels := by
      have hz : ∀ j, raw40089step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40089step1 = (fun i j => raw40089step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40089step1 raw40089step0; decide +kernel
      have hl : raw40089step1Labels = raw40089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40089step0 raw40089step0Labels permutation104 hz
    mixedMoment B raw40089step1 raw40089step1Labels = mixedMoment B raw40089step2 raw40089step2Labels := by
      have hz : ∀ j, raw40089step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40089step2 = (fun i j => raw40089step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40089step2 raw40089step1; decide +kernel
      have hl : raw40089step2Labels = raw40089step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40089step1 raw40089step1Labels permutation20 hz
    mixedMoment B raw40089step2 raw40089step2Labels = mixedMoment B raw40089step3 raw40089step3Labels := by
      have ha : raw40089step3 = (fun i j => raw40089step2 (permutation7 i) (permutation5 j)) := by apply Matrix.ext; unfold raw40089step3 raw40089step2; decide +kernel
      have hl : raw40089step3Labels = raw40089step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40089step2 raw40089step2Labels permutation7 permutation5
    _ = mixedMoment B node5507 node5507Labels := by rfl

theorem canonical40090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40090 raw40090Labels = mixedMoment B node528 node528Labels := by
  calc
    mixedMoment B raw40090 raw40090Labels = mixedMoment B raw40090step0 raw40090step0Labels := by
      have hz : ∀ j, raw40090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40090step0 = (fun i j => raw40090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40090step0 raw40090; decide +kernel
      have hl : raw40090step0Labels = raw40090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40090 raw40090Labels permutation434 hz
    mixedMoment B raw40090step0 raw40090step0Labels = mixedMoment B raw40090step1 raw40090step1Labels := by
      have hz : ∀ j, raw40090step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40090step1 = (fun i j => raw40090step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40090step1 raw40090step0; decide +kernel
      have hl : raw40090step1Labels = raw40090step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40090step0 raw40090step0Labels permutation80 hz
    mixedMoment B raw40090step1 raw40090step1Labels = mixedMoment B raw40090step2 raw40090step2Labels := by
      have ha : raw40090step2 = (fun i j => raw40090step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40090step2 raw40090step1; decide +kernel
      have hl : raw40090step2Labels = raw40090step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40090step1 raw40090step1Labels permutation31 permutation3
    mixedMoment B raw40090step2 raw40090step2Labels = mixedMoment B raw40090step3 raw40090step3Labels := by
      have ha : raw40090step3 = -raw40090step2 := by apply Matrix.ext; change ∀ i j, raw40090step3 i j = -(raw40090step2 i j); unfold raw40090step3 raw40090step2; decide +kernel
      have hl : raw40090step3Labels = raw40090step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node528 node528Labels := by rfl

theorem canonical40091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40091 raw40091Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw40091 raw40091Labels = mixedMoment B raw40091step0 raw40091step0Labels := by
      have hz : ∀ j, raw40091 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40091step0 = (fun i j => raw40091 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40091step0 raw40091; decide +kernel
      have hl : raw40091step0Labels = raw40091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40091 raw40091Labels permutation434 hz
    mixedMoment B raw40091step0 raw40091step0Labels = mixedMoment B raw40091step1 raw40091step1Labels := by
      have hz : ∀ j, raw40091step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40091step1 = (fun i j => raw40091step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40091step1 raw40091step0; decide +kernel
      have hl : raw40091step1Labels = raw40091step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40091step0 raw40091step0Labels permutation80 hz
    mixedMoment B raw40091step1 raw40091step1Labels = mixedMoment B raw40091step2 raw40091step2Labels := by
      have ha : raw40091step2 = (fun i j => raw40091step1 (permutation22 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40091step2 raw40091step1; decide +kernel
      have hl : raw40091step2Labels = raw40091step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40091step1 raw40091step1Labels permutation22 permutation6
    mixedMoment B raw40091step2 raw40091step2Labels = mixedMoment B raw40091step3 raw40091step3Labels := by
      have ha : raw40091step3 = -raw40091step2 := by apply Matrix.ext; change ∀ i j, raw40091step3 i j = -(raw40091step2 i j); unfold raw40091step3 raw40091step2; decide +kernel
      have hl : raw40091step3Labels = raw40091step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node496 node496Labels := by rfl

theorem canonical40092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40092 raw40092Labels = mixedMoment B node502 node502Labels := by
  calc
    mixedMoment B raw40092 raw40092Labels = mixedMoment B raw40092step0 raw40092step0Labels := by
      have hz : ∀ j, raw40092 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40092step0 = (fun i j => raw40092 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40092step0 raw40092; decide +kernel
      have hl : raw40092step0Labels = raw40092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40092 raw40092Labels permutation346 hz
    mixedMoment B raw40092step0 raw40092step0Labels = mixedMoment B raw40092step1 raw40092step1Labels := by
      have ha : raw40092step1 = (fun i j => raw40092step0 (permutation131 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40092step1 raw40092step0; decide +kernel
      have hl : raw40092step1Labels = raw40092step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40092step0 raw40092step0Labels permutation131 permutation7
    _ = mixedMoment B node502 node502Labels := by rfl

theorem canonical40093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40093 raw40093Labels = mixedMoment B node514 node514Labels := by
  calc
    mixedMoment B raw40093 raw40093Labels = mixedMoment B raw40093step0 raw40093step0Labels := by
      have hz : ∀ j, raw40093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40093step0 = (fun i j => raw40093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40093step0 raw40093; decide +kernel
      have hl : raw40093step0Labels = raw40093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40093 raw40093Labels permutation346 hz
    mixedMoment B raw40093step0 raw40093step0Labels = mixedMoment B raw40093step1 raw40093step1Labels := by
      have ha : raw40093step1 = (fun i j => raw40093step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40093step1 raw40093step0; decide +kernel
      have hl : raw40093step1Labels = raw40093step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40093step0 raw40093step0Labels permutation44 permutation4
    mixedMoment B raw40093step1 raw40093step1Labels = mixedMoment B raw40093step2 raw40093step2Labels := by
      have ha : raw40093step2 = -raw40093step1 := by apply Matrix.ext; change ∀ i j, raw40093step2 i j = -(raw40093step1 i j); unfold raw40093step2 raw40093step1; decide +kernel
      have hl : raw40093step2Labels = raw40093step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node514 node514Labels := by rfl

theorem canonical40094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40094 raw40094Labels = mixedMoment B node483 node483Labels := by
  calc
    mixedMoment B raw40094 raw40094Labels = mixedMoment B raw40094step0 raw40094step0Labels := by
      have hz : ∀ j, raw40094 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40094step0 = (fun i j => raw40094 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40094step0 raw40094; decide +kernel
      have hl : raw40094step0Labels = raw40094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40094 raw40094Labels permutation346 hz
    mixedMoment B raw40094step0 raw40094step0Labels = mixedMoment B raw40094step1 raw40094step1Labels := by
      have ha : raw40094step1 = (fun i j => raw40094step0 (permutation101 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40094step1 raw40094step0; decide +kernel
      have hl : raw40094step1Labels = raw40094step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40094step0 raw40094step0Labels permutation101 permutation4
    _ = mixedMoment B node483 node483Labels := by rfl

theorem canonical40095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40095 raw40095Labels = mixedMoment B node438 node438Labels := by
  calc
    mixedMoment B raw40095 raw40095Labels = mixedMoment B raw40095step0 raw40095step0Labels := by
      have hz : ∀ j, raw40095 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40095step0 = (fun i j => raw40095 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40095step0 raw40095; decide +kernel
      have hl : raw40095step0Labels = raw40095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40095 raw40095Labels permutation434 hz
    mixedMoment B raw40095step0 raw40095step0Labels = mixedMoment B raw40095step1 raw40095step1Labels := by
      have ha : raw40095step1 = (fun i j => raw40095step0 (permutation112 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40095step1 raw40095step0; decide +kernel
      have hl : raw40095step1Labels = raw40095step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40095step0 raw40095step0Labels permutation112 permutation6
    mixedMoment B raw40095step1 raw40095step1Labels = mixedMoment B raw40095step2 raw40095step2Labels := by
      have ha : raw40095step2 = -raw40095step1 := by apply Matrix.ext; change ∀ i j, raw40095step2 i j = -(raw40095step1 i j); unfold raw40095step2 raw40095step1; decide +kernel
      have hl : raw40095step2Labels = raw40095step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node438 node438Labels := by rfl

theorem canonical40096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40096 raw40096Labels = mixedMoment B node514 node514Labels := by
  calc
    mixedMoment B raw40096 raw40096Labels = mixedMoment B raw40096step0 raw40096step0Labels := by
      have hz : ∀ j, raw40096 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40096step0 = (fun i j => raw40096 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40096step0 raw40096; decide +kernel
      have hl : raw40096step0Labels = raw40096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40096 raw40096Labels permutation434 hz
    mixedMoment B raw40096step0 raw40096step0Labels = mixedMoment B raw40096step1 raw40096step1Labels := by
      have ha : raw40096step1 = (fun i j => raw40096step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40096step1 raw40096step0; decide +kernel
      have hl : raw40096step1Labels = raw40096step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40096step0 raw40096step0Labels permutation139 permutation4
    _ = mixedMoment B node514 node514Labels := by rfl

theorem canonical40097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40097 raw40097Labels = mixedMoment B node436 node436Labels := by
  calc
    mixedMoment B raw40097 raw40097Labels = mixedMoment B raw40097step0 raw40097step0Labels := by
      have ha : raw40097step0 = (fun i j => raw40097 (permutation463 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40097step0 raw40097; decide +kernel
      have hl : raw40097step0Labels = raw40097Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40097 raw40097Labels permutation463 permutation6
    mixedMoment B raw40097step0 raw40097step0Labels = mixedMoment B raw40097step1 raw40097step1Labels := by
      have ha : raw40097step1 = -raw40097step0 := by apply Matrix.ext; change ∀ i j, raw40097step1 i j = -(raw40097step0 i j); unfold raw40097step1 raw40097step0; decide +kernel
      have hl : raw40097step1Labels = raw40097step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node436 node436Labels := by rfl

theorem canonical40098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40098 raw40098Labels = mixedMoment B node530 node530Labels := by
  calc
    mixedMoment B raw40098 raw40098Labels = mixedMoment B raw40098step0 raw40098step0Labels := by
      have hz : ∀ j, raw40098 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40098step0 = (fun i j => raw40098 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40098step0 raw40098; decide +kernel
      have hl : raw40098step0Labels = raw40098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40098 raw40098Labels permutation520 hz
    mixedMoment B raw40098step0 raw40098step0Labels = mixedMoment B raw40098step1 raw40098step1Labels := by
      have hz : ∀ j, raw40098step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40098step1 = (fun i j => raw40098step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40098step1 raw40098step0; decide +kernel
      have hl : raw40098step1Labels = raw40098step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40098step0 raw40098step0Labels permutation104 hz
    mixedMoment B raw40098step1 raw40098step1Labels = mixedMoment B raw40098step2 raw40098step2Labels := by
      have hz : ∀ j, raw40098step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40098step2 = (fun i j => raw40098step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40098step2 raw40098step1; decide +kernel
      have hl : raw40098step2Labels = raw40098step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40098step1 raw40098step1Labels permutation20 hz
    mixedMoment B raw40098step2 raw40098step2Labels = mixedMoment B raw40098step3 raw40098step3Labels := by
      have ha : raw40098step3 = (fun i j => raw40098step2 (permutation6 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40098step3 raw40098step2; decide +kernel
      have hl : raw40098step3Labels = raw40098step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40098step2 raw40098step2Labels permutation6 permutation2
    mixedMoment B raw40098step3 raw40098step3Labels = mixedMoment B raw40098step4 raw40098step4Labels := by
      have ha : raw40098step4 = -raw40098step3 := by apply Matrix.ext; change ∀ i j, raw40098step4 i j = -(raw40098step3 i j); unfold raw40098step4 raw40098step3; decide +kernel
      have hl : raw40098step4Labels = raw40098step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node530 node530Labels := by rfl

theorem canonical40099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40099 raw40099Labels = mixedMoment B node503 node503Labels := by
  calc
    mixedMoment B raw40099 raw40099Labels = mixedMoment B raw40099step0 raw40099step0Labels := by
      have hz : ∀ j, raw40099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40099step0 = (fun i j => raw40099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40099step0 raw40099; decide +kernel
      have hl : raw40099step0Labels = raw40099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40099 raw40099Labels permutation434 hz
    mixedMoment B raw40099step0 raw40099step0Labels = mixedMoment B raw40099step1 raw40099step1Labels := by
      have hz : ∀ j, raw40099step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40099step1 = (fun i j => raw40099step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40099step1 raw40099step0; decide +kernel
      have hl : raw40099step1Labels = raw40099step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40099step0 raw40099step0Labels permutation80 hz
    mixedMoment B raw40099step1 raw40099step1Labels = mixedMoment B raw40099step2 raw40099step2Labels := by
      have ha : raw40099step2 = (fun i j => raw40099step1 (permutation27 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40099step2 raw40099step1; decide +kernel
      have hl : raw40099step2Labels = raw40099step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40099step1 raw40099step1Labels permutation27 permutation7
    _ = mixedMoment B node503 node503Labels := by rfl

theorem canonical40100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40100 raw40100Labels = mixedMoment B node355 node355Labels := by
  calc
    mixedMoment B raw40100 raw40100Labels = mixedMoment B raw40100step0 raw40100step0Labels := by
      have hz : ∀ j, raw40100 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40100step0 = (fun i j => raw40100 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40100step0 raw40100; decide +kernel
      have hl : raw40100step0Labels = raw40100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40100 raw40100Labels permutation434 hz
    mixedMoment B raw40100step0 raw40100step0Labels = mixedMoment B raw40100step1 raw40100step1Labels := by
      have hz : ∀ j, raw40100step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40100step1 = (fun i j => raw40100step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40100step1 raw40100step0; decide +kernel
      have hl : raw40100step1Labels = raw40100step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40100step0 raw40100step0Labels permutation80 hz
    mixedMoment B raw40100step1 raw40100step1Labels = mixedMoment B raw40100step2 raw40100step2Labels := by
      have ha : raw40100step2 = (fun i j => raw40100step1 (permutation27 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40100step2 raw40100step1; decide +kernel
      have hl : raw40100step2Labels = raw40100step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40100step1 raw40100step1Labels permutation27 permutation7
    _ = mixedMoment B node355 node355Labels := by rfl

theorem canonical40101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40101 raw40101Labels = mixedMoment B node516 node516Labels := by
  calc
    mixedMoment B raw40101 raw40101Labels = mixedMoment B raw40101step0 raw40101step0Labels := by
      have hz : ∀ j, raw40101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40101step0 = (fun i j => raw40101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40101step0 raw40101; decide +kernel
      have hl : raw40101step0Labels = raw40101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40101 raw40101Labels permutation434 hz
    mixedMoment B raw40101step0 raw40101step0Labels = mixedMoment B raw40101step1 raw40101step1Labels := by
      have hz : ∀ j, raw40101step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40101step1 = (fun i j => raw40101step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40101step1 raw40101step0; decide +kernel
      have hl : raw40101step1Labels = raw40101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40101step0 raw40101step0Labels permutation80 hz
    mixedMoment B raw40101step1 raw40101step1Labels = mixedMoment B raw40101step2 raw40101step2Labels := by
      have ha : raw40101step2 = (fun i j => raw40101step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40101step2 raw40101step1; decide +kernel
      have hl : raw40101step2Labels = raw40101step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40101step1 raw40101step1Labels permutation29 permutation4
    _ = mixedMoment B node516 node516Labels := by rfl

theorem canonical40102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40102 raw40102Labels = mixedMoment B node437 node437Labels := by
  calc
    mixedMoment B raw40102 raw40102Labels = mixedMoment B raw40102step0 raw40102step0Labels := by
      have hz : ∀ j, raw40102 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40102step0 = (fun i j => raw40102 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40102step0 raw40102; decide +kernel
      have hl : raw40102step0Labels = raw40102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40102 raw40102Labels permutation346 hz
    mixedMoment B raw40102step0 raw40102step0Labels = mixedMoment B raw40102step1 raw40102step1Labels := by
      have ha : raw40102step1 = (fun i j => raw40102step0 (permutation90 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40102step1 raw40102step0; decide +kernel
      have hl : raw40102step1Labels = raw40102step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40102step0 raw40102step0Labels permutation90 permutation6
    mixedMoment B raw40102step1 raw40102step1Labels = mixedMoment B raw40102step2 raw40102step2Labels := by
      have ha : raw40102step2 = -raw40102step1 := by apply Matrix.ext; change ∀ i j, raw40102step2 i j = -(raw40102step1 i j); unfold raw40102step2 raw40102step1; decide +kernel
      have hl : raw40102step2Labels = raw40102step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node437 node437Labels := by rfl

theorem canonical40103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40103 raw40103Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw40103 raw40103Labels = mixedMoment B raw40103step0 raw40103step0Labels := by
      have hz : ∀ j, raw40103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40103step0 = (fun i j => raw40103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40103step0 raw40103; decide +kernel
      have hl : raw40103step0Labels = raw40103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40103 raw40103Labels permutation434 hz
    mixedMoment B raw40103step0 raw40103step0Labels = mixedMoment B raw40103step1 raw40103step1Labels := by
      have ha : raw40103step1 = (fun i j => raw40103step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40103step1 raw40103step0; decide +kernel
      have hl : raw40103step1Labels = raw40103step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40103step0 raw40103step0Labels permutation79 permutation6
    mixedMoment B raw40103step1 raw40103step1Labels = mixedMoment B raw40103step2 raw40103step2Labels := by
      have ha : raw40103step2 = -raw40103step1 := by apply Matrix.ext; change ∀ i j, raw40103step2 i j = -(raw40103step1 i j); unfold raw40103step2 raw40103step1; decide +kernel
      have hl : raw40103step2Labels = raw40103step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node387 node387Labels := by rfl

theorem canonical40104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40104 raw40104Labels = mixedMoment B node310 node310Labels := by
  calc
    mixedMoment B raw40104 raw40104Labels = mixedMoment B raw40104step0 raw40104step0Labels := by
      have ha : raw40104step0 = (fun i j => raw40104 (permutation317 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40104step0 raw40104; decide +kernel
      have hl : raw40104step0Labels = raw40104Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40104 raw40104Labels permutation317 permutation6
    mixedMoment B raw40104step0 raw40104step0Labels = mixedMoment B raw40104step1 raw40104step1Labels := by
      have ha : raw40104step1 = -raw40104step0 := by apply Matrix.ext; change ∀ i j, raw40104step1 i j = -(raw40104step0 i j); unfold raw40104step1 raw40104step0; decide +kernel
      have hl : raw40104step1Labels = raw40104step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node310 node310Labels := by rfl

theorem canonical40105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40105 raw40105Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw40105 raw40105Labels = mixedMoment B raw40105step0 raw40105step0Labels := by
      have hz : ∀ j, raw40105 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40105step0 = (fun i j => raw40105 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40105step0 raw40105; decide +kernel
      have hl : raw40105step0Labels = raw40105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40105 raw40105Labels permutation520 hz
    mixedMoment B raw40105step0 raw40105step0Labels = mixedMoment B raw40105step1 raw40105step1Labels := by
      have hz : ∀ j, raw40105step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40105step1 = (fun i j => raw40105step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40105step1 raw40105step0; decide +kernel
      have hl : raw40105step1Labels = raw40105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40105step0 raw40105step0Labels permutation104 hz
    mixedMoment B raw40105step1 raw40105step1Labels = mixedMoment B raw40105step2 raw40105step2Labels := by
      have hz : ∀ j, raw40105step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40105step2 = (fun i j => raw40105step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40105step2 raw40105step1; decide +kernel
      have hl : raw40105step2Labels = raw40105step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40105step1 raw40105step1Labels permutation20 hz
    mixedMoment B raw40105step2 raw40105step2Labels = mixedMoment B raw40105step3 raw40105step3Labels := by
      have ha : raw40105step3 = (fun i j => raw40105step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40105step3 raw40105step2; decide +kernel
      have hl : raw40105step3Labels = raw40105step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40105step2 raw40105step2Labels permutation4 permutation6
    mixedMoment B raw40105step3 raw40105step3Labels = mixedMoment B raw40105step4 raw40105step4Labels := by
      have ha : raw40105step4 = -raw40105step3 := by apply Matrix.ext; change ∀ i j, raw40105step4 i j = -(raw40105step3 i j); unfold raw40105step4 raw40105step3; decide +kernel
      have hl : raw40105step4Labels = raw40105step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node420 node420Labels := by rfl

theorem canonical40106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40106 raw40106Labels = mixedMoment B node390 node390Labels := by
  calc
    mixedMoment B raw40106 raw40106Labels = mixedMoment B raw40106step0 raw40106step0Labels := by
      have hz : ∀ j, raw40106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40106step0 = (fun i j => raw40106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40106step0 raw40106; decide +kernel
      have hl : raw40106step0Labels = raw40106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40106 raw40106Labels permutation434 hz
    mixedMoment B raw40106step0 raw40106step0Labels = mixedMoment B raw40106step1 raw40106step1Labels := by
      have hz : ∀ j, raw40106step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40106step1 = (fun i j => raw40106step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40106step1 raw40106step0; decide +kernel
      have hl : raw40106step1Labels = raw40106step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40106step0 raw40106step0Labels permutation80 hz
    mixedMoment B raw40106step1 raw40106step1Labels = mixedMoment B raw40106step2 raw40106step2Labels := by
      have ha : raw40106step2 = (fun i j => raw40106step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40106step2 raw40106step1; decide +kernel
      have hl : raw40106step2Labels = raw40106step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40106step1 raw40106step1Labels permutation18 permutation6
    mixedMoment B raw40106step2 raw40106step2Labels = mixedMoment B raw40106step3 raw40106step3Labels := by
      have ha : raw40106step3 = -raw40106step2 := by apply Matrix.ext; change ∀ i j, raw40106step3 i j = -(raw40106step2 i j); unfold raw40106step3 raw40106step2; decide +kernel
      have hl : raw40106step3Labels = raw40106step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node390 node390Labels := by rfl

theorem canonical40107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40107 raw40107Labels = mixedMoment B node312 node312Labels := by
  calc
    mixedMoment B raw40107 raw40107Labels = mixedMoment B raw40107step0 raw40107step0Labels := by
      have hz : ∀ j, raw40107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40107step0 = (fun i j => raw40107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40107step0 raw40107; decide +kernel
      have hl : raw40107step0Labels = raw40107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40107 raw40107Labels permutation346 hz
    mixedMoment B raw40107step0 raw40107step0Labels = mixedMoment B raw40107step1 raw40107step1Labels := by
      have ha : raw40107step1 = (fun i j => raw40107step0 (permutation66 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40107step1 raw40107step0; decide +kernel
      have hl : raw40107step1Labels = raw40107step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40107step0 raw40107step0Labels permutation66 permutation6
    mixedMoment B raw40107step1 raw40107step1Labels = mixedMoment B raw40107step2 raw40107step2Labels := by
      have ha : raw40107step2 = -raw40107step1 := by apply Matrix.ext; change ∀ i j, raw40107step2 i j = -(raw40107step1 i j); unfold raw40107step2 raw40107step1; decide +kernel
      have hl : raw40107step2Labels = raw40107step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node312 node312Labels := by rfl

theorem canonical40108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40108 raw40108Labels = mixedMoment B node111 node111Labels := by
  calc
    mixedMoment B raw40108 raw40108Labels = mixedMoment B raw40108step0 raw40108step0Labels := by
      have hz : ∀ j, raw40108 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40108step0 = (fun i j => raw40108 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40108step0 raw40108; decide +kernel
      have hl : raw40108step0Labels = raw40108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40108 raw40108Labels permutation520 hz
    mixedMoment B raw40108step0 raw40108step0Labels = mixedMoment B raw40108step1 raw40108step1Labels := by
      have hz : ∀ j, raw40108step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40108step1 = (fun i j => raw40108step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40108step1 raw40108step0; decide +kernel
      have hl : raw40108step1Labels = raw40108step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40108step0 raw40108step0Labels permutation104 hz
    mixedMoment B raw40108step1 raw40108step1Labels = mixedMoment B raw40108step2 raw40108step2Labels := by
      have ha : raw40108step2 = (fun i j => raw40108step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40108step2 raw40108step1; decide +kernel
      have hl : raw40108step2Labels = raw40108step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40108step1 raw40108step1Labels permutation16 permutation6
    mixedMoment B raw40108step2 raw40108step2Labels = mixedMoment B raw40108step3 raw40108step3Labels := by
      have ha : raw40108step3 = -raw40108step2 := by apply Matrix.ext; change ∀ i j, raw40108step3 i j = -(raw40108step2 i j); unfold raw40108step3 raw40108step2; decide +kernel
      have hl : raw40108step3Labels = raw40108step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node111 node111Labels := by rfl

theorem canonical40109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40109 raw40109Labels = mixedMoment B node112 node112Labels := by
  calc
    mixedMoment B raw40109 raw40109Labels = mixedMoment B raw40109step0 raw40109step0Labels := by
      have hz : ∀ j, raw40109 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40109step0 = (fun i j => raw40109 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40109step0 raw40109; decide +kernel
      have hl : raw40109step0Labels = raw40109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40109 raw40109Labels permutation520 hz
    mixedMoment B raw40109step0 raw40109step0Labels = mixedMoment B raw40109step1 raw40109step1Labels := by
      have hz : ∀ j, raw40109step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40109step1 = (fun i j => raw40109step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40109step1 raw40109step0; decide +kernel
      have hl : raw40109step1Labels = raw40109step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40109step0 raw40109step0Labels permutation104 hz
    mixedMoment B raw40109step1 raw40109step1Labels = mixedMoment B raw40109step2 raw40109step2Labels := by
      have hz : ∀ j, raw40109step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40109step2 = (fun i j => raw40109step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40109step2 raw40109step1; decide +kernel
      have hl : raw40109step2Labels = raw40109step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40109step1 raw40109step1Labels permutation20 hz
    mixedMoment B raw40109step2 raw40109step2Labels = mixedMoment B raw40109step3 raw40109step3Labels := by
      have ha : raw40109step3 = (fun i j => raw40109step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40109step3 raw40109step2; decide +kernel
      have hl : raw40109step3Labels = raw40109step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40109step2 raw40109step2Labels permutation4 permutation6
    mixedMoment B raw40109step3 raw40109step3Labels = mixedMoment B raw40109step4 raw40109step4Labels := by
      have ha : raw40109step4 = -raw40109step3 := by apply Matrix.ext; change ∀ i j, raw40109step4 i j = -(raw40109step3 i j); unfold raw40109step4 raw40109step3; decide +kernel
      have hl : raw40109step4Labels = raw40109step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node112 node112Labels := by rfl

theorem canonical40110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40110 raw40110Labels = mixedMoment B node0 node0Labels := by
  calc
    mixedMoment B raw40110 raw40110Labels = mixedMoment B raw40110step0 raw40110step0Labels := by
      have hz : ∀ j, raw40110 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40110step0 = (fun i j => raw40110 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40110step0 raw40110; decide +kernel
      have hl : raw40110step0Labels = raw40110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40110 raw40110Labels permutation520 hz
    mixedMoment B raw40110step0 raw40110step0Labels = mixedMoment B raw40110step1 raw40110step1Labels := by
      have hz : ∀ j, raw40110step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40110step1 = (fun i j => raw40110step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40110step1 raw40110step0; decide +kernel
      have hl : raw40110step1Labels = raw40110step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40110step0 raw40110step0Labels permutation104 hz
    mixedMoment B raw40110step1 raw40110step1Labels = mixedMoment B raw40110step2 raw40110step2Labels := by
      have hz : ∀ i, raw40110step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw40110step2 = (fun i j => raw40110step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw40110step2 raw40110step1; decide +kernel
      have hl : raw40110step2Labels = (fun j => raw40110step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw40110step1 raw40110step1Labels permutation6 hz
    mixedMoment B raw40110step2 raw40110step2Labels = mixedMoment B raw40110step3 raw40110step3Labels := by
      have ha : raw40110step3 = (fun i j => raw40110step2 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw40110step3 raw40110step2; decide +kernel
      have hl : raw40110step3Labels = raw40110step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40110step2 raw40110step2Labels permutation26 permutation0
    mixedMoment B raw40110step3 raw40110step3Labels = mixedMoment B raw40110step4 raw40110step4Labels := by
      have ha : raw40110step4 = -raw40110step3 := by apply Matrix.ext; change ∀ i j, raw40110step4 i j = -(raw40110step3 i j); unfold raw40110step4 raw40110step3; decide +kernel
      have hl : raw40110step4Labels = raw40110step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node0 node0Labels := by rfl

theorem canonical40111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40111 raw40111Labels = mixedMoment B node3 node3Labels := by
  calc
    mixedMoment B raw40111 raw40111Labels = mixedMoment B raw40111step0 raw40111step0Labels := by
      have hz : ∀ j, raw40111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40111step0 = (fun i j => raw40111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40111step0 raw40111; decide +kernel
      have hl : raw40111step0Labels = raw40111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40111 raw40111Labels permutation434 hz
    mixedMoment B raw40111step0 raw40111step0Labels = mixedMoment B raw40111step1 raw40111step1Labels := by
      have hz : ∀ i, raw40111step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw40111step1 = (fun i j => raw40111step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw40111step1 raw40111step0; decide +kernel
      have hl : raw40111step1Labels = (fun j => raw40111step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw40111step0 raw40111step0Labels permutation6 hz
    mixedMoment B raw40111step1 raw40111step1Labels = mixedMoment B raw40111step2 raw40111step2Labels := by
      have ha : raw40111step2 = (fun i j => raw40111step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw40111step2 raw40111step1; decide +kernel
      have hl : raw40111step2Labels = raw40111step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40111step1 raw40111step1Labels permutation146 permutation0
    mixedMoment B raw40111step2 raw40111step2Labels = mixedMoment B raw40111step3 raw40111step3Labels := by
      have ha : raw40111step3 = -raw40111step2 := by apply Matrix.ext; change ∀ i j, raw40111step3 i j = -(raw40111step2 i j); unfold raw40111step3 raw40111step2; decide +kernel
      have hl : raw40111step3Labels = raw40111step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3 node3Labels := by rfl

theorem canonical40112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40112 raw40112Labels = mixedMoment B node411 node411Labels := by
  calc
    mixedMoment B raw40112 raw40112Labels = mixedMoment B raw40112step0 raw40112step0Labels := by
      have hz : ∀ j, raw40112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40112step0 = (fun i j => raw40112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40112step0 raw40112; decide +kernel
      have hl : raw40112step0Labels = raw40112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40112 raw40112Labels permutation434 hz
    mixedMoment B raw40112step0 raw40112step0Labels = mixedMoment B raw40112step1 raw40112step1Labels := by
      have ha : raw40112step1 = (fun i j => raw40112step0 (permutation122 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40112step1 raw40112step0; decide +kernel
      have hl : raw40112step1Labels = raw40112step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40112step0 raw40112step0Labels permutation122 permutation4
    _ = mixedMoment B node411 node411Labels := by rfl

theorem canonical40113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40113 raw40113Labels = mixedMoment B node492 node492Labels := by
  calc
    mixedMoment B raw40113 raw40113Labels = mixedMoment B raw40113step0 raw40113step0Labels := by
      have ha : raw40113step0 = (fun i j => raw40113 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40113step0 raw40113; decide +kernel
      have hl : raw40113step0Labels = raw40113Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40113 raw40113Labels permutation683 permutation2
    mixedMoment B raw40113step0 raw40113step0Labels = mixedMoment B raw40113step1 raw40113step1Labels := by
      have ha : raw40113step1 = -raw40113step0 := by apply Matrix.ext; change ∀ i j, raw40113step1 i j = -(raw40113step0 i j); unfold raw40113step1 raw40113step0; decide +kernel
      have hl : raw40113step1Labels = raw40113step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node492 node492Labels := by rfl

theorem canonical40114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40114 raw40114Labels = mixedMoment B node265 node265Labels := by
  calc
    mixedMoment B raw40114 raw40114Labels = mixedMoment B raw40114step0 raw40114step0Labels := by
      have hz : ∀ j, raw40114 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40114step0 = (fun i j => raw40114 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40114step0 raw40114; decide +kernel
      have hl : raw40114step0Labels = raw40114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40114 raw40114Labels permutation520 hz
    mixedMoment B raw40114step0 raw40114step0Labels = mixedMoment B raw40114step1 raw40114step1Labels := by
      have ha : raw40114step1 = (fun i j => raw40114step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40114step1 raw40114step0; decide +kernel
      have hl : raw40114step1Labels = raw40114step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40114step0 raw40114step0Labels permutation150 permutation3
    mixedMoment B raw40114step1 raw40114step1Labels = mixedMoment B raw40114step2 raw40114step2Labels := by
      have ha : raw40114step2 = -raw40114step1 := by apply Matrix.ext; change ∀ i j, raw40114step2 i j = -(raw40114step1 i j); unfold raw40114step2 raw40114step1; decide +kernel
      have hl : raw40114step2Labels = raw40114step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node265 node265Labels := by rfl

theorem canonical40115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40115 raw40115Labels = mixedMoment B node464 node464Labels := by
  calc
    mixedMoment B raw40115 raw40115Labels = mixedMoment B raw40115step0 raw40115step0Labels := by
      have ha : raw40115step0 = (fun i j => raw40115 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40115step0 raw40115; decide +kernel
      have hl : raw40115step0Labels = raw40115Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40115 raw40115Labels permutation687 permutation3
    mixedMoment B raw40115step0 raw40115step0Labels = mixedMoment B raw40115step1 raw40115step1Labels := by
      have ha : raw40115step1 = -raw40115step0 := by apply Matrix.ext; change ∀ i j, raw40115step1 i j = -(raw40115step0 i j); unfold raw40115step1 raw40115step0; decide +kernel
      have hl : raw40115step1Labels = raw40115step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node464 node464Labels := by rfl

theorem canonical40116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40116 raw40116Labels = mixedMoment B node382 node382Labels := by
  calc
    mixedMoment B raw40116 raw40116Labels = mixedMoment B raw40116step0 raw40116step0Labels := by
      have ha : raw40116step0 = (fun i j => raw40116 (permutation547 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40116step0 raw40116; decide +kernel
      have hl : raw40116step0Labels = raw40116Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40116 raw40116Labels permutation547 permutation4
    _ = mixedMoment B node382 node382Labels := by rfl

theorem canonical40117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40117 raw40117Labels = mixedMoment B node5509 node5509Labels := by
  calc
    mixedMoment B raw40117 raw40117Labels = mixedMoment B raw40117step0 raw40117step0Labels := by
      have hz : ∀ j, raw40117 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40117step0 = (fun i j => raw40117 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40117step0 raw40117; decide +kernel
      have hl : raw40117step0Labels = raw40117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40117 raw40117Labels permutation434 hz
    mixedMoment B raw40117step0 raw40117step0Labels = mixedMoment B raw40117step1 raw40117step1Labels := by
      have ha : raw40117step1 = (fun i j => raw40117step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40117step1 raw40117step0; decide +kernel
      have hl : raw40117step1Labels = raw40117step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40117step0 raw40117step0Labels permutation150 permutation3
    mixedMoment B raw40117step1 raw40117step1Labels = mixedMoment B raw40117step2 raw40117step2Labels := by
      have ha : raw40117step2 = -raw40117step1 := by apply Matrix.ext; change ∀ i j, raw40117step2 i j = -(raw40117step1 i j); unfold raw40117step2 raw40117step1; decide +kernel
      have hl : raw40117step2Labels = raw40117step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5509 node5509Labels := by rfl

theorem canonical40118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40118 raw40118Labels = mixedMoment B node386 node386Labels := by
  calc
    mixedMoment B raw40118 raw40118Labels = mixedMoment B raw40118step0 raw40118step0Labels := by
      have hz : ∀ j, raw40118 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40118step0 = (fun i j => raw40118 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40118step0 raw40118; decide +kernel
      have hl : raw40118step0Labels = raw40118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40118 raw40118Labels permutation434 hz
    mixedMoment B raw40118step0 raw40118step0Labels = mixedMoment B raw40118step1 raw40118step1Labels := by
      have ha : raw40118step1 = (fun i j => raw40118step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40118step1 raw40118step0; decide +kernel
      have hl : raw40118step1Labels = raw40118step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40118step0 raw40118step0Labels permutation116 permutation4
    _ = mixedMoment B node386 node386Labels := by rfl

theorem canonical40119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40119 raw40119Labels = mixedMoment B node488 node488Labels := by
  calc
    mixedMoment B raw40119 raw40119Labels = mixedMoment B raw40119step0 raw40119step0Labels := by
      have ha : raw40119step0 = (fun i j => raw40119 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40119step0 raw40119; decide +kernel
      have hl : raw40119step0Labels = raw40119Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40119 raw40119Labels permutation683 permutation2
    mixedMoment B raw40119step0 raw40119step0Labels = mixedMoment B raw40119step1 raw40119step1Labels := by
      have ha : raw40119step1 = -raw40119step0 := by apply Matrix.ext; change ∀ i j, raw40119step1 i j = -(raw40119step0 i j); unfold raw40119step1 raw40119step0; decide +kernel
      have hl : raw40119step1Labels = raw40119step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node488 node488Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment640 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 640) =
      Integer.Sparse.eval keyMomentRow640 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 640).leftCharge (GramAssembly.key 640).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 479) := by
    have ha : gramCharges (GramAssembly.key 640).leftCharge (GramAssembly.key 640).rightCharge = raw40088 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40088Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40088 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 640).leftCharge (GramAssembly.key 640).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow640, Integer.Sparse.eval]

theorem keyMoment641 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 641) =
      Integer.Sparse.eval keyMomentRow641 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 641).leftCharge (GramAssembly.key 641).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 5) := by
    have ha : gramCharges (GramAssembly.key 641).leftCharge (GramAssembly.key 641).rightCharge = raw40089 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40089Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40089 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 641).leftCharge (GramAssembly.key 641).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow641, Integer.Sparse.eval]

theorem keyMoment642 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 642) =
      Integer.Sparse.eval keyMomentRow642 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 642).leftCharge (GramAssembly.key 642).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 528) := by
    have ha : gramCharges (GramAssembly.key 642).leftCharge (GramAssembly.key 642).rightCharge = raw40090 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40090Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40090 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 642).leftCharge (GramAssembly.key 642).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow642, Integer.Sparse.eval]

theorem keyMoment643 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 643) =
      Integer.Sparse.eval keyMomentRow643 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 643).leftCharge (GramAssembly.key 643).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 496) := by
    have ha : gramCharges (GramAssembly.key 643).leftCharge (GramAssembly.key 643).rightCharge = raw40091 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40091Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40091 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 643).leftCharge (GramAssembly.key 643).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow643, Integer.Sparse.eval]

theorem keyMoment644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 644) =
      Integer.Sparse.eval keyMomentRow644 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 644).leftCharge (GramAssembly.key 644).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 502) := by
    have ha : gramCharges (GramAssembly.key 644).leftCharge (GramAssembly.key 644).rightCharge = raw40092 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40092Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40092 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 644).leftCharge (GramAssembly.key 644).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow644, Integer.Sparse.eval]

theorem keyMoment645 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 645) =
      Integer.Sparse.eval keyMomentRow645 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 645).leftCharge (GramAssembly.key 645).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 514) := by
    have ha : gramCharges (GramAssembly.key 645).leftCharge (GramAssembly.key 645).rightCharge = raw40093 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40093Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40093 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 645).leftCharge (GramAssembly.key 645).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow645, Integer.Sparse.eval]

theorem keyMoment646 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 646) =
      Integer.Sparse.eval keyMomentRow646 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 646).leftCharge (GramAssembly.key 646).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 483) := by
    have ha : gramCharges (GramAssembly.key 646).leftCharge (GramAssembly.key 646).rightCharge = raw40094 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40094Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40094 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 646).leftCharge (GramAssembly.key 646).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow646, Integer.Sparse.eval]

theorem keyMoment647 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 647) =
      Integer.Sparse.eval keyMomentRow647 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 647).leftCharge (GramAssembly.key 647).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 438) := by
    have ha : gramCharges (GramAssembly.key 647).leftCharge (GramAssembly.key 647).rightCharge = raw40095 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40095Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40095 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 647).leftCharge (GramAssembly.key 647).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow647, Integer.Sparse.eval]

theorem keyMoment648 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 648) =
      Integer.Sparse.eval keyMomentRow648 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 648).leftCharge (GramAssembly.key 648).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 514) := by
    have ha : gramCharges (GramAssembly.key 648).leftCharge (GramAssembly.key 648).rightCharge = raw40096 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40096Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40096 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 648).leftCharge (GramAssembly.key 648).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow648, Integer.Sparse.eval]

theorem keyMoment649 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 649) =
      Integer.Sparse.eval keyMomentRow649 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 649).leftCharge (GramAssembly.key 649).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 436) := by
    have ha : gramCharges (GramAssembly.key 649).leftCharge (GramAssembly.key 649).rightCharge = raw40097 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40097Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40097 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 649).leftCharge (GramAssembly.key 649).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow649, Integer.Sparse.eval]

theorem keyMoment650 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 650) =
      Integer.Sparse.eval keyMomentRow650 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 650).leftCharge (GramAssembly.key 650).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 530) := by
    have ha : gramCharges (GramAssembly.key 650).leftCharge (GramAssembly.key 650).rightCharge = raw40098 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40098Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40098 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 650).leftCharge (GramAssembly.key 650).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow650, Integer.Sparse.eval]

theorem keyMoment651 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 651) =
      Integer.Sparse.eval keyMomentRow651 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 651).leftCharge (GramAssembly.key 651).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 503) := by
    have ha : gramCharges (GramAssembly.key 651).leftCharge (GramAssembly.key 651).rightCharge = raw40099 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40099Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40099 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 651).leftCharge (GramAssembly.key 651).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow651, Integer.Sparse.eval]

theorem keyMoment652 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 652) =
      Integer.Sparse.eval keyMomentRow652 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 652).leftCharge (GramAssembly.key 652).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 355) := by
    have ha : gramCharges (GramAssembly.key 652).leftCharge (GramAssembly.key 652).rightCharge = raw40100 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40100Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40100 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 652).leftCharge (GramAssembly.key 652).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow652, Integer.Sparse.eval]

theorem keyMoment653 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 653) =
      Integer.Sparse.eval keyMomentRow653 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 653).leftCharge (GramAssembly.key 653).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 516) := by
    have ha : gramCharges (GramAssembly.key 653).leftCharge (GramAssembly.key 653).rightCharge = raw40101 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40101Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40101 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 653).leftCharge (GramAssembly.key 653).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow653, Integer.Sparse.eval]

theorem keyMoment654 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 654) =
      Integer.Sparse.eval keyMomentRow654 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 654).leftCharge (GramAssembly.key 654).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 437) := by
    have ha : gramCharges (GramAssembly.key 654).leftCharge (GramAssembly.key 654).rightCharge = raw40102 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40102Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40102 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 654).leftCharge (GramAssembly.key 654).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow654, Integer.Sparse.eval]

theorem keyMoment655 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 655) =
      Integer.Sparse.eval keyMomentRow655 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 655).leftCharge (GramAssembly.key 655).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 387) := by
    have ha : gramCharges (GramAssembly.key 655).leftCharge (GramAssembly.key 655).rightCharge = raw40103 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40103Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40103 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 655).leftCharge (GramAssembly.key 655).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow655, Integer.Sparse.eval]

theorem keyMoment656 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 656) =
      Integer.Sparse.eval keyMomentRow656 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 656).leftCharge (GramAssembly.key 656).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 310) := by
    have ha : gramCharges (GramAssembly.key 656).leftCharge (GramAssembly.key 656).rightCharge = raw40104 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40104Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40104 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 656).leftCharge (GramAssembly.key 656).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow656, Integer.Sparse.eval]

theorem keyMoment657 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 657) =
      Integer.Sparse.eval keyMomentRow657 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 657).leftCharge (GramAssembly.key 657).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 420) := by
    have ha : gramCharges (GramAssembly.key 657).leftCharge (GramAssembly.key 657).rightCharge = raw40105 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40105Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40105 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 657).leftCharge (GramAssembly.key 657).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow657, Integer.Sparse.eval]

theorem keyMoment658 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 658) =
      Integer.Sparse.eval keyMomentRow658 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 658).leftCharge (GramAssembly.key 658).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 390) := by
    have ha : gramCharges (GramAssembly.key 658).leftCharge (GramAssembly.key 658).rightCharge = raw40106 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40106Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40106 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 658).leftCharge (GramAssembly.key 658).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow658, Integer.Sparse.eval]

theorem keyMoment659 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 659) =
      Integer.Sparse.eval keyMomentRow659 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 659).leftCharge (GramAssembly.key 659).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 312) := by
    have ha : gramCharges (GramAssembly.key 659).leftCharge (GramAssembly.key 659).rightCharge = raw40107 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40107Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40107 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 659).leftCharge (GramAssembly.key 659).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow659, Integer.Sparse.eval]

theorem keyMoment660 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 660) =
      Integer.Sparse.eval keyMomentRow660 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 660).leftCharge (GramAssembly.key 660).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 111) := by
    have ha : gramCharges (GramAssembly.key 660).leftCharge (GramAssembly.key 660).rightCharge = raw40108 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40108Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40108 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 660).leftCharge (GramAssembly.key 660).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow660, Integer.Sparse.eval]

theorem keyMoment661 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 661) =
      Integer.Sparse.eval keyMomentRow661 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 661).leftCharge (GramAssembly.key 661).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 112) := by
    have ha : gramCharges (GramAssembly.key 661).leftCharge (GramAssembly.key 661).rightCharge = raw40109 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40109Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40109 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 661).leftCharge (GramAssembly.key 661).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow661, Integer.Sparse.eval]

theorem keyMoment662 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 662) =
      Integer.Sparse.eval keyMomentRow662 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 662).leftCharge (GramAssembly.key 662).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 0) := by
    have ha : gramCharges (GramAssembly.key 662).leftCharge (GramAssembly.key 662).rightCharge = raw40110 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40110Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40110 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 662).leftCharge (GramAssembly.key 662).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow662, Integer.Sparse.eval]

theorem keyMoment663 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 663) =
      Integer.Sparse.eval keyMomentRow663 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 663).leftCharge (GramAssembly.key 663).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 3) := by
    have ha : gramCharges (GramAssembly.key 663).leftCharge (GramAssembly.key 663).rightCharge = raw40111 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40111Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40111 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 663).leftCharge (GramAssembly.key 663).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow663, Integer.Sparse.eval]

theorem keyMoment664 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 664) =
      Integer.Sparse.eval keyMomentRow664 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 664).leftCharge (GramAssembly.key 664).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 411) := by
    have ha : gramCharges (GramAssembly.key 664).leftCharge (GramAssembly.key 664).rightCharge = raw40112 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40112Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40112 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 664).leftCharge (GramAssembly.key 664).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow664, Integer.Sparse.eval]

theorem keyMoment665 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 665) =
      Integer.Sparse.eval keyMomentRow665 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 665).leftCharge (GramAssembly.key 665).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 492) := by
    have ha : gramCharges (GramAssembly.key 665).leftCharge (GramAssembly.key 665).rightCharge = raw40113 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40113Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40113 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 665).leftCharge (GramAssembly.key 665).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow665, Integer.Sparse.eval]

theorem keyMoment666 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 666) =
      Integer.Sparse.eval keyMomentRow666 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 666).leftCharge (GramAssembly.key 666).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 265) := by
    have ha : gramCharges (GramAssembly.key 666).leftCharge (GramAssembly.key 666).rightCharge = raw40114 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40114Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40114 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 666).leftCharge (GramAssembly.key 666).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow666, Integer.Sparse.eval]

theorem keyMoment667 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 667) =
      Integer.Sparse.eval keyMomentRow667 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 667).leftCharge (GramAssembly.key 667).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 464) := by
    have ha : gramCharges (GramAssembly.key 667).leftCharge (GramAssembly.key 667).rightCharge = raw40115 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40115Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40115 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 667).leftCharge (GramAssembly.key 667).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow667, Integer.Sparse.eval]

theorem keyMoment668 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 668) =
      Integer.Sparse.eval keyMomentRow668 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 668).leftCharge (GramAssembly.key 668).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 382) := by
    have ha : gramCharges (GramAssembly.key 668).leftCharge (GramAssembly.key 668).rightCharge = raw40116 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40116Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40116 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 668).leftCharge (GramAssembly.key 668).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow668, Integer.Sparse.eval]

theorem keyMoment669 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 669) =
      Integer.Sparse.eval keyMomentRow669 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 669).leftCharge (GramAssembly.key 669).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 7) := by
    have ha : gramCharges (GramAssembly.key 669).leftCharge (GramAssembly.key 669).rightCharge = raw40117 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40117Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40117 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 669).leftCharge (GramAssembly.key 669).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow669, Integer.Sparse.eval]

theorem keyMoment670 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 670) =
      Integer.Sparse.eval keyMomentRow670 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 670).leftCharge (GramAssembly.key 670).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 386) := by
    have ha : gramCharges (GramAssembly.key 670).leftCharge (GramAssembly.key 670).rightCharge = raw40118 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40118Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40118 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 670).leftCharge (GramAssembly.key 670).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow670, Integer.Sparse.eval]

theorem keyMoment671 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 671) =
      Integer.Sparse.eval keyMomentRow671 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 671).leftCharge (GramAssembly.key 671).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 488) := by
    have ha : gramCharges (GramAssembly.key 671).leftCharge (GramAssembly.key 671).rightCharge = raw40119 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40119Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40119 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 671).leftCharge (GramAssembly.key 671).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow671, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt640 : keyMomentRows (640 : Fin 2886) =
    keyMomentRow640 := by decide +kernel

theorem keyMomentRowsAt641 : keyMomentRows (641 : Fin 2886) =
    keyMomentRow641 := by decide +kernel

theorem keyMomentRowsAt642 : keyMomentRows (642 : Fin 2886) =
    keyMomentRow642 := by decide +kernel

theorem keyMomentRowsAt643 : keyMomentRows (643 : Fin 2886) =
    keyMomentRow643 := by decide +kernel

theorem keyMomentRowsAt644 : keyMomentRows (644 : Fin 2886) =
    keyMomentRow644 := by decide +kernel

theorem keyMomentRowsAt645 : keyMomentRows (645 : Fin 2886) =
    keyMomentRow645 := by decide +kernel

theorem keyMomentRowsAt646 : keyMomentRows (646 : Fin 2886) =
    keyMomentRow646 := by decide +kernel

theorem keyMomentRowsAt647 : keyMomentRows (647 : Fin 2886) =
    keyMomentRow647 := by decide +kernel

theorem keyMomentRowsAt648 : keyMomentRows (648 : Fin 2886) =
    keyMomentRow648 := by decide +kernel

theorem keyMomentRowsAt649 : keyMomentRows (649 : Fin 2886) =
    keyMomentRow649 := by decide +kernel

theorem keyMomentRowsAt650 : keyMomentRows (650 : Fin 2886) =
    keyMomentRow650 := by decide +kernel

theorem keyMomentRowsAt651 : keyMomentRows (651 : Fin 2886) =
    keyMomentRow651 := by decide +kernel

theorem keyMomentRowsAt652 : keyMomentRows (652 : Fin 2886) =
    keyMomentRow652 := by decide +kernel

theorem keyMomentRowsAt653 : keyMomentRows (653 : Fin 2886) =
    keyMomentRow653 := by decide +kernel

theorem keyMomentRowsAt654 : keyMomentRows (654 : Fin 2886) =
    keyMomentRow654 := by decide +kernel

theorem keyMomentRowsAt655 : keyMomentRows (655 : Fin 2886) =
    keyMomentRow655 := by decide +kernel

theorem keyMomentRowsAt656 : keyMomentRows (656 : Fin 2886) =
    keyMomentRow656 := by decide +kernel

theorem keyMomentRowsAt657 : keyMomentRows (657 : Fin 2886) =
    keyMomentRow657 := by decide +kernel

theorem keyMomentRowsAt658 : keyMomentRows (658 : Fin 2886) =
    keyMomentRow658 := by decide +kernel

theorem keyMomentRowsAt659 : keyMomentRows (659 : Fin 2886) =
    keyMomentRow659 := by decide +kernel

theorem keyMomentRowsAt660 : keyMomentRows (660 : Fin 2886) =
    keyMomentRow660 := by decide +kernel

theorem keyMomentRowsAt661 : keyMomentRows (661 : Fin 2886) =
    keyMomentRow661 := by decide +kernel

theorem keyMomentRowsAt662 : keyMomentRows (662 : Fin 2886) =
    keyMomentRow662 := by decide +kernel

theorem keyMomentRowsAt663 : keyMomentRows (663 : Fin 2886) =
    keyMomentRow663 := by decide +kernel

theorem keyMomentRowsAt664 : keyMomentRows (664 : Fin 2886) =
    keyMomentRow664 := by decide +kernel

theorem keyMomentRowsAt665 : keyMomentRows (665 : Fin 2886) =
    keyMomentRow665 := by decide +kernel

theorem keyMomentRowsAt666 : keyMomentRows (666 : Fin 2886) =
    keyMomentRow666 := by decide +kernel

theorem keyMomentRowsAt667 : keyMomentRows (667 : Fin 2886) =
    keyMomentRow667 := by decide +kernel

theorem keyMomentRowsAt668 : keyMomentRows (668 : Fin 2886) =
    keyMomentRow668 := by decide +kernel

theorem keyMomentRowsAt669 : keyMomentRows (669 : Fin 2886) =
    keyMomentRow669 := by decide +kernel

theorem keyMomentRowsAt670 : keyMomentRows (670 : Fin 2886) =
    keyMomentRow670 := by decide +kernel

theorem keyMomentRowsAt671 : keyMomentRows (671 : Fin 2886) =
    keyMomentRow671 := by decide +kernel

theorem keyMomentChunkSound20_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 20) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 640 ∨ k.val = 641 ∨ k.val = 642 ∨ k.val = 643 ∨ k.val = 644 ∨ k.val = 645 ∨ k.val = 646 ∨ k.val = 647 ∨ k.val = 648 ∨ k.val = 649 ∨ k.val = 650 ∨ k.val = 651 ∨ k.val = 652 ∨ k.val = 653 ∨ k.val = 654 ∨ k.val = 655 ∨ k.val = 656 ∨ k.val = 657 ∨ k.val = 658 ∨ k.val = 659 ∨ k.val = 660 ∨ k.val = 661 ∨ k.val = 662 ∨ k.val = 663 ∨ k.val = 664 ∨ k.val = 665 ∨ k.val = 666 ∨ k.val = 667 ∨ k.val = 668 ∨ k.val = 669 ∨ k.val = 670 ∨ k.val = 671 := by omega
  rcases heq with h640 | h641 | h642 | h643 | h644 | h645 | h646 | h647 | h648 | h649 | h650 | h651 | h652 | h653 | h654 | h655 | h656 | h657 | h658 | h659 | h660 | h661 | h662 | h663 | h664 | h665 | h666 | h667 | h668 | h669 | h670 | h671
  · have he : k = (640 : Fin 2886) := Fin.ext h640
    subst k
    rw [keyMomentRowsAt640]
    exact keyMoment640 B hB
  · have he : k = (641 : Fin 2886) := Fin.ext h641
    subst k
    rw [keyMomentRowsAt641]
    exact keyMoment641 B hB
  · have he : k = (642 : Fin 2886) := Fin.ext h642
    subst k
    rw [keyMomentRowsAt642]
    exact keyMoment642 B hB
  · have he : k = (643 : Fin 2886) := Fin.ext h643
    subst k
    rw [keyMomentRowsAt643]
    exact keyMoment643 B hB
  · have he : k = (644 : Fin 2886) := Fin.ext h644
    subst k
    rw [keyMomentRowsAt644]
    exact keyMoment644 B hB
  · have he : k = (645 : Fin 2886) := Fin.ext h645
    subst k
    rw [keyMomentRowsAt645]
    exact keyMoment645 B hB
  · have he : k = (646 : Fin 2886) := Fin.ext h646
    subst k
    rw [keyMomentRowsAt646]
    exact keyMoment646 B hB
  · have he : k = (647 : Fin 2886) := Fin.ext h647
    subst k
    rw [keyMomentRowsAt647]
    exact keyMoment647 B hB
  · have he : k = (648 : Fin 2886) := Fin.ext h648
    subst k
    rw [keyMomentRowsAt648]
    exact keyMoment648 B hB
  · have he : k = (649 : Fin 2886) := Fin.ext h649
    subst k
    rw [keyMomentRowsAt649]
    exact keyMoment649 B hB
  · have he : k = (650 : Fin 2886) := Fin.ext h650
    subst k
    rw [keyMomentRowsAt650]
    exact keyMoment650 B hB
  · have he : k = (651 : Fin 2886) := Fin.ext h651
    subst k
    rw [keyMomentRowsAt651]
    exact keyMoment651 B hB
  · have he : k = (652 : Fin 2886) := Fin.ext h652
    subst k
    rw [keyMomentRowsAt652]
    exact keyMoment652 B hB
  · have he : k = (653 : Fin 2886) := Fin.ext h653
    subst k
    rw [keyMomentRowsAt653]
    exact keyMoment653 B hB
  · have he : k = (654 : Fin 2886) := Fin.ext h654
    subst k
    rw [keyMomentRowsAt654]
    exact keyMoment654 B hB
  · have he : k = (655 : Fin 2886) := Fin.ext h655
    subst k
    rw [keyMomentRowsAt655]
    exact keyMoment655 B hB
  · have he : k = (656 : Fin 2886) := Fin.ext h656
    subst k
    rw [keyMomentRowsAt656]
    exact keyMoment656 B hB
  · have he : k = (657 : Fin 2886) := Fin.ext h657
    subst k
    rw [keyMomentRowsAt657]
    exact keyMoment657 B hB
  · have he : k = (658 : Fin 2886) := Fin.ext h658
    subst k
    rw [keyMomentRowsAt658]
    exact keyMoment658 B hB
  · have he : k = (659 : Fin 2886) := Fin.ext h659
    subst k
    rw [keyMomentRowsAt659]
    exact keyMoment659 B hB
  · have he : k = (660 : Fin 2886) := Fin.ext h660
    subst k
    rw [keyMomentRowsAt660]
    exact keyMoment660 B hB
  · have he : k = (661 : Fin 2886) := Fin.ext h661
    subst k
    rw [keyMomentRowsAt661]
    exact keyMoment661 B hB
  · have he : k = (662 : Fin 2886) := Fin.ext h662
    subst k
    rw [keyMomentRowsAt662]
    exact keyMoment662 B hB
  · have he : k = (663 : Fin 2886) := Fin.ext h663
    subst k
    rw [keyMomentRowsAt663]
    exact keyMoment663 B hB
  · have he : k = (664 : Fin 2886) := Fin.ext h664
    subst k
    rw [keyMomentRowsAt664]
    exact keyMoment664 B hB
  · have he : k = (665 : Fin 2886) := Fin.ext h665
    subst k
    rw [keyMomentRowsAt665]
    exact keyMoment665 B hB
  · have he : k = (666 : Fin 2886) := Fin.ext h666
    subst k
    rw [keyMomentRowsAt666]
    exact keyMoment666 B hB
  · have he : k = (667 : Fin 2886) := Fin.ext h667
    subst k
    rw [keyMomentRowsAt667]
    exact keyMoment667 B hB
  · have he : k = (668 : Fin 2886) := Fin.ext h668
    subst k
    rw [keyMomentRowsAt668]
    exact keyMoment668 B hB
  · have he : k = (669 : Fin 2886) := Fin.ext h669
    subst k
    rw [keyMomentRowsAt669]
    exact keyMoment669 B hB
  · have he : k = (670 : Fin 2886) := Fin.ext h670
    subst k
    rw [keyMomentRowsAt670]
    exact keyMoment670 B hB
  · have he : k = (671 : Fin 2886) := Fin.ext h671
    subst k
    rw [keyMomentRowsAt671]
    exact keyMoment671 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound20_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound20_e_oai
