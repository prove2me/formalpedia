-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound36_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:53:34.657707+00:00
-- url     : https://prove2.me/submissions/70601f4b-c41f-4b3e-a82b-b8700ab83e26

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E107
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14639 raw14639Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw14639 raw14639Labels = mixedMoment B raw14639step0 raw14639step0Labels := by
      have ha : raw14639step0 = (fun i j => raw14639 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14639step0 raw14639; decide +kernel
      have hl : raw14639step0Labels = raw14639Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14639 raw14639Labels permutation664 permutation3
    mixedMoment B raw14639step0 raw14639step0Labels = mixedMoment B raw14639step1 raw14639step1Labels := by
      have ha : raw14639step1 = -raw14639step0 := by apply Matrix.ext; change ∀ i j, raw14639step1 i j = -(raw14639step0 i j); unfold raw14639step1 raw14639step0; decide +kernel
      have hl : raw14639step1Labels = raw14639step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3064 node3064Labels := by rfl

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

theorem canonical3332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3332 raw3332Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3332 raw3332Labels = mixedMoment B raw3332step0 raw3332step0Labels := by
      have hz : ∀ j, raw3332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3332step0 = (fun i j => raw3332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3332step0 raw3332; decide +kernel
      have hl : raw3332step0Labels = raw3332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3332 raw3332Labels permutation346 hz
    mixedMoment B raw3332step0 raw3332step0Labels = mixedMoment B raw3332step1 raw3332step1Labels := by
      have hz : ∀ i, raw3332step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3332step1 = (fun i j => raw3332step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3332step1 raw3332step0; decide +kernel
      have hl : raw3332step1Labels = (fun j => raw3332step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3332step0 raw3332step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical317
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40589 raw40589Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw40589 raw40589Labels = mixedMoment B raw40589step0 raw40589step0Labels := by
      have hz : ∀ j, raw40589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40589step0 = (fun i j => raw40589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40589step0 raw40589; decide +kernel
      have hl : raw40589step0Labels = raw40589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40589 raw40589Labels permutation346 hz
    mixedMoment B raw40589step0 raw40589step0Labels = mixedMoment B raw40589step1 raw40589step1Labels := by
      have ha : raw40589step1 = (fun i j => raw40589step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40589step1 raw40589step0; decide +kernel
      have hl : raw40589step1Labels = raw40589step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40589step0 raw40589step0Labels permutation145 permutation3
    mixedMoment B raw40589step1 raw40589step1Labels = mixedMoment B raw40589step2 raw40589step2Labels := by
      have ha : raw40589step2 = -raw40589step1 := by apply Matrix.ext; change ∀ i j, raw40589step2 i j = -(raw40589step1 i j); unfold raw40589step2 raw40589step1; decide +kernel
      have hl : raw40589step2Labels = raw40589step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical40590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40590 raw40590Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw40590 raw40590Labels = mixedMoment B raw40590step0 raw40590step0Labels := by
      have hz : ∀ j, raw40590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40590step0 = (fun i j => raw40590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40590step0 raw40590; decide +kernel
      have hl : raw40590step0Labels = raw40590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40590 raw40590Labels permutation346 hz
    mixedMoment B raw40590step0 raw40590step0Labels = mixedMoment B raw40590step1 raw40590step1Labels := by
      have ha : raw40590step1 = (fun i j => raw40590step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40590step1 raw40590step0; decide +kernel
      have hl : raw40590step1Labels = raw40590step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40590step0 raw40590step0Labels permutation32 permutation3
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical40591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40591 raw40591Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw40591 raw40591Labels = mixedMoment B raw40591step0 raw40591step0Labels := by
      have hz : ∀ j, raw40591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40591step0 = (fun i j => raw40591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40591step0 raw40591; decide +kernel
      have hl : raw40591step0Labels = raw40591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40591 raw40591Labels permutation346 hz
    mixedMoment B raw40591step0 raw40591step0Labels = mixedMoment B raw40591step1 raw40591step1Labels := by
      have ha : raw40591step1 = (fun i j => raw40591step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40591step1 raw40591step0; decide +kernel
      have hl : raw40591step1Labels = raw40591step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40591step0 raw40591step0Labels permutation32 permutation3
    _ = mixedMoment B node3808 node3808Labels := by rfl

theorem canonical40592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40592 raw40592Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw40592 raw40592Labels = mixedMoment B raw40592step0 raw40592step0Labels := by
      have hz : ∀ j, raw40592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40592step0 = (fun i j => raw40592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40592step0 raw40592; decide +kernel
      have hl : raw40592step0Labels = raw40592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40592 raw40592Labels permutation346 hz
    mixedMoment B raw40592step0 raw40592step0Labels = mixedMoment B raw40592step1 raw40592step1Labels := by
      have ha : raw40592step1 = (fun i j => raw40592step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40592step1 raw40592step0; decide +kernel
      have hl : raw40592step1Labels = raw40592step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40592step0 raw40592step0Labels permutation32 permutation3
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical40593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40593 raw40593Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw40593 raw40593Labels = mixedMoment B raw40593step0 raw40593step0Labels := by
      have hz : ∀ j, raw40593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40593step0 = (fun i j => raw40593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40593step0 raw40593; decide +kernel
      have hl : raw40593step0Labels = raw40593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40593 raw40593Labels permutation346 hz
    mixedMoment B raw40593step0 raw40593step0Labels = mixedMoment B raw40593step1 raw40593step1Labels := by
      have ha : raw40593step1 = (fun i j => raw40593step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40593step1 raw40593step0; decide +kernel
      have hl : raw40593step1Labels = raw40593step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40593step0 raw40593step0Labels permutation32 permutation3
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical40594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40594 raw40594Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw40594 raw40594Labels = mixedMoment B raw40594step0 raw40594step0Labels := by
      have hz : ∀ j, raw40594 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40594step0 = (fun i j => raw40594 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40594step0 raw40594; decide +kernel
      have hl : raw40594step0Labels = raw40594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40594 raw40594Labels permutation346 hz
    mixedMoment B raw40594step0 raw40594step0Labels = mixedMoment B raw40594step1 raw40594step1Labels := by
      have ha : raw40594step1 = (fun i j => raw40594step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40594step1 raw40594step0; decide +kernel
      have hl : raw40594step1Labels = raw40594step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40594step0 raw40594step0Labels permutation32 permutation3
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical40595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40595 raw40595Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw40595 raw40595Labels = mixedMoment B raw40595step0 raw40595step0Labels := by
      have hz : ∀ j, raw40595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40595step0 = (fun i j => raw40595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40595step0 raw40595; decide +kernel
      have hl : raw40595step0Labels = raw40595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40595 raw40595Labels permutation346 hz
    mixedMoment B raw40595step0 raw40595step0Labels = mixedMoment B raw40595step1 raw40595step1Labels := by
      have ha : raw40595step1 = (fun i j => raw40595step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40595step1 raw40595step0; decide +kernel
      have hl : raw40595step1Labels = raw40595step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40595step0 raw40595step0Labels permutation32 permutation3
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical40596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40596 raw40596Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw40596 raw40596Labels = mixedMoment B raw40596step0 raw40596step0Labels := by
      have ha : raw40596step0 = (fun i j => raw40596 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40596step0 raw40596; decide +kernel
      have hl : raw40596step0Labels = raw40596Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40596 raw40596Labels permutation152 permutation3
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical40597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40597 raw40597Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw40597 raw40597Labels = mixedMoment B raw40597step0 raw40597step0Labels := by
      have ha : raw40597step0 = (fun i j => raw40597 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40597step0 raw40597; decide +kernel
      have hl : raw40597step0Labels = raw40597Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40597 raw40597Labels permutation152 permutation3
    _ = mixedMoment B node3801 node3801Labels := by rfl

theorem canonical40598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40598 raw40598Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw40598 raw40598Labels = mixedMoment B raw40598step0 raw40598step0Labels := by
      have ha : raw40598step0 = (fun i j => raw40598 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40598step0 raw40598; decide +kernel
      have hl : raw40598step0Labels = raw40598Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40598 raw40598Labels permutation152 permutation3
    _ = mixedMoment B node3805 node3805Labels := by rfl

theorem canonical40599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40599 raw40599Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw40599 raw40599Labels = mixedMoment B raw40599step0 raw40599step0Labels := by
      have ha : raw40599step0 = (fun i j => raw40599 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40599step0 raw40599; decide +kernel
      have hl : raw40599step0Labels = raw40599Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40599 raw40599Labels permutation152 permutation3
    _ = mixedMoment B node3806 node3806Labels := by rfl

theorem canonical40600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40600 raw40600Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw40600 raw40600Labels = mixedMoment B raw40600step0 raw40600step0Labels := by
      have ha : raw40600step0 = (fun i j => raw40600 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40600step0 raw40600; decide +kernel
      have hl : raw40600step0Labels = raw40600Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40600 raw40600Labels permutation152 permutation3
    _ = mixedMoment B node3812 node3812Labels := by rfl

theorem canonical40601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40601 raw40601Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw40601 raw40601Labels = mixedMoment B raw40601step0 raw40601step0Labels := by
      have hz : ∀ j, raw40601 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40601step0 = (fun i j => raw40601 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40601step0 raw40601; decide +kernel
      have hl : raw40601step0Labels = raw40601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40601 raw40601Labels permutation520 hz
    mixedMoment B raw40601step0 raw40601step0Labels = mixedMoment B raw40601step1 raw40601step1Labels := by
      have hz : ∀ j, raw40601step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40601step1 = (fun i j => raw40601step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40601step1 raw40601step0; decide +kernel
      have hl : raw40601step1Labels = raw40601step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40601step0 raw40601step0Labels permutation104 hz
    mixedMoment B raw40601step1 raw40601step1Labels = mixedMoment B raw40601step2 raw40601step2Labels := by
      have ha : raw40601step2 = (fun i j => raw40601step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40601step2 raw40601step1; decide +kernel
      have hl : raw40601step2Labels = raw40601step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40601step1 raw40601step1Labels permutation31 permutation3
    mixedMoment B raw40601step2 raw40601step2Labels = mixedMoment B raw40601step3 raw40601step3Labels := by
      have ha : raw40601step3 = -raw40601step2 := by apply Matrix.ext; change ∀ i j, raw40601step3 i j = -(raw40601step2 i j); unfold raw40601step3 raw40601step2; decide +kernel
      have hl : raw40601step3Labels = raw40601step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical40602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40602 raw40602Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw40602 raw40602Labels = mixedMoment B raw40602step0 raw40602step0Labels := by
      have hz : ∀ j, raw40602 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40602step0 = (fun i j => raw40602 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40602step0 raw40602; decide +kernel
      have hl : raw40602step0Labels = raw40602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40602 raw40602Labels permutation434 hz
    mixedMoment B raw40602step0 raw40602step0Labels = mixedMoment B raw40602step1 raw40602step1Labels := by
      have ha : raw40602step1 = (fun i j => raw40602step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40602step1 raw40602step0; decide +kernel
      have hl : raw40602step1Labels = raw40602step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40602step0 raw40602step0Labels permutation151 permutation3
    mixedMoment B raw40602step1 raw40602step1Labels = mixedMoment B raw40602step2 raw40602step2Labels := by
      have ha : raw40602step2 = -raw40602step1 := by apply Matrix.ext; change ∀ i j, raw40602step2 i j = -(raw40602step1 i j); unfold raw40602step2 raw40602step1; decide +kernel
      have hl : raw40602step2Labels = raw40602step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical40603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40603 raw40603Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw40603 raw40603Labels = mixedMoment B raw40603step0 raw40603step0Labels := by
      have hz : ∀ j, raw40603 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40603step0 = (fun i j => raw40603 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40603step0 raw40603; decide +kernel
      have hl : raw40603step0Labels = raw40603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40603 raw40603Labels permutation434 hz
    mixedMoment B raw40603step0 raw40603step0Labels = mixedMoment B raw40603step1 raw40603step1Labels := by
      have ha : raw40603step1 = (fun i j => raw40603step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40603step1 raw40603step0; decide +kernel
      have hl : raw40603step1Labels = raw40603step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40603step0 raw40603step0Labels permutation151 permutation3
    mixedMoment B raw40603step1 raw40603step1Labels = mixedMoment B raw40603step2 raw40603step2Labels := by
      have ha : raw40603step2 = -raw40603step1 := by apply Matrix.ext; change ∀ i j, raw40603step2 i j = -(raw40603step1 i j); unfold raw40603step2 raw40603step1; decide +kernel
      have hl : raw40603step2Labels = raw40603step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3038 node3038Labels := by rfl

theorem canonical40604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40604 raw40604Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw40604 raw40604Labels = mixedMoment B raw40604step0 raw40604step0Labels := by
      have hz : ∀ j, raw40604 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40604step0 = (fun i j => raw40604 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40604step0 raw40604; decide +kernel
      have hl : raw40604step0Labels = raw40604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40604 raw40604Labels permutation434 hz
    mixedMoment B raw40604step0 raw40604step0Labels = mixedMoment B raw40604step1 raw40604step1Labels := by
      have ha : raw40604step1 = (fun i j => raw40604step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40604step1 raw40604step0; decide +kernel
      have hl : raw40604step1Labels = raw40604step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40604step0 raw40604step0Labels permutation151 permutation3
    mixedMoment B raw40604step1 raw40604step1Labels = mixedMoment B raw40604step2 raw40604step2Labels := by
      have ha : raw40604step2 = -raw40604step1 := by apply Matrix.ext; change ∀ i j, raw40604step2 i j = -(raw40604step1 i j); unfold raw40604step2 raw40604step1; decide +kernel
      have hl : raw40604step2Labels = raw40604step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical40605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40605 raw40605Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw40605 raw40605Labels = mixedMoment B raw40605step0 raw40605step0Labels := by
      have hz : ∀ j, raw40605 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40605step0 = (fun i j => raw40605 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40605step0 raw40605; decide +kernel
      have hl : raw40605step0Labels = raw40605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40605 raw40605Labels permutation434 hz
    mixedMoment B raw40605step0 raw40605step0Labels = mixedMoment B raw40605step1 raw40605step1Labels := by
      have ha : raw40605step1 = (fun i j => raw40605step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40605step1 raw40605step0; decide +kernel
      have hl : raw40605step1Labels = raw40605step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40605step0 raw40605step0Labels permutation32 permutation3
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical40606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40606 raw40606Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw40606 raw40606Labels = mixedMoment B raw40606step0 raw40606step0Labels := by
      have hz : ∀ j, raw40606 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40606step0 = (fun i j => raw40606 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40606step0 raw40606; decide +kernel
      have hl : raw40606step0Labels = raw40606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40606 raw40606Labels permutation434 hz
    mixedMoment B raw40606step0 raw40606step0Labels = mixedMoment B raw40606step1 raw40606step1Labels := by
      have ha : raw40606step1 = (fun i j => raw40606step0 (permutation110 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40606step1 raw40606step0; decide +kernel
      have hl : raw40606step1Labels = raw40606step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40606step0 raw40606step0Labels permutation110 permutation6
    mixedMoment B raw40606step1 raw40606step1Labels = mixedMoment B raw40606step2 raw40606step2Labels := by
      have ha : raw40606step2 = -raw40606step1 := by apply Matrix.ext; change ∀ i j, raw40606step2 i j = -(raw40606step1 i j); unfold raw40606step2 raw40606step1; decide +kernel
      have hl : raw40606step2Labels = raw40606step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical40607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40607 raw40607Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw40607 raw40607Labels = mixedMoment B raw40607step0 raw40607step0Labels := by
      have ha : raw40607step0 = (fun i j => raw40607 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40607step0 raw40607; decide +kernel
      have hl : raw40607step0Labels = raw40607Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40607 raw40607Labels permutation152 permutation3
    _ = mixedMoment B node3837 node3837Labels := by rfl

theorem canonical40608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40608 raw40608Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw40608 raw40608Labels = mixedMoment B raw40608step0 raw40608step0Labels := by
      have ha : raw40608step0 = (fun i j => raw40608 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40608step0 raw40608; decide +kernel
      have hl : raw40608step0Labels = raw40608Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40608 raw40608Labels permutation152 permutation3
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical40609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40609 raw40609Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw40609 raw40609Labels = mixedMoment B raw40609step0 raw40609step0Labels := by
      have ha : raw40609step0 = (fun i j => raw40609 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40609step0 raw40609; decide +kernel
      have hl : raw40609step0Labels = raw40609Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40609 raw40609Labels permutation152 permutation3
    _ = mixedMoment B node3839 node3839Labels := by rfl

theorem canonical40610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40610 raw40610Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw40610 raw40610Labels = mixedMoment B raw40610step0 raw40610step0Labels := by
      have ha : raw40610step0 = (fun i j => raw40610 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40610step0 raw40610; decide +kernel
      have hl : raw40610step0Labels = raw40610Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40610 raw40610Labels permutation152 permutation3
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical40611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40611 raw40611Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw40611 raw40611Labels = mixedMoment B raw40611step0 raw40611step0Labels := by
      have ha : raw40611step0 = (fun i j => raw40611 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40611step0 raw40611; decide +kernel
      have hl : raw40611step0Labels = raw40611Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40611 raw40611Labels permutation152 permutation3
    _ = mixedMoment B node3841 node3841Labels := by rfl

theorem canonical40612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40612 raw40612Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw40612 raw40612Labels = mixedMoment B raw40612step0 raw40612step0Labels := by
      have ha : raw40612step0 = (fun i j => raw40612 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40612step0 raw40612; decide +kernel
      have hl : raw40612step0Labels = raw40612Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40612 raw40612Labels permutation152 permutation3
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical40613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40613 raw40613Labels = mixedMoment B node3844 node3844Labels := by
  calc
    mixedMoment B raw40613 raw40613Labels = mixedMoment B raw40613step0 raw40613step0Labels := by
      have ha : raw40613step0 = (fun i j => raw40613 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40613step0 raw40613; decide +kernel
      have hl : raw40613step0Labels = raw40613Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40613 raw40613Labels permutation152 permutation3
    _ = mixedMoment B node3844 node3844Labels := by rfl

theorem canonical40614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40614 raw40614Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw40614 raw40614Labels = mixedMoment B raw40614step0 raw40614step0Labels := by
      have hz : ∀ j, raw40614 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40614step0 = (fun i j => raw40614 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40614step0 raw40614; decide +kernel
      have hl : raw40614step0Labels = raw40614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40614 raw40614Labels permutation434 hz
    mixedMoment B raw40614step0 raw40614step0Labels = mixedMoment B raw40614step1 raw40614step1Labels := by
      have hz : ∀ j, raw40614step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40614step1 = (fun i j => raw40614step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40614step1 raw40614step0; decide +kernel
      have hl : raw40614step1Labels = raw40614step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40614step0 raw40614step0Labels permutation80 hz
    mixedMoment B raw40614step1 raw40614step1Labels = mixedMoment B raw40614step2 raw40614step2Labels := by
      have ha : raw40614step2 = (fun i j => raw40614step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40614step2 raw40614step1; decide +kernel
      have hl : raw40614step2Labels = raw40614step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40614step1 raw40614step1Labels permutation26 permutation6
    _ = mixedMoment B node3052 node3052Labels := by rfl

theorem canonical40615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40615 raw40615Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw40615 raw40615Labels = mixedMoment B raw40615step0 raw40615step0Labels := by
      have hz : ∀ j, raw40615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40615step0 = (fun i j => raw40615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40615step0 raw40615; decide +kernel
      have hl : raw40615step0Labels = raw40615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40615 raw40615Labels permutation346 hz
    mixedMoment B raw40615step0 raw40615step0Labels = mixedMoment B raw40615step1 raw40615step1Labels := by
      have ha : raw40615step1 = (fun i j => raw40615step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40615step1 raw40615step0; decide +kernel
      have hl : raw40615step1Labels = raw40615step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40615step0 raw40615step0Labels permutation32 permutation3
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical40616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40616 raw40616Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw40616 raw40616Labels = mixedMoment B raw40616step0 raw40616step0Labels := by
      have hz : ∀ j, raw40616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40616step0 = (fun i j => raw40616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40616step0 raw40616; decide +kernel
      have hl : raw40616step0Labels = raw40616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40616 raw40616Labels permutation346 hz
    mixedMoment B raw40616step0 raw40616step0Labels = mixedMoment B raw40616step1 raw40616step1Labels := by
      have ha : raw40616step1 = (fun i j => raw40616step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40616step1 raw40616step0; decide +kernel
      have hl : raw40616step1Labels = raw40616step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40616step0 raw40616step0Labels permutation128 permutation6
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical40617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40617 raw40617Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw40617 raw40617Labels = mixedMoment B raw40617step0 raw40617step0Labels := by
      have hz : ∀ j, raw40617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40617step0 = (fun i j => raw40617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40617step0 raw40617; decide +kernel
      have hl : raw40617step0Labels = raw40617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40617 raw40617Labels permutation346 hz
    mixedMoment B raw40617step0 raw40617step0Labels = mixedMoment B raw40617step1 raw40617step1Labels := by
      have ha : raw40617step1 = (fun i j => raw40617step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40617step1 raw40617step0; decide +kernel
      have hl : raw40617step1Labels = raw40617step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40617step0 raw40617step0Labels permutation32 permutation3
    _ = mixedMoment B node3854 node3854Labels := by rfl

theorem canonical40618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40618 raw40618Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw40618 raw40618Labels = mixedMoment B raw40618step0 raw40618step0Labels := by
      have hz : ∀ j, raw40618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40618step0 = (fun i j => raw40618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40618step0 raw40618; decide +kernel
      have hl : raw40618step0Labels = raw40618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40618 raw40618Labels permutation346 hz
    mixedMoment B raw40618step0 raw40618step0Labels = mixedMoment B raw40618step1 raw40618step1Labels := by
      have ha : raw40618step1 = (fun i j => raw40618step0 (permutation132 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40618step1 raw40618step0; decide +kernel
      have hl : raw40618step1Labels = raw40618step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40618step0 raw40618step0Labels permutation132 permutation6
    _ = mixedMoment B node3038 node3038Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1152) =
      Integer.Sparse.eval keyMomentRow1152 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1152).leftCharge (GramAssembly.key 1152).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3077) := by
    have ha : gramCharges (GramAssembly.key 1152).leftCharge (GramAssembly.key 1152).rightCharge = raw40589 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40589Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40589 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1152).leftCharge (GramAssembly.key 1152).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1152, Integer.Sparse.eval]

theorem keyMoment1153 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1153) =
      Integer.Sparse.eval keyMomentRow1153 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1153).leftCharge (GramAssembly.key 1153).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3807) := by
    have ha : gramCharges (GramAssembly.key 1153).leftCharge (GramAssembly.key 1153).rightCharge = raw40590 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40590Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40590 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1153).leftCharge (GramAssembly.key 1153).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1153, Integer.Sparse.eval]

theorem keyMoment1154 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1154) =
      Integer.Sparse.eval keyMomentRow1154 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1154).leftCharge (GramAssembly.key 1154).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3808) := by
    have ha : gramCharges (GramAssembly.key 1154).leftCharge (GramAssembly.key 1154).rightCharge = raw40591 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40591Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40591 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1154).leftCharge (GramAssembly.key 1154).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1154, Integer.Sparse.eval]

theorem keyMoment1155 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1155) =
      Integer.Sparse.eval keyMomentRow1155 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1155).leftCharge (GramAssembly.key 1155).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3809) := by
    have ha : gramCharges (GramAssembly.key 1155).leftCharge (GramAssembly.key 1155).rightCharge = raw40592 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40592Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40592 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1155).leftCharge (GramAssembly.key 1155).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1155, Integer.Sparse.eval]

theorem keyMoment1156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1156) =
      Integer.Sparse.eval keyMomentRow1156 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1156).leftCharge (GramAssembly.key 1156).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3813) := by
    have ha : gramCharges (GramAssembly.key 1156).leftCharge (GramAssembly.key 1156).rightCharge = raw40593 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40593Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40593 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1156).leftCharge (GramAssembly.key 1156).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1156, Integer.Sparse.eval]

theorem keyMoment1157 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1157) =
      Integer.Sparse.eval keyMomentRow1157 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1157).leftCharge (GramAssembly.key 1157).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3814) := by
    have ha : gramCharges (GramAssembly.key 1157).leftCharge (GramAssembly.key 1157).rightCharge = raw40594 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40594Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40594 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1157).leftCharge (GramAssembly.key 1157).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1157, Integer.Sparse.eval]

theorem keyMoment1158 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1158) =
      Integer.Sparse.eval keyMomentRow1158 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1158).leftCharge (GramAssembly.key 1158).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3816) := by
    have ha : gramCharges (GramAssembly.key 1158).leftCharge (GramAssembly.key 1158).rightCharge = raw40595 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40595Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40595 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1158).leftCharge (GramAssembly.key 1158).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1158, Integer.Sparse.eval]

theorem keyMoment1159 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1159) =
      Integer.Sparse.eval keyMomentRow1159 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1159).leftCharge (GramAssembly.key 1159).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4091) := by
    have ha : gramCharges (GramAssembly.key 1159).leftCharge (GramAssembly.key 1159).rightCharge = raw3332 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw3332Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical3332 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1159).leftCharge (GramAssembly.key 1159).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1159, Integer.Sparse.eval]

theorem keyMoment1160 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1160) =
      Integer.Sparse.eval keyMomentRow1160 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1160).leftCharge (GramAssembly.key 1160).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3800) := by
    have ha : gramCharges (GramAssembly.key 1160).leftCharge (GramAssembly.key 1160).rightCharge = raw40596 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40596Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40596 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1160).leftCharge (GramAssembly.key 1160).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1160, Integer.Sparse.eval]

theorem keyMoment1161 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1161) =
      Integer.Sparse.eval keyMomentRow1161 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1161).leftCharge (GramAssembly.key 1161).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3801) := by
    have ha : gramCharges (GramAssembly.key 1161).leftCharge (GramAssembly.key 1161).rightCharge = raw40597 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40597Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40597 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1161).leftCharge (GramAssembly.key 1161).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1161, Integer.Sparse.eval]

theorem keyMoment1162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1162) =
      Integer.Sparse.eval keyMomentRow1162 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1162).leftCharge (GramAssembly.key 1162).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3805) := by
    have ha : gramCharges (GramAssembly.key 1162).leftCharge (GramAssembly.key 1162).rightCharge = raw40598 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40598Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40598 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1162).leftCharge (GramAssembly.key 1162).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1162, Integer.Sparse.eval]

theorem keyMoment1163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1163) =
      Integer.Sparse.eval keyMomentRow1163 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1163).leftCharge (GramAssembly.key 1163).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3806) := by
    have ha : gramCharges (GramAssembly.key 1163).leftCharge (GramAssembly.key 1163).rightCharge = raw40599 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40599Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40599 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1163).leftCharge (GramAssembly.key 1163).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1163, Integer.Sparse.eval]

theorem keyMoment1164 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1164) =
      Integer.Sparse.eval keyMomentRow1164 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1164).leftCharge (GramAssembly.key 1164).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3812) := by
    have ha : gramCharges (GramAssembly.key 1164).leftCharge (GramAssembly.key 1164).rightCharge = raw40600 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40600Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40600 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1164).leftCharge (GramAssembly.key 1164).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1164, Integer.Sparse.eval]

theorem keyMoment1165 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1165) =
      Integer.Sparse.eval keyMomentRow1165 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1165).leftCharge (GramAssembly.key 1165).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2264) := by
    have ha : gramCharges (GramAssembly.key 1165).leftCharge (GramAssembly.key 1165).rightCharge = raw40601 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40601Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40601 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1165).leftCharge (GramAssembly.key 1165).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1165, Integer.Sparse.eval]

theorem keyMoment1166 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1166) =
      Integer.Sparse.eval keyMomentRow1166 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1166).leftCharge (GramAssembly.key 1166).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2722) := by
    have ha : gramCharges (GramAssembly.key 1166).leftCharge (GramAssembly.key 1166).rightCharge = raw40602 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40602Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40602 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1166).leftCharge (GramAssembly.key 1166).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1166, Integer.Sparse.eval]

theorem keyMoment1167 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1167) =
      Integer.Sparse.eval keyMomentRow1167 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1167).leftCharge (GramAssembly.key 1167).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3038) := by
    have ha : gramCharges (GramAssembly.key 1167).leftCharge (GramAssembly.key 1167).rightCharge = raw40603 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40603Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40603 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1167).leftCharge (GramAssembly.key 1167).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1167, Integer.Sparse.eval]

theorem keyMoment1168 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1168) =
      Integer.Sparse.eval keyMomentRow1168 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1168).leftCharge (GramAssembly.key 1168).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3807) := by
    have ha : gramCharges (GramAssembly.key 1168).leftCharge (GramAssembly.key 1168).rightCharge = raw40604 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40604Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40604 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1168).leftCharge (GramAssembly.key 1168).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1168, Integer.Sparse.eval]

theorem keyMoment1169 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1169) =
      Integer.Sparse.eval keyMomentRow1169 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1169).leftCharge (GramAssembly.key 1169).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3845) := by
    have ha : gramCharges (GramAssembly.key 1169).leftCharge (GramAssembly.key 1169).rightCharge = raw40605 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40605Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40605 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1169).leftCharge (GramAssembly.key 1169).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1169, Integer.Sparse.eval]

theorem keyMoment1170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1170) =
      Integer.Sparse.eval keyMomentRow1170 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1170).leftCharge (GramAssembly.key 1170).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3541) := by
    have ha : gramCharges (GramAssembly.key 1170).leftCharge (GramAssembly.key 1170).rightCharge = raw40606 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40606Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40606 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1170).leftCharge (GramAssembly.key 1170).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1170, Integer.Sparse.eval]

theorem keyMoment1171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1171) =
      Integer.Sparse.eval keyMomentRow1171 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1171).leftCharge (GramAssembly.key 1171).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3064) := by
    have ha : gramCharges (GramAssembly.key 1171).leftCharge (GramAssembly.key 1171).rightCharge = raw14639 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw14639Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical14639 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1171).leftCharge (GramAssembly.key 1171).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1171, Integer.Sparse.eval]

theorem keyMoment1172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1172) =
      Integer.Sparse.eval keyMomentRow1172 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1172).leftCharge (GramAssembly.key 1172).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3837) := by
    have ha : gramCharges (GramAssembly.key 1172).leftCharge (GramAssembly.key 1172).rightCharge = raw40607 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40607Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40607 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1172).leftCharge (GramAssembly.key 1172).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1172, Integer.Sparse.eval]

theorem keyMoment1173 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1173) =
      Integer.Sparse.eval keyMomentRow1173 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1173).leftCharge (GramAssembly.key 1173).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3838) := by
    have ha : gramCharges (GramAssembly.key 1173).leftCharge (GramAssembly.key 1173).rightCharge = raw40608 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40608Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40608 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1173).leftCharge (GramAssembly.key 1173).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1173, Integer.Sparse.eval]

theorem keyMoment1174 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1174) =
      Integer.Sparse.eval keyMomentRow1174 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1174).leftCharge (GramAssembly.key 1174).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3839) := by
    have ha : gramCharges (GramAssembly.key 1174).leftCharge (GramAssembly.key 1174).rightCharge = raw40609 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40609Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40609 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1174).leftCharge (GramAssembly.key 1174).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1174, Integer.Sparse.eval]

theorem keyMoment1175 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1175) =
      Integer.Sparse.eval keyMomentRow1175 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1175).leftCharge (GramAssembly.key 1175).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3840) := by
    have ha : gramCharges (GramAssembly.key 1175).leftCharge (GramAssembly.key 1175).rightCharge = raw40610 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40610Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40610 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1175).leftCharge (GramAssembly.key 1175).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1175, Integer.Sparse.eval]

theorem keyMoment1176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1176) =
      Integer.Sparse.eval keyMomentRow1176 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1176).leftCharge (GramAssembly.key 1176).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3841) := by
    have ha : gramCharges (GramAssembly.key 1176).leftCharge (GramAssembly.key 1176).rightCharge = raw40611 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40611Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40611 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1176).leftCharge (GramAssembly.key 1176).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1176, Integer.Sparse.eval]

theorem keyMoment1177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1177) =
      Integer.Sparse.eval keyMomentRow1177 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1177).leftCharge (GramAssembly.key 1177).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3843) := by
    have ha : gramCharges (GramAssembly.key 1177).leftCharge (GramAssembly.key 1177).rightCharge = raw40612 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40612Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40612 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1177).leftCharge (GramAssembly.key 1177).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1177, Integer.Sparse.eval]

theorem keyMoment1178 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1178) =
      Integer.Sparse.eval keyMomentRow1178 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1178).leftCharge (GramAssembly.key 1178).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3844) := by
    have ha : gramCharges (GramAssembly.key 1178).leftCharge (GramAssembly.key 1178).rightCharge = raw40613 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40613Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40613 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1178).leftCharge (GramAssembly.key 1178).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1178, Integer.Sparse.eval]

theorem keyMoment1179 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1179) =
      Integer.Sparse.eval keyMomentRow1179 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1179).leftCharge (GramAssembly.key 1179).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3052) := by
    have ha : gramCharges (GramAssembly.key 1179).leftCharge (GramAssembly.key 1179).rightCharge = raw40614 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40614Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40614 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1179).leftCharge (GramAssembly.key 1179).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1179, Integer.Sparse.eval]

theorem keyMoment1180 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1180) =
      Integer.Sparse.eval keyMomentRow1180 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1180).leftCharge (GramAssembly.key 1180).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3850) := by
    have ha : gramCharges (GramAssembly.key 1180).leftCharge (GramAssembly.key 1180).rightCharge = raw40615 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40615Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40615 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1180).leftCharge (GramAssembly.key 1180).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1180, Integer.Sparse.eval]

theorem keyMoment1181 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1181) =
      Integer.Sparse.eval keyMomentRow1181 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1181).leftCharge (GramAssembly.key 1181).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3051) := by
    have ha : gramCharges (GramAssembly.key 1181).leftCharge (GramAssembly.key 1181).rightCharge = raw40616 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40616Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40616 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1181).leftCharge (GramAssembly.key 1181).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1181, Integer.Sparse.eval]

theorem keyMoment1182 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1182) =
      Integer.Sparse.eval keyMomentRow1182 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1182).leftCharge (GramAssembly.key 1182).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3854) := by
    have ha : gramCharges (GramAssembly.key 1182).leftCharge (GramAssembly.key 1182).rightCharge = raw40617 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40617Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40617 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1182).leftCharge (GramAssembly.key 1182).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1182, Integer.Sparse.eval]

theorem keyMoment1183 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1183) =
      Integer.Sparse.eval keyMomentRow1183 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1183).leftCharge (GramAssembly.key 1183).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3038) := by
    have ha : gramCharges (GramAssembly.key 1183).leftCharge (GramAssembly.key 1183).rightCharge = raw40618 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40618Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40618 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1183).leftCharge (GramAssembly.key 1183).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1183, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1152 : keyMomentRows (1152 : Fin 2886) =
    keyMomentRow1152 := by decide +kernel

theorem keyMomentRowsAt1153 : keyMomentRows (1153 : Fin 2886) =
    keyMomentRow1153 := by decide +kernel

theorem keyMomentRowsAt1154 : keyMomentRows (1154 : Fin 2886) =
    keyMomentRow1154 := by decide +kernel

theorem keyMomentRowsAt1155 : keyMomentRows (1155 : Fin 2886) =
    keyMomentRow1155 := by decide +kernel

theorem keyMomentRowsAt1156 : keyMomentRows (1156 : Fin 2886) =
    keyMomentRow1156 := by decide +kernel

theorem keyMomentRowsAt1157 : keyMomentRows (1157 : Fin 2886) =
    keyMomentRow1157 := by decide +kernel

theorem keyMomentRowsAt1158 : keyMomentRows (1158 : Fin 2886) =
    keyMomentRow1158 := by decide +kernel

theorem keyMomentRowsAt1159 : keyMomentRows (1159 : Fin 2886) =
    keyMomentRow1159 := by decide +kernel

theorem keyMomentRowsAt1160 : keyMomentRows (1160 : Fin 2886) =
    keyMomentRow1160 := by decide +kernel

theorem keyMomentRowsAt1161 : keyMomentRows (1161 : Fin 2886) =
    keyMomentRow1161 := by decide +kernel

theorem keyMomentRowsAt1162 : keyMomentRows (1162 : Fin 2886) =
    keyMomentRow1162 := by decide +kernel

theorem keyMomentRowsAt1163 : keyMomentRows (1163 : Fin 2886) =
    keyMomentRow1163 := by decide +kernel

theorem keyMomentRowsAt1164 : keyMomentRows (1164 : Fin 2886) =
    keyMomentRow1164 := by decide +kernel

theorem keyMomentRowsAt1165 : keyMomentRows (1165 : Fin 2886) =
    keyMomentRow1165 := by decide +kernel

theorem keyMomentRowsAt1166 : keyMomentRows (1166 : Fin 2886) =
    keyMomentRow1166 := by decide +kernel

theorem keyMomentRowsAt1167 : keyMomentRows (1167 : Fin 2886) =
    keyMomentRow1167 := by decide +kernel

theorem keyMomentRowsAt1168 : keyMomentRows (1168 : Fin 2886) =
    keyMomentRow1168 := by decide +kernel

theorem keyMomentRowsAt1169 : keyMomentRows (1169 : Fin 2886) =
    keyMomentRow1169 := by decide +kernel

theorem keyMomentRowsAt1170 : keyMomentRows (1170 : Fin 2886) =
    keyMomentRow1170 := by decide +kernel

theorem keyMomentRowsAt1171 : keyMomentRows (1171 : Fin 2886) =
    keyMomentRow1171 := by decide +kernel

theorem keyMomentRowsAt1172 : keyMomentRows (1172 : Fin 2886) =
    keyMomentRow1172 := by decide +kernel

theorem keyMomentRowsAt1173 : keyMomentRows (1173 : Fin 2886) =
    keyMomentRow1173 := by decide +kernel

theorem keyMomentRowsAt1174 : keyMomentRows (1174 : Fin 2886) =
    keyMomentRow1174 := by decide +kernel

theorem keyMomentRowsAt1175 : keyMomentRows (1175 : Fin 2886) =
    keyMomentRow1175 := by decide +kernel

theorem keyMomentRowsAt1176 : keyMomentRows (1176 : Fin 2886) =
    keyMomentRow1176 := by decide +kernel

theorem keyMomentRowsAt1177 : keyMomentRows (1177 : Fin 2886) =
    keyMomentRow1177 := by decide +kernel

theorem keyMomentRowsAt1178 : keyMomentRows (1178 : Fin 2886) =
    keyMomentRow1178 := by decide +kernel

theorem keyMomentRowsAt1179 : keyMomentRows (1179 : Fin 2886) =
    keyMomentRow1179 := by decide +kernel

theorem keyMomentRowsAt1180 : keyMomentRows (1180 : Fin 2886) =
    keyMomentRow1180 := by decide +kernel

theorem keyMomentRowsAt1181 : keyMomentRows (1181 : Fin 2886) =
    keyMomentRow1181 := by decide +kernel

theorem keyMomentRowsAt1182 : keyMomentRows (1182 : Fin 2886) =
    keyMomentRow1182 := by decide +kernel

theorem keyMomentRowsAt1183 : keyMomentRows (1183 : Fin 2886) =
    keyMomentRow1183 := by decide +kernel

theorem keyMomentChunkSound36_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 36) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1152 ∨ k.val = 1153 ∨ k.val = 1154 ∨ k.val = 1155 ∨ k.val = 1156 ∨ k.val = 1157 ∨ k.val = 1158 ∨ k.val = 1159 ∨ k.val = 1160 ∨ k.val = 1161 ∨ k.val = 1162 ∨ k.val = 1163 ∨ k.val = 1164 ∨ k.val = 1165 ∨ k.val = 1166 ∨ k.val = 1167 ∨ k.val = 1168 ∨ k.val = 1169 ∨ k.val = 1170 ∨ k.val = 1171 ∨ k.val = 1172 ∨ k.val = 1173 ∨ k.val = 1174 ∨ k.val = 1175 ∨ k.val = 1176 ∨ k.val = 1177 ∨ k.val = 1178 ∨ k.val = 1179 ∨ k.val = 1180 ∨ k.val = 1181 ∨ k.val = 1182 ∨ k.val = 1183 := by omega
  rcases heq with h1152 | h1153 | h1154 | h1155 | h1156 | h1157 | h1158 | h1159 | h1160 | h1161 | h1162 | h1163 | h1164 | h1165 | h1166 | h1167 | h1168 | h1169 | h1170 | h1171 | h1172 | h1173 | h1174 | h1175 | h1176 | h1177 | h1178 | h1179 | h1180 | h1181 | h1182 | h1183
  · have he : k = (1152 : Fin 2886) := Fin.ext h1152
    subst k
    rw [keyMomentRowsAt1152]
    exact keyMoment1152 B hB
  · have he : k = (1153 : Fin 2886) := Fin.ext h1153
    subst k
    rw [keyMomentRowsAt1153]
    exact keyMoment1153 B hB
  · have he : k = (1154 : Fin 2886) := Fin.ext h1154
    subst k
    rw [keyMomentRowsAt1154]
    exact keyMoment1154 B hB
  · have he : k = (1155 : Fin 2886) := Fin.ext h1155
    subst k
    rw [keyMomentRowsAt1155]
    exact keyMoment1155 B hB
  · have he : k = (1156 : Fin 2886) := Fin.ext h1156
    subst k
    rw [keyMomentRowsAt1156]
    exact keyMoment1156 B hB
  · have he : k = (1157 : Fin 2886) := Fin.ext h1157
    subst k
    rw [keyMomentRowsAt1157]
    exact keyMoment1157 B hB
  · have he : k = (1158 : Fin 2886) := Fin.ext h1158
    subst k
    rw [keyMomentRowsAt1158]
    exact keyMoment1158 B hB
  · have he : k = (1159 : Fin 2886) := Fin.ext h1159
    subst k
    rw [keyMomentRowsAt1159]
    exact keyMoment1159 B hB
  · have he : k = (1160 : Fin 2886) := Fin.ext h1160
    subst k
    rw [keyMomentRowsAt1160]
    exact keyMoment1160 B hB
  · have he : k = (1161 : Fin 2886) := Fin.ext h1161
    subst k
    rw [keyMomentRowsAt1161]
    exact keyMoment1161 B hB
  · have he : k = (1162 : Fin 2886) := Fin.ext h1162
    subst k
    rw [keyMomentRowsAt1162]
    exact keyMoment1162 B hB
  · have he : k = (1163 : Fin 2886) := Fin.ext h1163
    subst k
    rw [keyMomentRowsAt1163]
    exact keyMoment1163 B hB
  · have he : k = (1164 : Fin 2886) := Fin.ext h1164
    subst k
    rw [keyMomentRowsAt1164]
    exact keyMoment1164 B hB
  · have he : k = (1165 : Fin 2886) := Fin.ext h1165
    subst k
    rw [keyMomentRowsAt1165]
    exact keyMoment1165 B hB
  · have he : k = (1166 : Fin 2886) := Fin.ext h1166
    subst k
    rw [keyMomentRowsAt1166]
    exact keyMoment1166 B hB
  · have he : k = (1167 : Fin 2886) := Fin.ext h1167
    subst k
    rw [keyMomentRowsAt1167]
    exact keyMoment1167 B hB
  · have he : k = (1168 : Fin 2886) := Fin.ext h1168
    subst k
    rw [keyMomentRowsAt1168]
    exact keyMoment1168 B hB
  · have he : k = (1169 : Fin 2886) := Fin.ext h1169
    subst k
    rw [keyMomentRowsAt1169]
    exact keyMoment1169 B hB
  · have he : k = (1170 : Fin 2886) := Fin.ext h1170
    subst k
    rw [keyMomentRowsAt1170]
    exact keyMoment1170 B hB
  · have he : k = (1171 : Fin 2886) := Fin.ext h1171
    subst k
    rw [keyMomentRowsAt1171]
    exact keyMoment1171 B hB
  · have he : k = (1172 : Fin 2886) := Fin.ext h1172
    subst k
    rw [keyMomentRowsAt1172]
    exact keyMoment1172 B hB
  · have he : k = (1173 : Fin 2886) := Fin.ext h1173
    subst k
    rw [keyMomentRowsAt1173]
    exact keyMoment1173 B hB
  · have he : k = (1174 : Fin 2886) := Fin.ext h1174
    subst k
    rw [keyMomentRowsAt1174]
    exact keyMoment1174 B hB
  · have he : k = (1175 : Fin 2886) := Fin.ext h1175
    subst k
    rw [keyMomentRowsAt1175]
    exact keyMoment1175 B hB
  · have he : k = (1176 : Fin 2886) := Fin.ext h1176
    subst k
    rw [keyMomentRowsAt1176]
    exact keyMoment1176 B hB
  · have he : k = (1177 : Fin 2886) := Fin.ext h1177
    subst k
    rw [keyMomentRowsAt1177]
    exact keyMoment1177 B hB
  · have he : k = (1178 : Fin 2886) := Fin.ext h1178
    subst k
    rw [keyMomentRowsAt1178]
    exact keyMoment1178 B hB
  · have he : k = (1179 : Fin 2886) := Fin.ext h1179
    subst k
    rw [keyMomentRowsAt1179]
    exact keyMoment1179 B hB
  · have he : k = (1180 : Fin 2886) := Fin.ext h1180
    subst k
    rw [keyMomentRowsAt1180]
    exact keyMoment1180 B hB
  · have he : k = (1181 : Fin 2886) := Fin.ext h1181
    subst k
    rw [keyMomentRowsAt1181]
    exact keyMoment1181 B hB
  · have he : k = (1182 : Fin 2886) := Fin.ext h1182
    subst k
    rw [keyMomentRowsAt1182]
    exact keyMoment1182 B hB
  · have he : k = (1183 : Fin 2886) := Fin.ext h1183
    subst k
    rw [keyMomentRowsAt1183]
    exact keyMoment1183 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound36_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound36_e_oai
