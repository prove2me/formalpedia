-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound33_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:52:08.404204+00:00
-- url     : https://prove2.me/submissions/32e597a9-3bd5-4e94-92c6-296eedb3319a

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

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical316
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40495 raw40495Labels = mixedMoment B node1321 node1321Labels := by
  calc
    mixedMoment B raw40495 raw40495Labels = mixedMoment B raw40495step0 raw40495step0Labels := by
      have hz : ∀ j, raw40495 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40495step0 = (fun i j => raw40495 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40495step0 raw40495; decide +kernel
      have hl : raw40495step0Labels = raw40495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40495 raw40495Labels permutation434 hz
    mixedMoment B raw40495step0 raw40495step0Labels = mixedMoment B raw40495step1 raw40495step1Labels := by
      have ha : raw40495step1 = (fun i j => raw40495step0 (permutation47 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40495step1 raw40495step0; decide +kernel
      have hl : raw40495step1Labels = raw40495step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40495step0 raw40495step0Labels permutation47 permutation6
    mixedMoment B raw40495step1 raw40495step1Labels = mixedMoment B raw40495step2 raw40495step2Labels := by
      have ha : raw40495step2 = -raw40495step1 := by apply Matrix.ext; change ∀ i j, raw40495step2 i j = -(raw40495step1 i j); unfold raw40495step2 raw40495step1; decide +kernel
      have hl : raw40495step2Labels = raw40495step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1321 node1321Labels := by rfl

theorem canonical40496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40496 raw40496Labels = mixedMoment B node1335 node1335Labels := by
  calc
    mixedMoment B raw40496 raw40496Labels = mixedMoment B raw40496step0 raw40496step0Labels := by
      have ha : raw40496step0 = (fun i j => raw40496 (permutation223 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40496step0 raw40496; decide +kernel
      have hl : raw40496step0Labels = raw40496Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40496 raw40496Labels permutation223 permutation6
    mixedMoment B raw40496step0 raw40496step0Labels = mixedMoment B raw40496step1 raw40496step1Labels := by
      have ha : raw40496step1 = -raw40496step0 := by apply Matrix.ext; change ∀ i j, raw40496step1 i j = -(raw40496step0 i j); unfold raw40496step1 raw40496step0; decide +kernel
      have hl : raw40496step1Labels = raw40496step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1335 node1335Labels := by rfl

theorem canonical40497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40497 raw40497Labels = mixedMoment B node1330 node1330Labels := by
  calc
    mixedMoment B raw40497 raw40497Labels = mixedMoment B raw40497step0 raw40497step0Labels := by
      have ha : raw40497step0 = (fun i j => raw40497 (permutation215 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40497step0 raw40497; decide +kernel
      have hl : raw40497step0Labels = raw40497Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40497 raw40497Labels permutation215 permutation6
    mixedMoment B raw40497step0 raw40497step0Labels = mixedMoment B raw40497step1 raw40497step1Labels := by
      have ha : raw40497step1 = -raw40497step0 := by apply Matrix.ext; change ∀ i j, raw40497step1 i j = -(raw40497step0 i j); unfold raw40497step1 raw40497step0; decide +kernel
      have hl : raw40497step1Labels = raw40497step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1330 node1330Labels := by rfl

theorem canonical40498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40498 raw40498Labels = mixedMoment B node1314 node1314Labels := by
  calc
    mixedMoment B raw40498 raw40498Labels = mixedMoment B raw40498step0 raw40498step0Labels := by
      have ha : raw40498step0 = (fun i j => raw40498 (permutation259 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40498step0 raw40498; decide +kernel
      have hl : raw40498step0Labels = raw40498Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40498 raw40498Labels permutation259 permutation6
    mixedMoment B raw40498step0 raw40498step0Labels = mixedMoment B raw40498step1 raw40498step1Labels := by
      have ha : raw40498step1 = -raw40498step0 := by apply Matrix.ext; change ∀ i j, raw40498step1 i j = -(raw40498step0 i j); unfold raw40498step1 raw40498step0; decide +kernel
      have hl : raw40498step1Labels = raw40498step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1314 node1314Labels := by rfl

theorem canonical40499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40499 raw40499Labels = mixedMoment B node1383 node1383Labels := by
  calc
    mixedMoment B raw40499 raw40499Labels = mixedMoment B raw40499step0 raw40499step0Labels := by
      have ha : raw40499step0 = (fun i j => raw40499 (permutation245 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40499step0 raw40499; decide +kernel
      have hl : raw40499step0Labels = raw40499Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40499 raw40499Labels permutation245 permutation6
    mixedMoment B raw40499step0 raw40499step0Labels = mixedMoment B raw40499step1 raw40499step1Labels := by
      have ha : raw40499step1 = -raw40499step0 := by apply Matrix.ext; change ∀ i j, raw40499step1 i j = -(raw40499step0 i j); unfold raw40499step1 raw40499step0; decide +kernel
      have hl : raw40499step1Labels = raw40499step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1383 node1383Labels := by rfl

theorem canonical40500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40500 raw40500Labels = mixedMoment B node1375 node1375Labels := by
  calc
    mixedMoment B raw40500 raw40500Labels = mixedMoment B raw40500step0 raw40500step0Labels := by
      have hz : ∀ j, raw40500 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40500step0 = (fun i j => raw40500 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40500step0 raw40500; decide +kernel
      have hl : raw40500step0Labels = raw40500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40500 raw40500Labels permutation434 hz
    mixedMoment B raw40500step0 raw40500step0Labels = mixedMoment B raw40500step1 raw40500step1Labels := by
      have hz : ∀ j, raw40500step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40500step1 = (fun i j => raw40500step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40500step1 raw40500step0; decide +kernel
      have hl : raw40500step1Labels = raw40500step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40500step0 raw40500step0Labels permutation80 hz
    mixedMoment B raw40500step1 raw40500step1Labels = mixedMoment B raw40500step2 raw40500step2Labels := by
      have ha : raw40500step2 = (fun i j => raw40500step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40500step2 raw40500step1; decide +kernel
      have hl : raw40500step2Labels = raw40500step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40500step1 raw40500step1Labels permutation13 permutation6
    mixedMoment B raw40500step2 raw40500step2Labels = mixedMoment B raw40500step3 raw40500step3Labels := by
      have ha : raw40500step3 = -raw40500step2 := by apply Matrix.ext; change ∀ i j, raw40500step3 i j = -(raw40500step2 i j); unfold raw40500step3 raw40500step2; decide +kernel
      have hl : raw40500step3Labels = raw40500step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1375 node1375Labels := by rfl

theorem canonical40501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40501 raw40501Labels = mixedMoment B node1325 node1325Labels := by
  calc
    mixedMoment B raw40501 raw40501Labels = mixedMoment B raw40501step0 raw40501step0Labels := by
      have hz : ∀ j, raw40501 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40501step0 = (fun i j => raw40501 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40501step0 raw40501; decide +kernel
      have hl : raw40501step0Labels = raw40501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40501 raw40501Labels permutation434 hz
    mixedMoment B raw40501step0 raw40501step0Labels = mixedMoment B raw40501step1 raw40501step1Labels := by
      have hz : ∀ j, raw40501step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40501step1 = (fun i j => raw40501step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40501step1 raw40501step0; decide +kernel
      have hl : raw40501step1Labels = raw40501step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40501step0 raw40501step0Labels permutation80 hz
    mixedMoment B raw40501step1 raw40501step1Labels = mixedMoment B raw40501step2 raw40501step2Labels := by
      have ha : raw40501step2 = (fun i j => raw40501step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40501step2 raw40501step1; decide +kernel
      have hl : raw40501step2Labels = raw40501step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40501step1 raw40501step1Labels permutation10 permutation6
    mixedMoment B raw40501step2 raw40501step2Labels = mixedMoment B raw40501step3 raw40501step3Labels := by
      have ha : raw40501step3 = -raw40501step2 := by apply Matrix.ext; change ∀ i j, raw40501step3 i j = -(raw40501step2 i j); unfold raw40501step3 raw40501step2; decide +kernel
      have hl : raw40501step3Labels = raw40501step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1325 node1325Labels := by rfl

theorem canonical40502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40502 raw40502Labels = mixedMoment B node1338 node1338Labels := by
  calc
    mixedMoment B raw40502 raw40502Labels = mixedMoment B raw40502step0 raw40502step0Labels := by
      have hz : ∀ j, raw40502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40502step0 = (fun i j => raw40502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40502step0 raw40502; decide +kernel
      have hl : raw40502step0Labels = raw40502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40502 raw40502Labels permutation346 hz
    mixedMoment B raw40502step0 raw40502step0Labels = mixedMoment B raw40502step1 raw40502step1Labels := by
      have ha : raw40502step1 = (fun i j => raw40502step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40502step1 raw40502step0; decide +kernel
      have hl : raw40502step1Labels = raw40502step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40502step0 raw40502step0Labels permutation43 permutation6
    mixedMoment B raw40502step1 raw40502step1Labels = mixedMoment B raw40502step2 raw40502step2Labels := by
      have ha : raw40502step2 = -raw40502step1 := by apply Matrix.ext; change ∀ i j, raw40502step2 i j = -(raw40502step1 i j); unfold raw40502step2 raw40502step1; decide +kernel
      have hl : raw40502step2Labels = raw40502step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1338 node1338Labels := by rfl

theorem canonical40503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40503 raw40503Labels = mixedMoment B node1334 node1334Labels := by
  calc
    mixedMoment B raw40503 raw40503Labels = mixedMoment B raw40503step0 raw40503step0Labels := by
      have hz : ∀ j, raw40503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40503step0 = (fun i j => raw40503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40503step0 raw40503; decide +kernel
      have hl : raw40503step0Labels = raw40503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40503 raw40503Labels permutation346 hz
    mixedMoment B raw40503step0 raw40503step0Labels = mixedMoment B raw40503step1 raw40503step1Labels := by
      have ha : raw40503step1 = (fun i j => raw40503step0 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40503step1 raw40503step0; decide +kernel
      have hl : raw40503step1Labels = raw40503step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40503step0 raw40503step0Labels permutation40 permutation6
    mixedMoment B raw40503step1 raw40503step1Labels = mixedMoment B raw40503step2 raw40503step2Labels := by
      have ha : raw40503step2 = -raw40503step1 := by apply Matrix.ext; change ∀ i j, raw40503step2 i j = -(raw40503step1 i j); unfold raw40503step2 raw40503step1; decide +kernel
      have hl : raw40503step2Labels = raw40503step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1334 node1334Labels := by rfl

theorem canonical40504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40504 raw40504Labels = mixedMoment B node1318 node1318Labels := by
  calc
    mixedMoment B raw40504 raw40504Labels = mixedMoment B raw40504step0 raw40504step0Labels := by
      have hz : ∀ j, raw40504 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40504step0 = (fun i j => raw40504 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40504step0 raw40504; decide +kernel
      have hl : raw40504step0Labels = raw40504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40504 raw40504Labels permutation346 hz
    mixedMoment B raw40504step0 raw40504step0Labels = mixedMoment B raw40504step1 raw40504step1Labels := by
      have ha : raw40504step1 = (fun i j => raw40504step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40504step1 raw40504step0; decide +kernel
      have hl : raw40504step1Labels = raw40504step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40504step0 raw40504step0Labels permutation55 permutation6
    mixedMoment B raw40504step1 raw40504step1Labels = mixedMoment B raw40504step2 raw40504step2Labels := by
      have ha : raw40504step2 = -raw40504step1 := by apply Matrix.ext; change ∀ i j, raw40504step2 i j = -(raw40504step1 i j); unfold raw40504step2 raw40504step1; decide +kernel
      have hl : raw40504step2Labels = raw40504step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1318 node1318Labels := by rfl

theorem canonical40505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40505 raw40505Labels = mixedMoment B node1391 node1391Labels := by
  calc
    mixedMoment B raw40505 raw40505Labels = mixedMoment B raw40505step0 raw40505step0Labels := by
      have hz : ∀ j, raw40505 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40505step0 = (fun i j => raw40505 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40505step0 raw40505; decide +kernel
      have hl : raw40505step0Labels = raw40505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40505 raw40505Labels permutation346 hz
    mixedMoment B raw40505step0 raw40505step0Labels = mixedMoment B raw40505step1 raw40505step1Labels := by
      have ha : raw40505step1 = (fun i j => raw40505step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40505step1 raw40505step0; decide +kernel
      have hl : raw40505step1Labels = raw40505step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40505step0 raw40505step0Labels permutation49 permutation6
    mixedMoment B raw40505step1 raw40505step1Labels = mixedMoment B raw40505step2 raw40505step2Labels := by
      have ha : raw40505step2 = -raw40505step1 := by apply Matrix.ext; change ∀ i j, raw40505step2 i j = -(raw40505step1 i j); unfold raw40505step2 raw40505step1; decide +kernel
      have hl : raw40505step2Labels = raw40505step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1391 node1391Labels := by rfl

theorem canonical40506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40506 raw40506Labels = mixedMoment B node1328 node1328Labels := by
  calc
    mixedMoment B raw40506 raw40506Labels = mixedMoment B raw40506step0 raw40506step0Labels := by
      have ha : raw40506step0 = (fun i j => raw40506 (permutation199 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40506step0 raw40506; decide +kernel
      have hl : raw40506step0Labels = raw40506Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40506 raw40506Labels permutation199 permutation6
    mixedMoment B raw40506step0 raw40506step0Labels = mixedMoment B raw40506step1 raw40506step1Labels := by
      have ha : raw40506step1 = -raw40506step0 := by apply Matrix.ext; change ∀ i j, raw40506step1 i j = -(raw40506step0 i j); unfold raw40506step1 raw40506step0; decide +kernel
      have hl : raw40506step1Labels = raw40506step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1328 node1328Labels := by rfl

theorem canonical40507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40507 raw40507Labels = mixedMoment B node1435 node1435Labels := by
  calc
    mixedMoment B raw40507 raw40507Labels = mixedMoment B raw40507step0 raw40507step0Labels := by
      have hz : ∀ j, raw40507 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40507step0 = (fun i j => raw40507 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40507step0 raw40507; decide +kernel
      have hl : raw40507step0Labels = raw40507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40507 raw40507Labels permutation520 hz
    mixedMoment B raw40507step0 raw40507step0Labels = mixedMoment B raw40507step1 raw40507step1Labels := by
      have ha : raw40507step1 = (fun i j => raw40507step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40507step1 raw40507step0; decide +kernel
      have hl : raw40507step1Labels = raw40507step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40507step0 raw40507step0Labels permutation50 permutation6
    mixedMoment B raw40507step1 raw40507step1Labels = mixedMoment B raw40507step2 raw40507step2Labels := by
      have ha : raw40507step2 = -raw40507step1 := by apply Matrix.ext; change ∀ i j, raw40507step2 i j = -(raw40507step1 i j); unfold raw40507step2 raw40507step1; decide +kernel
      have hl : raw40507step2Labels = raw40507step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1435 node1435Labels := by rfl

theorem canonical40508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40508 raw40508Labels = mixedMoment B node1366 node1366Labels := by
  calc
    mixedMoment B raw40508 raw40508Labels = mixedMoment B raw40508step0 raw40508step0Labels := by
      have ha : raw40508step0 = (fun i j => raw40508 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40508step0 raw40508; decide +kernel
      have hl : raw40508step0Labels = raw40508Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40508 raw40508Labels permutation260 permutation6
    mixedMoment B raw40508step0 raw40508step0Labels = mixedMoment B raw40508step1 raw40508step1Labels := by
      have ha : raw40508step1 = -raw40508step0 := by apply Matrix.ext; change ∀ i j, raw40508step1 i j = -(raw40508step0 i j); unfold raw40508step1 raw40508step0; decide +kernel
      have hl : raw40508step1Labels = raw40508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1366 node1366Labels := by rfl

theorem canonical40509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40509 raw40509Labels = mixedMoment B node1319 node1319Labels := by
  calc
    mixedMoment B raw40509 raw40509Labels = mixedMoment B raw40509step0 raw40509step0Labels := by
      have ha : raw40509step0 = (fun i j => raw40509 (permutation224 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40509step0 raw40509; decide +kernel
      have hl : raw40509step0Labels = raw40509Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40509 raw40509Labels permutation224 permutation6
    mixedMoment B raw40509step0 raw40509step0Labels = mixedMoment B raw40509step1 raw40509step1Labels := by
      have ha : raw40509step1 = -raw40509step0 := by apply Matrix.ext; change ∀ i j, raw40509step1 i j = -(raw40509step0 i j); unfold raw40509step1 raw40509step0; decide +kernel
      have hl : raw40509step1Labels = raw40509step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1319 node1319Labels := by rfl

theorem canonical40510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40510 raw40510Labels = mixedMoment B node1370 node1370Labels := by
  calc
    mixedMoment B raw40510 raw40510Labels = mixedMoment B raw40510step0 raw40510step0Labels := by
      have hz : ∀ j, raw40510 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40510step0 = (fun i j => raw40510 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40510step0 raw40510; decide +kernel
      have hl : raw40510step0Labels = raw40510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40510 raw40510Labels permutation434 hz
    mixedMoment B raw40510step0 raw40510step0Labels = mixedMoment B raw40510step1 raw40510step1Labels := by
      have ha : raw40510step1 = (fun i j => raw40510step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40510step1 raw40510step0; decide +kernel
      have hl : raw40510step1Labels = raw40510step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40510step0 raw40510step0Labels permutation50 permutation6
    mixedMoment B raw40510step1 raw40510step1Labels = mixedMoment B raw40510step2 raw40510step2Labels := by
      have ha : raw40510step2 = -raw40510step1 := by apply Matrix.ext; change ∀ i j, raw40510step2 i j = -(raw40510step1 i j); unfold raw40510step2 raw40510step1; decide +kernel
      have hl : raw40510step2Labels = raw40510step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1370 node1370Labels := by rfl

theorem canonical40511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40511 raw40511Labels = mixedMoment B node1320 node1320Labels := by
  calc
    mixedMoment B raw40511 raw40511Labels = mixedMoment B raw40511step0 raw40511step0Labels := by
      have hz : ∀ j, raw40511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40511step0 = (fun i j => raw40511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40511step0 raw40511; decide +kernel
      have hl : raw40511step0Labels = raw40511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40511 raw40511Labels permutation434 hz
    mixedMoment B raw40511step0 raw40511step0Labels = mixedMoment B raw40511step1 raw40511step1Labels := by
      have ha : raw40511step1 = (fun i j => raw40511step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40511step1 raw40511step0; decide +kernel
      have hl : raw40511step1Labels = raw40511step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40511step0 raw40511step0Labels permutation44 permutation6
    mixedMoment B raw40511step1 raw40511step1Labels = mixedMoment B raw40511step2 raw40511step2Labels := by
      have ha : raw40511step2 = -raw40511step1 := by apply Matrix.ext; change ∀ i j, raw40511step2 i j = -(raw40511step1 i j); unfold raw40511step2 raw40511step1; decide +kernel
      have hl : raw40511step2Labels = raw40511step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1320 node1320Labels := by rfl

theorem canonical40512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40512 raw40512Labels = mixedMoment B node1316 node1316Labels := by
  calc
    mixedMoment B raw40512 raw40512Labels = mixedMoment B raw40512step0 raw40512step0Labels := by
      have ha : raw40512step0 = (fun i j => raw40512 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40512step0 raw40512; decide +kernel
      have hl : raw40512step0Labels = raw40512Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40512 raw40512Labels permutation260 permutation6
    mixedMoment B raw40512step0 raw40512step0Labels = mixedMoment B raw40512step1 raw40512step1Labels := by
      have ha : raw40512step1 = -raw40512step0 := by apply Matrix.ext; change ∀ i j, raw40512step1 i j = -(raw40512step0 i j); unfold raw40512step1 raw40512step0; decide +kernel
      have hl : raw40512step1Labels = raw40512step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1316 node1316Labels := by rfl

theorem canonical40513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40513 raw40513Labels = mixedMoment B node1372 node1372Labels := by
  calc
    mixedMoment B raw40513 raw40513Labels = mixedMoment B raw40513step0 raw40513step0Labels := by
      have hz : ∀ j, raw40513 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40513step0 = (fun i j => raw40513 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40513step0 raw40513; decide +kernel
      have hl : raw40513step0Labels = raw40513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40513 raw40513Labels permutation434 hz
    mixedMoment B raw40513step0 raw40513step0Labels = mixedMoment B raw40513step1 raw40513step1Labels := by
      have hz : ∀ j, raw40513step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40513step1 = (fun i j => raw40513step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40513step1 raw40513step0; decide +kernel
      have hl : raw40513step1Labels = raw40513step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40513step0 raw40513step0Labels permutation80 hz
    mixedMoment B raw40513step1 raw40513step1Labels = mixedMoment B raw40513step2 raw40513step2Labels := by
      have ha : raw40513step2 = (fun i j => raw40513step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40513step2 raw40513step1; decide +kernel
      have hl : raw40513step2Labels = raw40513step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40513step1 raw40513step1Labels permutation12 permutation6
    mixedMoment B raw40513step2 raw40513step2Labels = mixedMoment B raw40513step3 raw40513step3Labels := by
      have ha : raw40513step3 = -raw40513step2 := by apply Matrix.ext; change ∀ i j, raw40513step3 i j = -(raw40513step2 i j); unfold raw40513step3 raw40513step2; decide +kernel
      have hl : raw40513step3Labels = raw40513step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1372 node1372Labels := by rfl

theorem canonical40514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40514 raw40514Labels = mixedMoment B node1142 node1142Labels := by
  calc
    mixedMoment B raw40514 raw40514Labels = mixedMoment B raw40514step0 raw40514step0Labels := by
      have hz : ∀ j, raw40514 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40514step0 = (fun i j => raw40514 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40514step0 raw40514; decide +kernel
      have hl : raw40514step0Labels = raw40514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40514 raw40514Labels permutation434 hz
    mixedMoment B raw40514step0 raw40514step0Labels = mixedMoment B raw40514step1 raw40514step1Labels := by
      have hz : ∀ j, raw40514step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40514step1 = (fun i j => raw40514step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40514step1 raw40514step0; decide +kernel
      have hl : raw40514step1Labels = raw40514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40514step0 raw40514step0Labels permutation80 hz
    mixedMoment B raw40514step1 raw40514step1Labels = mixedMoment B raw40514step2 raw40514step2Labels := by
      have ha : raw40514step2 = (fun i j => raw40514step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40514step2 raw40514step1; decide +kernel
      have hl : raw40514step2Labels = raw40514step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40514step1 raw40514step1Labels permutation29 permutation6
    _ = mixedMoment B node1142 node1142Labels := by rfl

theorem canonical40515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40515 raw40515Labels = mixedMoment B node1337 node1337Labels := by
  calc
    mixedMoment B raw40515 raw40515Labels = mixedMoment B raw40515step0 raw40515step0Labels := by
      have hz : ∀ j, raw40515 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40515step0 = (fun i j => raw40515 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40515step0 raw40515; decide +kernel
      have hl : raw40515step0Labels = raw40515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40515 raw40515Labels permutation346 hz
    mixedMoment B raw40515step0 raw40515step0Labels = mixedMoment B raw40515step1 raw40515step1Labels := by
      have ha : raw40515step1 = (fun i j => raw40515step0 (permutation42 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40515step1 raw40515step0; decide +kernel
      have hl : raw40515step1Labels = raw40515step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40515step0 raw40515step0Labels permutation42 permutation6
    mixedMoment B raw40515step1 raw40515step1Labels = mixedMoment B raw40515step2 raw40515step2Labels := by
      have ha : raw40515step2 = -raw40515step1 := by apply Matrix.ext; change ∀ i j, raw40515step2 i j = -(raw40515step1 i j); unfold raw40515step2 raw40515step1; decide +kernel
      have hl : raw40515step2Labels = raw40515step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1337 node1337Labels := by rfl

theorem canonical40516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40516 raw40516Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw40516 raw40516Labels = mixedMoment B raw40516step0 raw40516step0Labels := by
      have hz : ∀ j, raw40516 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40516step0 = (fun i j => raw40516 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40516step0 raw40516; decide +kernel
      have hl : raw40516step0Labels = raw40516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40516 raw40516Labels permutation346 hz
    mixedMoment B raw40516step0 raw40516step0Labels = mixedMoment B raw40516step1 raw40516step1Labels := by
      have ha : raw40516step1 = (fun i j => raw40516step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40516step1 raw40516step0; decide +kernel
      have hl : raw40516step1Labels = raw40516step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40516step0 raw40516step0Labels permutation139 permutation6
    _ = mixedMoment B node1118 node1118Labels := by rfl

theorem canonical40517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40517 raw40517Labels = mixedMoment B node1317 node1317Labels := by
  calc
    mixedMoment B raw40517 raw40517Labels = mixedMoment B raw40517step0 raw40517step0Labels := by
      have hz : ∀ j, raw40517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40517step0 = (fun i j => raw40517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40517step0 raw40517; decide +kernel
      have hl : raw40517step0Labels = raw40517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40517 raw40517Labels permutation346 hz
    mixedMoment B raw40517step0 raw40517step0Labels = mixedMoment B raw40517step1 raw40517step1Labels := by
      have ha : raw40517step1 = (fun i j => raw40517step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40517step1 raw40517step0; decide +kernel
      have hl : raw40517step1Labels = raw40517step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40517step0 raw40517step0Labels permutation54 permutation6
    mixedMoment B raw40517step1 raw40517step1Labels = mixedMoment B raw40517step2 raw40517step2Labels := by
      have ha : raw40517step2 = -raw40517step1 := by apply Matrix.ext; change ∀ i j, raw40517step2 i j = -(raw40517step1 i j); unfold raw40517step2 raw40517step1; decide +kernel
      have hl : raw40517step2Labels = raw40517step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1317 node1317Labels := by rfl

theorem canonical40518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40518 raw40518Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw40518 raw40518Labels = mixedMoment B raw40518step0 raw40518step0Labels := by
      have hz : ∀ j, raw40518 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40518step0 = (fun i j => raw40518 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40518step0 raw40518; decide +kernel
      have hl : raw40518step0Labels = raw40518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40518 raw40518Labels permutation346 hz
    mixedMoment B raw40518step0 raw40518step0Labels = mixedMoment B raw40518step1 raw40518step1Labels := by
      have ha : raw40518step1 = (fun i j => raw40518step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40518step1 raw40518step0; decide +kernel
      have hl : raw40518step1Labels = raw40518step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40518step0 raw40518step0Labels permutation48 permutation6
    mixedMoment B raw40518step1 raw40518step1Labels = mixedMoment B raw40518step2 raw40518step2Labels := by
      have ha : raw40518step2 = -raw40518step1 := by apply Matrix.ext; change ∀ i j, raw40518step2 i j = -(raw40518step1 i j); unfold raw40518step2 raw40518step1; decide +kernel
      have hl : raw40518step2Labels = raw40518step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1388 node1388Labels := by rfl

theorem canonical40519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40519 raw40519Labels = mixedMoment B node1322 node1322Labels := by
  calc
    mixedMoment B raw40519 raw40519Labels = mixedMoment B raw40519step0 raw40519step0Labels := by
      have hz : ∀ j, raw40519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40519step0 = (fun i j => raw40519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40519step0 raw40519; decide +kernel
      have hl : raw40519step0Labels = raw40519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40519 raw40519Labels permutation346 hz
    mixedMoment B raw40519step0 raw40519step0Labels = mixedMoment B raw40519step1 raw40519step1Labels := by
      have ha : raw40519step1 = (fun i j => raw40519step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40519step1 raw40519step0; decide +kernel
      have hl : raw40519step1Labels = raw40519step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40519step0 raw40519step0Labels permutation50 permutation6
    mixedMoment B raw40519step1 raw40519step1Labels = mixedMoment B raw40519step2 raw40519step2Labels := by
      have ha : raw40519step2 = -raw40519step1 := by apply Matrix.ext; change ∀ i j, raw40519step2 i j = -(raw40519step1 i j); unfold raw40519step2 raw40519step1; decide +kernel
      have hl : raw40519step2Labels = raw40519step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1322 node1322Labels := by rfl

theorem canonical40520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40520 raw40520Labels = mixedMoment B node1327 node1327Labels := by
  calc
    mixedMoment B raw40520 raw40520Labels = mixedMoment B raw40520step0 raw40520step0Labels := by
      have ha : raw40520step0 = (fun i j => raw40520 (permutation198 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40520step0 raw40520; decide +kernel
      have hl : raw40520step0Labels = raw40520Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40520 raw40520Labels permutation198 permutation6
    mixedMoment B raw40520step0 raw40520step0Labels = mixedMoment B raw40520step1 raw40520step1Labels := by
      have ha : raw40520step1 = -raw40520step0 := by apply Matrix.ext; change ∀ i j, raw40520step1 i j = -(raw40520step0 i j); unfold raw40520step1 raw40520step0; decide +kernel
      have hl : raw40520step1Labels = raw40520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1327 node1327Labels := by rfl

theorem canonical40521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40521 raw40521Labels = mixedMoment B node1064 node1064Labels := by
  calc
    mixedMoment B raw40521 raw40521Labels = mixedMoment B raw40521step0 raw40521step0Labels := by
      have hz : ∀ j, raw40521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40521step0 = (fun i j => raw40521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40521step0 raw40521; decide +kernel
      have hl : raw40521step0Labels = raw40521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40521 raw40521Labels permutation434 hz
    mixedMoment B raw40521step0 raw40521step0Labels = mixedMoment B raw40521step1 raw40521step1Labels := by
      have hz : ∀ j, raw40521step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40521step1 = (fun i j => raw40521step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40521step1 raw40521step0; decide +kernel
      have hl : raw40521step1Labels = raw40521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40521step0 raw40521step0Labels permutation80 hz
    mixedMoment B raw40521step1 raw40521step1Labels = mixedMoment B raw40521step2 raw40521step2Labels := by
      have hz : ∀ j, raw40521step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40521step2 = (fun i j => raw40521step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40521step2 raw40521step1; decide +kernel
      have hl : raw40521step2Labels = raw40521step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40521step1 raw40521step1Labels permutation14 hz
    mixedMoment B raw40521step2 raw40521step2Labels = mixedMoment B raw40521step3 raw40521step3Labels := by
      have ha : raw40521step3 = (fun i j => raw40521step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40521step3 raw40521step2; decide +kernel
      have hl : raw40521step3Labels = raw40521step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40521step2 raw40521step2Labels permutation5 permutation6
    _ = mixedMoment B node1064 node1064Labels := by rfl

theorem canonical40522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40522 raw40522Labels = mixedMoment B node617 node617Labels := by
  calc
    mixedMoment B raw40522 raw40522Labels = mixedMoment B raw40522step0 raw40522step0Labels := by
      have hz : ∀ j, raw40522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40522step0 = (fun i j => raw40522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40522step0 raw40522; decide +kernel
      have hl : raw40522step0Labels = raw40522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40522 raw40522Labels permutation434 hz
    mixedMoment B raw40522step0 raw40522step0Labels = mixedMoment B raw40522step1 raw40522step1Labels := by
      have hz : ∀ j, raw40522step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40522step1 = (fun i j => raw40522step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40522step1 raw40522step0; decide +kernel
      have hl : raw40522step1Labels = raw40522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40522step0 raw40522step0Labels permutation80 hz
    mixedMoment B raw40522step1 raw40522step1Labels = mixedMoment B raw40522step2 raw40522step2Labels := by
      have hz : ∀ j, raw40522step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40522step2 = (fun i j => raw40522step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40522step2 raw40522step1; decide +kernel
      have hl : raw40522step2Labels = raw40522step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40522step1 raw40522step1Labels permutation14 hz
    mixedMoment B raw40522step2 raw40522step2Labels = mixedMoment B raw40522step3 raw40522step3Labels := by
      have ha : raw40522step3 = (fun i j => raw40522step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40522step3 raw40522step2; decide +kernel
      have hl : raw40522step3Labels = raw40522step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40522step2 raw40522step2Labels permutation7 permutation6
    _ = mixedMoment B node617 node617Labels := by rfl

theorem canonical40523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40523 raw40523Labels = mixedMoment B node951 node951Labels := by
  calc
    mixedMoment B raw40523 raw40523Labels = mixedMoment B raw40523step0 raw40523step0Labels := by
      have hz : ∀ j, raw40523 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40523step0 = (fun i j => raw40523 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40523step0 raw40523; decide +kernel
      have hl : raw40523step0Labels = raw40523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40523 raw40523Labels permutation346 hz
    mixedMoment B raw40523step0 raw40523step0Labels = mixedMoment B raw40523step1 raw40523step1Labels := by
      have hz : ∀ j, raw40523step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40523step1 = (fun i j => raw40523step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40523step1 raw40523step0; decide +kernel
      have hl : raw40523step1Labels = raw40523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40523step0 raw40523step0Labels permutation56 hz
    mixedMoment B raw40523step1 raw40523step1Labels = mixedMoment B raw40523step2 raw40523step2Labels := by
      have ha : raw40523step2 = (fun i j => raw40523step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40523step2 raw40523step1; decide +kernel
      have hl : raw40523step2Labels = raw40523step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40523step1 raw40523step1Labels permutation25 permutation6
    _ = mixedMoment B node951 node951Labels := by rfl

theorem canonical40524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40524 raw40524Labels = mixedMoment B node587 node587Labels := by
  calc
    mixedMoment B raw40524 raw40524Labels = mixedMoment B raw40524step0 raw40524step0Labels := by
      have hz : ∀ j, raw40524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40524step0 = (fun i j => raw40524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40524step0 raw40524; decide +kernel
      have hl : raw40524step0Labels = raw40524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40524 raw40524Labels permutation346 hz
    mixedMoment B raw40524step0 raw40524step0Labels = mixedMoment B raw40524step1 raw40524step1Labels := by
      have hz : ∀ j, raw40524step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40524step1 = (fun i j => raw40524step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40524step1 raw40524step0; decide +kernel
      have hl : raw40524step1Labels = raw40524step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40524step0 raw40524step0Labels permutation56 hz
    mixedMoment B raw40524step1 raw40524step1Labels = mixedMoment B raw40524step2 raw40524step2Labels := by
      have ha : raw40524step2 = (fun i j => raw40524step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40524step2 raw40524step1; decide +kernel
      have hl : raw40524step2Labels = raw40524step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40524step1 raw40524step1Labels permutation31 permutation6
    _ = mixedMoment B node587 node587Labels := by rfl

theorem canonical40525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40525 raw40525Labels = mixedMoment B node936 node936Labels := by
  calc
    mixedMoment B raw40525 raw40525Labels = mixedMoment B raw40525step0 raw40525step0Labels := by
      have hz : ∀ j, raw40525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40525step0 = (fun i j => raw40525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40525step0 raw40525; decide +kernel
      have hl : raw40525step0Labels = raw40525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40525 raw40525Labels permutation346 hz
    mixedMoment B raw40525step0 raw40525step0Labels = mixedMoment B raw40525step1 raw40525step1Labels := by
      have hz : ∀ j, raw40525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40525step1 = (fun i j => raw40525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40525step1 raw40525step0; decide +kernel
      have hl : raw40525step1Labels = raw40525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40525step0 raw40525step0Labels permutation56 hz
    mixedMoment B raw40525step1 raw40525step1Labels = mixedMoment B raw40525step2 raw40525step2Labels := by
      have ha : raw40525step2 = (fun i j => raw40525step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40525step2 raw40525step1; decide +kernel
      have hl : raw40525step2Labels = raw40525step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40525step1 raw40525step1Labels permutation17 permutation6
    _ = mixedMoment B node936 node936Labels := by rfl

theorem canonical40526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40526 raw40526Labels = mixedMoment B node1027 node1027Labels := by
  calc
    mixedMoment B raw40526 raw40526Labels = mixedMoment B raw40526step0 raw40526step0Labels := by
      have hz : ∀ j, raw40526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40526step0 = (fun i j => raw40526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40526step0 raw40526; decide +kernel
      have hl : raw40526step0Labels = raw40526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40526 raw40526Labels permutation346 hz
    mixedMoment B raw40526step0 raw40526step0Labels = mixedMoment B raw40526step1 raw40526step1Labels := by
      have hz : ∀ j, raw40526step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40526step1 = (fun i j => raw40526step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40526step1 raw40526step0; decide +kernel
      have hl : raw40526step1Labels = raw40526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40526step0 raw40526step0Labels permutation56 hz
    mixedMoment B raw40526step1 raw40526step1Labels = mixedMoment B raw40526step2 raw40526step2Labels := by
      have ha : raw40526step2 = (fun i j => raw40526step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40526step2 raw40526step1; decide +kernel
      have hl : raw40526step2Labels = raw40526step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40526step1 raw40526step1Labels permutation17 permutation6
    _ = mixedMoment B node1027 node1027Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1056 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1056) =
      Integer.Sparse.eval keyMomentRow1056 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1056).leftCharge (GramAssembly.key 1056).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1321) := by
    have ha : gramCharges (GramAssembly.key 1056).leftCharge (GramAssembly.key 1056).rightCharge = raw40495 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40495Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40495 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1056).leftCharge (GramAssembly.key 1056).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1056, Integer.Sparse.eval]

theorem keyMoment1057 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1057) =
      Integer.Sparse.eval keyMomentRow1057 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1057).leftCharge (GramAssembly.key 1057).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1335) := by
    have ha : gramCharges (GramAssembly.key 1057).leftCharge (GramAssembly.key 1057).rightCharge = raw40496 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40496Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40496 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1057).leftCharge (GramAssembly.key 1057).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1057, Integer.Sparse.eval]

theorem keyMoment1058 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1058) =
      Integer.Sparse.eval keyMomentRow1058 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1058).leftCharge (GramAssembly.key 1058).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1330) := by
    have ha : gramCharges (GramAssembly.key 1058).leftCharge (GramAssembly.key 1058).rightCharge = raw40497 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40497Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40497 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1058).leftCharge (GramAssembly.key 1058).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1058, Integer.Sparse.eval]

theorem keyMoment1059 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1059) =
      Integer.Sparse.eval keyMomentRow1059 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1059).leftCharge (GramAssembly.key 1059).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1314) := by
    have ha : gramCharges (GramAssembly.key 1059).leftCharge (GramAssembly.key 1059).rightCharge = raw40498 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40498Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40498 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1059).leftCharge (GramAssembly.key 1059).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1059, Integer.Sparse.eval]

theorem keyMoment1060 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1060) =
      Integer.Sparse.eval keyMomentRow1060 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1060).leftCharge (GramAssembly.key 1060).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1383) := by
    have ha : gramCharges (GramAssembly.key 1060).leftCharge (GramAssembly.key 1060).rightCharge = raw40499 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40499Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40499 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1060).leftCharge (GramAssembly.key 1060).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1060, Integer.Sparse.eval]

theorem keyMoment1061 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1061) =
      Integer.Sparse.eval keyMomentRow1061 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1061).leftCharge (GramAssembly.key 1061).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1375) := by
    have ha : gramCharges (GramAssembly.key 1061).leftCharge (GramAssembly.key 1061).rightCharge = raw40500 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40500Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40500 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1061).leftCharge (GramAssembly.key 1061).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1061, Integer.Sparse.eval]

theorem keyMoment1062 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1062) =
      Integer.Sparse.eval keyMomentRow1062 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1062).leftCharge (GramAssembly.key 1062).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1325) := by
    have ha : gramCharges (GramAssembly.key 1062).leftCharge (GramAssembly.key 1062).rightCharge = raw40501 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40501Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40501 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1062).leftCharge (GramAssembly.key 1062).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1062, Integer.Sparse.eval]

theorem keyMoment1063 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1063) =
      Integer.Sparse.eval keyMomentRow1063 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1063).leftCharge (GramAssembly.key 1063).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1338) := by
    have ha : gramCharges (GramAssembly.key 1063).leftCharge (GramAssembly.key 1063).rightCharge = raw40502 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40502Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40502 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1063).leftCharge (GramAssembly.key 1063).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1063, Integer.Sparse.eval]

theorem keyMoment1064 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1064) =
      Integer.Sparse.eval keyMomentRow1064 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1064).leftCharge (GramAssembly.key 1064).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1334) := by
    have ha : gramCharges (GramAssembly.key 1064).leftCharge (GramAssembly.key 1064).rightCharge = raw40503 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40503Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40503 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1064).leftCharge (GramAssembly.key 1064).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1064, Integer.Sparse.eval]

theorem keyMoment1065 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1065) =
      Integer.Sparse.eval keyMomentRow1065 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1065).leftCharge (GramAssembly.key 1065).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1318) := by
    have ha : gramCharges (GramAssembly.key 1065).leftCharge (GramAssembly.key 1065).rightCharge = raw40504 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40504Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40504 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1065).leftCharge (GramAssembly.key 1065).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1065, Integer.Sparse.eval]

theorem keyMoment1066 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1066) =
      Integer.Sparse.eval keyMomentRow1066 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1066).leftCharge (GramAssembly.key 1066).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1391) := by
    have ha : gramCharges (GramAssembly.key 1066).leftCharge (GramAssembly.key 1066).rightCharge = raw40505 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40505Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40505 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1066).leftCharge (GramAssembly.key 1066).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1066, Integer.Sparse.eval]

theorem keyMoment1067 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1067) =
      Integer.Sparse.eval keyMomentRow1067 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1067).leftCharge (GramAssembly.key 1067).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1328) := by
    have ha : gramCharges (GramAssembly.key 1067).leftCharge (GramAssembly.key 1067).rightCharge = raw40506 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40506Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40506 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1067).leftCharge (GramAssembly.key 1067).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1067, Integer.Sparse.eval]

theorem keyMoment1068 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1068) =
      Integer.Sparse.eval keyMomentRow1068 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1068).leftCharge (GramAssembly.key 1068).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1435) := by
    have ha : gramCharges (GramAssembly.key 1068).leftCharge (GramAssembly.key 1068).rightCharge = raw40507 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40507Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40507 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1068).leftCharge (GramAssembly.key 1068).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1068, Integer.Sparse.eval]

theorem keyMoment1069 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1069) =
      Integer.Sparse.eval keyMomentRow1069 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1069).leftCharge (GramAssembly.key 1069).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1366) := by
    have ha : gramCharges (GramAssembly.key 1069).leftCharge (GramAssembly.key 1069).rightCharge = raw40508 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40508Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40508 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1069).leftCharge (GramAssembly.key 1069).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1069, Integer.Sparse.eval]

theorem keyMoment1070 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1070) =
      Integer.Sparse.eval keyMomentRow1070 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1070).leftCharge (GramAssembly.key 1070).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1319) := by
    have ha : gramCharges (GramAssembly.key 1070).leftCharge (GramAssembly.key 1070).rightCharge = raw40509 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40509Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40509 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1070).leftCharge (GramAssembly.key 1070).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1070, Integer.Sparse.eval]

theorem keyMoment1071 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1071) =
      Integer.Sparse.eval keyMomentRow1071 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1071).leftCharge (GramAssembly.key 1071).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1370) := by
    have ha : gramCharges (GramAssembly.key 1071).leftCharge (GramAssembly.key 1071).rightCharge = raw40510 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40510Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40510 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1071).leftCharge (GramAssembly.key 1071).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1071, Integer.Sparse.eval]

theorem keyMoment1072 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1072) =
      Integer.Sparse.eval keyMomentRow1072 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1072).leftCharge (GramAssembly.key 1072).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1320) := by
    have ha : gramCharges (GramAssembly.key 1072).leftCharge (GramAssembly.key 1072).rightCharge = raw40511 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40511Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40511 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1072).leftCharge (GramAssembly.key 1072).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1072, Integer.Sparse.eval]

theorem keyMoment1073 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1073) =
      Integer.Sparse.eval keyMomentRow1073 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1073).leftCharge (GramAssembly.key 1073).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1316) := by
    have ha : gramCharges (GramAssembly.key 1073).leftCharge (GramAssembly.key 1073).rightCharge = raw40512 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40512Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40512 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1073).leftCharge (GramAssembly.key 1073).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1073, Integer.Sparse.eval]

theorem keyMoment1074 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1074) =
      Integer.Sparse.eval keyMomentRow1074 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1074).leftCharge (GramAssembly.key 1074).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1372) := by
    have ha : gramCharges (GramAssembly.key 1074).leftCharge (GramAssembly.key 1074).rightCharge = raw40513 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40513Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40513 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1074).leftCharge (GramAssembly.key 1074).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1074, Integer.Sparse.eval]

theorem keyMoment1075 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1075) =
      Integer.Sparse.eval keyMomentRow1075 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1075).leftCharge (GramAssembly.key 1075).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1142) := by
    have ha : gramCharges (GramAssembly.key 1075).leftCharge (GramAssembly.key 1075).rightCharge = raw40514 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40514Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40514 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1075).leftCharge (GramAssembly.key 1075).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1075, Integer.Sparse.eval]

theorem keyMoment1076 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1076) =
      Integer.Sparse.eval keyMomentRow1076 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1076).leftCharge (GramAssembly.key 1076).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1337) := by
    have ha : gramCharges (GramAssembly.key 1076).leftCharge (GramAssembly.key 1076).rightCharge = raw40515 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40515Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40515 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1076).leftCharge (GramAssembly.key 1076).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1076, Integer.Sparse.eval]

theorem keyMoment1077 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1077) =
      Integer.Sparse.eval keyMomentRow1077 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1077).leftCharge (GramAssembly.key 1077).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1118) := by
    have ha : gramCharges (GramAssembly.key 1077).leftCharge (GramAssembly.key 1077).rightCharge = raw40516 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40516Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40516 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1077).leftCharge (GramAssembly.key 1077).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1077, Integer.Sparse.eval]

theorem keyMoment1078 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1078) =
      Integer.Sparse.eval keyMomentRow1078 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1078).leftCharge (GramAssembly.key 1078).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1317) := by
    have ha : gramCharges (GramAssembly.key 1078).leftCharge (GramAssembly.key 1078).rightCharge = raw40517 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40517Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40517 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1078).leftCharge (GramAssembly.key 1078).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1078, Integer.Sparse.eval]

theorem keyMoment1079 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1079) =
      Integer.Sparse.eval keyMomentRow1079 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1079).leftCharge (GramAssembly.key 1079).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1388) := by
    have ha : gramCharges (GramAssembly.key 1079).leftCharge (GramAssembly.key 1079).rightCharge = raw40518 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40518Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40518 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1079).leftCharge (GramAssembly.key 1079).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1079, Integer.Sparse.eval]

theorem keyMoment1080 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1080) =
      Integer.Sparse.eval keyMomentRow1080 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1080).leftCharge (GramAssembly.key 1080).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1322) := by
    have ha : gramCharges (GramAssembly.key 1080).leftCharge (GramAssembly.key 1080).rightCharge = raw40519 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40519Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40519 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1080).leftCharge (GramAssembly.key 1080).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1080, Integer.Sparse.eval]

theorem keyMoment1081 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1081) =
      Integer.Sparse.eval keyMomentRow1081 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1081).leftCharge (GramAssembly.key 1081).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1327) := by
    have ha : gramCharges (GramAssembly.key 1081).leftCharge (GramAssembly.key 1081).rightCharge = raw40520 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40520Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40520 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1081).leftCharge (GramAssembly.key 1081).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1081, Integer.Sparse.eval]

theorem keyMoment1082 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1082) =
      Integer.Sparse.eval keyMomentRow1082 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1082).leftCharge (GramAssembly.key 1082).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1064) := by
    have ha : gramCharges (GramAssembly.key 1082).leftCharge (GramAssembly.key 1082).rightCharge = raw40521 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40521Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40521 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1082).leftCharge (GramAssembly.key 1082).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1082, Integer.Sparse.eval]

theorem keyMoment1083 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1083) =
      Integer.Sparse.eval keyMomentRow1083 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1083).leftCharge (GramAssembly.key 1083).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 617) := by
    have ha : gramCharges (GramAssembly.key 1083).leftCharge (GramAssembly.key 1083).rightCharge = raw40522 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40522Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40522 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1083).leftCharge (GramAssembly.key 1083).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1083, Integer.Sparse.eval]

theorem keyMoment1084 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1084) =
      Integer.Sparse.eval keyMomentRow1084 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1084).leftCharge (GramAssembly.key 1084).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 951) := by
    have ha : gramCharges (GramAssembly.key 1084).leftCharge (GramAssembly.key 1084).rightCharge = raw40523 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40523Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40523 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1084).leftCharge (GramAssembly.key 1084).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1084, Integer.Sparse.eval]

theorem keyMoment1085 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1085) =
      Integer.Sparse.eval keyMomentRow1085 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1085).leftCharge (GramAssembly.key 1085).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 587) := by
    have ha : gramCharges (GramAssembly.key 1085).leftCharge (GramAssembly.key 1085).rightCharge = raw40524 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40524Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40524 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1085).leftCharge (GramAssembly.key 1085).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1085, Integer.Sparse.eval]

theorem keyMoment1086 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1086) =
      Integer.Sparse.eval keyMomentRow1086 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1086).leftCharge (GramAssembly.key 1086).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 936) := by
    have ha : gramCharges (GramAssembly.key 1086).leftCharge (GramAssembly.key 1086).rightCharge = raw40525 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40525Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40525 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1086).leftCharge (GramAssembly.key 1086).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1086, Integer.Sparse.eval]

theorem keyMoment1087 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1087) =
      Integer.Sparse.eval keyMomentRow1087 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1087).leftCharge (GramAssembly.key 1087).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1027) := by
    have ha : gramCharges (GramAssembly.key 1087).leftCharge (GramAssembly.key 1087).rightCharge = raw40526 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40526Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40526 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1087).leftCharge (GramAssembly.key 1087).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1087, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1056 : keyMomentRows (1056 : Fin 2886) =
    keyMomentRow1056 := by decide +kernel

theorem keyMomentRowsAt1057 : keyMomentRows (1057 : Fin 2886) =
    keyMomentRow1057 := by decide +kernel

theorem keyMomentRowsAt1058 : keyMomentRows (1058 : Fin 2886) =
    keyMomentRow1058 := by decide +kernel

theorem keyMomentRowsAt1059 : keyMomentRows (1059 : Fin 2886) =
    keyMomentRow1059 := by decide +kernel

theorem keyMomentRowsAt1060 : keyMomentRows (1060 : Fin 2886) =
    keyMomentRow1060 := by decide +kernel

theorem keyMomentRowsAt1061 : keyMomentRows (1061 : Fin 2886) =
    keyMomentRow1061 := by decide +kernel

theorem keyMomentRowsAt1062 : keyMomentRows (1062 : Fin 2886) =
    keyMomentRow1062 := by decide +kernel

theorem keyMomentRowsAt1063 : keyMomentRows (1063 : Fin 2886) =
    keyMomentRow1063 := by decide +kernel

theorem keyMomentRowsAt1064 : keyMomentRows (1064 : Fin 2886) =
    keyMomentRow1064 := by decide +kernel

theorem keyMomentRowsAt1065 : keyMomentRows (1065 : Fin 2886) =
    keyMomentRow1065 := by decide +kernel

theorem keyMomentRowsAt1066 : keyMomentRows (1066 : Fin 2886) =
    keyMomentRow1066 := by decide +kernel

theorem keyMomentRowsAt1067 : keyMomentRows (1067 : Fin 2886) =
    keyMomentRow1067 := by decide +kernel

theorem keyMomentRowsAt1068 : keyMomentRows (1068 : Fin 2886) =
    keyMomentRow1068 := by decide +kernel

theorem keyMomentRowsAt1069 : keyMomentRows (1069 : Fin 2886) =
    keyMomentRow1069 := by decide +kernel

theorem keyMomentRowsAt1070 : keyMomentRows (1070 : Fin 2886) =
    keyMomentRow1070 := by decide +kernel

theorem keyMomentRowsAt1071 : keyMomentRows (1071 : Fin 2886) =
    keyMomentRow1071 := by decide +kernel

theorem keyMomentRowsAt1072 : keyMomentRows (1072 : Fin 2886) =
    keyMomentRow1072 := by decide +kernel

theorem keyMomentRowsAt1073 : keyMomentRows (1073 : Fin 2886) =
    keyMomentRow1073 := by decide +kernel

theorem keyMomentRowsAt1074 : keyMomentRows (1074 : Fin 2886) =
    keyMomentRow1074 := by decide +kernel

theorem keyMomentRowsAt1075 : keyMomentRows (1075 : Fin 2886) =
    keyMomentRow1075 := by decide +kernel

theorem keyMomentRowsAt1076 : keyMomentRows (1076 : Fin 2886) =
    keyMomentRow1076 := by decide +kernel

theorem keyMomentRowsAt1077 : keyMomentRows (1077 : Fin 2886) =
    keyMomentRow1077 := by decide +kernel

theorem keyMomentRowsAt1078 : keyMomentRows (1078 : Fin 2886) =
    keyMomentRow1078 := by decide +kernel

theorem keyMomentRowsAt1079 : keyMomentRows (1079 : Fin 2886) =
    keyMomentRow1079 := by decide +kernel

theorem keyMomentRowsAt1080 : keyMomentRows (1080 : Fin 2886) =
    keyMomentRow1080 := by decide +kernel

theorem keyMomentRowsAt1081 : keyMomentRows (1081 : Fin 2886) =
    keyMomentRow1081 := by decide +kernel

theorem keyMomentRowsAt1082 : keyMomentRows (1082 : Fin 2886) =
    keyMomentRow1082 := by decide +kernel

theorem keyMomentRowsAt1083 : keyMomentRows (1083 : Fin 2886) =
    keyMomentRow1083 := by decide +kernel

theorem keyMomentRowsAt1084 : keyMomentRows (1084 : Fin 2886) =
    keyMomentRow1084 := by decide +kernel

theorem keyMomentRowsAt1085 : keyMomentRows (1085 : Fin 2886) =
    keyMomentRow1085 := by decide +kernel

theorem keyMomentRowsAt1086 : keyMomentRows (1086 : Fin 2886) =
    keyMomentRow1086 := by decide +kernel

theorem keyMomentRowsAt1087 : keyMomentRows (1087 : Fin 2886) =
    keyMomentRow1087 := by decide +kernel

theorem keyMomentChunkSound33_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 33) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1056 ∨ k.val = 1057 ∨ k.val = 1058 ∨ k.val = 1059 ∨ k.val = 1060 ∨ k.val = 1061 ∨ k.val = 1062 ∨ k.val = 1063 ∨ k.val = 1064 ∨ k.val = 1065 ∨ k.val = 1066 ∨ k.val = 1067 ∨ k.val = 1068 ∨ k.val = 1069 ∨ k.val = 1070 ∨ k.val = 1071 ∨ k.val = 1072 ∨ k.val = 1073 ∨ k.val = 1074 ∨ k.val = 1075 ∨ k.val = 1076 ∨ k.val = 1077 ∨ k.val = 1078 ∨ k.val = 1079 ∨ k.val = 1080 ∨ k.val = 1081 ∨ k.val = 1082 ∨ k.val = 1083 ∨ k.val = 1084 ∨ k.val = 1085 ∨ k.val = 1086 ∨ k.val = 1087 := by omega
  rcases heq with h1056 | h1057 | h1058 | h1059 | h1060 | h1061 | h1062 | h1063 | h1064 | h1065 | h1066 | h1067 | h1068 | h1069 | h1070 | h1071 | h1072 | h1073 | h1074 | h1075 | h1076 | h1077 | h1078 | h1079 | h1080 | h1081 | h1082 | h1083 | h1084 | h1085 | h1086 | h1087
  · have he : k = (1056 : Fin 2886) := Fin.ext h1056
    subst k
    rw [keyMomentRowsAt1056]
    exact keyMoment1056 B hB
  · have he : k = (1057 : Fin 2886) := Fin.ext h1057
    subst k
    rw [keyMomentRowsAt1057]
    exact keyMoment1057 B hB
  · have he : k = (1058 : Fin 2886) := Fin.ext h1058
    subst k
    rw [keyMomentRowsAt1058]
    exact keyMoment1058 B hB
  · have he : k = (1059 : Fin 2886) := Fin.ext h1059
    subst k
    rw [keyMomentRowsAt1059]
    exact keyMoment1059 B hB
  · have he : k = (1060 : Fin 2886) := Fin.ext h1060
    subst k
    rw [keyMomentRowsAt1060]
    exact keyMoment1060 B hB
  · have he : k = (1061 : Fin 2886) := Fin.ext h1061
    subst k
    rw [keyMomentRowsAt1061]
    exact keyMoment1061 B hB
  · have he : k = (1062 : Fin 2886) := Fin.ext h1062
    subst k
    rw [keyMomentRowsAt1062]
    exact keyMoment1062 B hB
  · have he : k = (1063 : Fin 2886) := Fin.ext h1063
    subst k
    rw [keyMomentRowsAt1063]
    exact keyMoment1063 B hB
  · have he : k = (1064 : Fin 2886) := Fin.ext h1064
    subst k
    rw [keyMomentRowsAt1064]
    exact keyMoment1064 B hB
  · have he : k = (1065 : Fin 2886) := Fin.ext h1065
    subst k
    rw [keyMomentRowsAt1065]
    exact keyMoment1065 B hB
  · have he : k = (1066 : Fin 2886) := Fin.ext h1066
    subst k
    rw [keyMomentRowsAt1066]
    exact keyMoment1066 B hB
  · have he : k = (1067 : Fin 2886) := Fin.ext h1067
    subst k
    rw [keyMomentRowsAt1067]
    exact keyMoment1067 B hB
  · have he : k = (1068 : Fin 2886) := Fin.ext h1068
    subst k
    rw [keyMomentRowsAt1068]
    exact keyMoment1068 B hB
  · have he : k = (1069 : Fin 2886) := Fin.ext h1069
    subst k
    rw [keyMomentRowsAt1069]
    exact keyMoment1069 B hB
  · have he : k = (1070 : Fin 2886) := Fin.ext h1070
    subst k
    rw [keyMomentRowsAt1070]
    exact keyMoment1070 B hB
  · have he : k = (1071 : Fin 2886) := Fin.ext h1071
    subst k
    rw [keyMomentRowsAt1071]
    exact keyMoment1071 B hB
  · have he : k = (1072 : Fin 2886) := Fin.ext h1072
    subst k
    rw [keyMomentRowsAt1072]
    exact keyMoment1072 B hB
  · have he : k = (1073 : Fin 2886) := Fin.ext h1073
    subst k
    rw [keyMomentRowsAt1073]
    exact keyMoment1073 B hB
  · have he : k = (1074 : Fin 2886) := Fin.ext h1074
    subst k
    rw [keyMomentRowsAt1074]
    exact keyMoment1074 B hB
  · have he : k = (1075 : Fin 2886) := Fin.ext h1075
    subst k
    rw [keyMomentRowsAt1075]
    exact keyMoment1075 B hB
  · have he : k = (1076 : Fin 2886) := Fin.ext h1076
    subst k
    rw [keyMomentRowsAt1076]
    exact keyMoment1076 B hB
  · have he : k = (1077 : Fin 2886) := Fin.ext h1077
    subst k
    rw [keyMomentRowsAt1077]
    exact keyMoment1077 B hB
  · have he : k = (1078 : Fin 2886) := Fin.ext h1078
    subst k
    rw [keyMomentRowsAt1078]
    exact keyMoment1078 B hB
  · have he : k = (1079 : Fin 2886) := Fin.ext h1079
    subst k
    rw [keyMomentRowsAt1079]
    exact keyMoment1079 B hB
  · have he : k = (1080 : Fin 2886) := Fin.ext h1080
    subst k
    rw [keyMomentRowsAt1080]
    exact keyMoment1080 B hB
  · have he : k = (1081 : Fin 2886) := Fin.ext h1081
    subst k
    rw [keyMomentRowsAt1081]
    exact keyMoment1081 B hB
  · have he : k = (1082 : Fin 2886) := Fin.ext h1082
    subst k
    rw [keyMomentRowsAt1082]
    exact keyMoment1082 B hB
  · have he : k = (1083 : Fin 2886) := Fin.ext h1083
    subst k
    rw [keyMomentRowsAt1083]
    exact keyMoment1083 B hB
  · have he : k = (1084 : Fin 2886) := Fin.ext h1084
    subst k
    rw [keyMomentRowsAt1084]
    exact keyMoment1084 B hB
  · have he : k = (1085 : Fin 2886) := Fin.ext h1085
    subst k
    rw [keyMomentRowsAt1085]
    exact keyMoment1085 B hB
  · have he : k = (1086 : Fin 2886) := Fin.ext h1086
    subst k
    rw [keyMomentRowsAt1086]
    exact keyMoment1086 B hB
  · have he : k = (1087 : Fin 2886) := Fin.ext h1087
    subst k
    rw [keyMomentRowsAt1087]
    exact keyMoment1087 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound33_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound33_e_oai
