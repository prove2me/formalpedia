-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound46_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:56:07.735073+00:00
-- url     : https://prove2.me/submissions/ffedde09-0bcb-4d7f-93cf-dc103f9611cc

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical319
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40890 raw40890Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw40890 raw40890Labels = mixedMoment B raw40890step0 raw40890step0Labels := by
      have hz : ∀ j, raw40890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40890step0 = (fun i j => raw40890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40890step0 raw40890; decide +kernel
      have hl : raw40890step0Labels = raw40890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40890 raw40890Labels permutation434 hz
    mixedMoment B raw40890step0 raw40890step0Labels = mixedMoment B raw40890step1 raw40890step1Labels := by
      have ha : raw40890step1 = (fun i j => raw40890step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40890step1 raw40890step0; decide +kernel
      have hl : raw40890step1Labels = raw40890step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40890step0 raw40890step0Labels permutation102 permutation6
    _ = mixedMoment B node2094 node2094Labels := by rfl

theorem canonical40891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40891 raw40891Labels = mixedMoment B node1816 node1816Labels := by
  calc
    mixedMoment B raw40891 raw40891Labels = mixedMoment B raw40891step0 raw40891step0Labels := by
      have hz : ∀ j, raw40891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40891step0 = (fun i j => raw40891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40891step0 raw40891; decide +kernel
      have hl : raw40891step0Labels = raw40891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40891 raw40891Labels permutation434 hz
    mixedMoment B raw40891step0 raw40891step0Labels = mixedMoment B raw40891step1 raw40891step1Labels := by
      have ha : raw40891step1 = (fun i j => raw40891step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40891step1 raw40891step0; decide +kernel
      have hl : raw40891step1Labels = raw40891step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40891step0 raw40891step0Labels permutation102 permutation6
    _ = mixedMoment B node1816 node1816Labels := by rfl

theorem canonical40892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40892 raw40892Labels = mixedMoment B node1977 node1977Labels := by
  calc
    mixedMoment B raw40892 raw40892Labels = mixedMoment B raw40892step0 raw40892step0Labels := by
      have ha : raw40892step0 = (fun i j => raw40892 (permutation413 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40892step0 raw40892; decide +kernel
      have hl : raw40892step0Labels = raw40892Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40892 raw40892Labels permutation413 permutation6
    _ = mixedMoment B node1977 node1977Labels := by rfl

theorem canonical40893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40893 raw40893Labels = mixedMoment B node1794 node1794Labels := by
  calc
    mixedMoment B raw40893 raw40893Labels = mixedMoment B raw40893step0 raw40893step0Labels := by
      have ha : raw40893step0 = (fun i j => raw40893 (permutation432 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40893step0 raw40893; decide +kernel
      have hl : raw40893step0Labels = raw40893Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40893 raw40893Labels permutation432 permutation6
    _ = mixedMoment B node1794 node1794Labels := by rfl

theorem canonical40894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40894 raw40894Labels = mixedMoment B node2758 node2758Labels := by
  calc
    mixedMoment B raw40894 raw40894Labels = mixedMoment B raw40894step0 raw40894step0Labels := by
      have hz : ∀ j, raw40894 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40894step0 = (fun i j => raw40894 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40894step0 raw40894; decide +kernel
      have hl : raw40894step0Labels = raw40894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40894 raw40894Labels permutation520 hz
    mixedMoment B raw40894step0 raw40894step0Labels = mixedMoment B raw40894step1 raw40894step1Labels := by
      have ha : raw40894step1 = (fun i j => raw40894step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40894step1 raw40894step0; decide +kernel
      have hl : raw40894step1Labels = raw40894step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40894step0 raw40894step0Labels permutation151 permutation3
    mixedMoment B raw40894step1 raw40894step1Labels = mixedMoment B raw40894step2 raw40894step2Labels := by
      have ha : raw40894step2 = -raw40894step1 := by apply Matrix.ext; change ∀ i j, raw40894step2 i j = -(raw40894step1 i j); unfold raw40894step2 raw40894step1; decide +kernel
      have hl : raw40894step2Labels = raw40894step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2758 node2758Labels := by rfl

theorem canonical40895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40895 raw40895Labels = mixedMoment B node3083 node3083Labels := by
  calc
    mixedMoment B raw40895 raw40895Labels = mixedMoment B raw40895step0 raw40895step0Labels := by
      have ha : raw40895step0 = (fun i j => raw40895 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40895step0 raw40895; decide +kernel
      have hl : raw40895step0Labels = raw40895Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40895 raw40895Labels permutation688 permutation3
    mixedMoment B raw40895step0 raw40895step0Labels = mixedMoment B raw40895step1 raw40895step1Labels := by
      have ha : raw40895step1 = -raw40895step0 := by apply Matrix.ext; change ∀ i j, raw40895step1 i j = -(raw40895step0 i j); unfold raw40895step1 raw40895step0; decide +kernel
      have hl : raw40895step1Labels = raw40895step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3083 node3083Labels := by rfl

theorem canonical40896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40896 raw40896Labels = mixedMoment B node3780 node3780Labels := by
  calc
    mixedMoment B raw40896 raw40896Labels = mixedMoment B raw40896step0 raw40896step0Labels := by
      have ha : raw40896step0 = (fun i j => raw40896 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40896step0 raw40896; decide +kernel
      have hl : raw40896step0Labels = raw40896Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40896 raw40896Labels permutation393 permutation6
    _ = mixedMoment B node3780 node3780Labels := by rfl

theorem canonical40897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40897 raw40897Labels = mixedMoment B node3783 node3783Labels := by
  calc
    mixedMoment B raw40897 raw40897Labels = mixedMoment B raw40897step0 raw40897step0Labels := by
      have ha : raw40897step0 = (fun i j => raw40897 (permutation398 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40897step0 raw40897; decide +kernel
      have hl : raw40897step0Labels = raw40897Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40897 raw40897Labels permutation398 permutation6
    _ = mixedMoment B node3783 node3783Labels := by rfl

theorem canonical40898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40898 raw40898Labels = mixedMoment B node3710 node3710Labels := by
  calc
    mixedMoment B raw40898 raw40898Labels = mixedMoment B raw40898step0 raw40898step0Labels := by
      have ha : raw40898step0 = (fun i j => raw40898 (permutation426 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40898step0 raw40898; decide +kernel
      have hl : raw40898step0Labels = raw40898Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40898 raw40898Labels permutation426 permutation6
    _ = mixedMoment B node3710 node3710Labels := by rfl

theorem canonical40899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40899 raw40899Labels = mixedMoment B node3699 node3699Labels := by
  calc
    mixedMoment B raw40899 raw40899Labels = mixedMoment B raw40899step0 raw40899step0Labels := by
      have hz : ∀ j, raw40899 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40899step0 = (fun i j => raw40899 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40899step0 raw40899; decide +kernel
      have hl : raw40899step0Labels = raw40899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40899 raw40899Labels permutation434 hz
    mixedMoment B raw40899step0 raw40899step0Labels = mixedMoment B raw40899step1 raw40899step1Labels := by
      have ha : raw40899step1 = (fun i j => raw40899step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40899step1 raw40899step0; decide +kernel
      have hl : raw40899step1Labels = raw40899step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40899step0 raw40899step0Labels permutation96 permutation6
    _ = mixedMoment B node3699 node3699Labels := by rfl

theorem canonical40900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40900 raw40900Labels = mixedMoment B node2819 node2819Labels := by
  calc
    mixedMoment B raw40900 raw40900Labels = mixedMoment B raw40900step0 raw40900step0Labels := by
      have hz : ∀ j, raw40900 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40900step0 = (fun i j => raw40900 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40900step0 raw40900; decide +kernel
      have hl : raw40900step0Labels = raw40900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40900 raw40900Labels permutation434 hz
    mixedMoment B raw40900step0 raw40900step0Labels = mixedMoment B raw40900step1 raw40900step1Labels := by
      have ha : raw40900step1 = (fun i j => raw40900step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40900step1 raw40900step0; decide +kernel
      have hl : raw40900step1Labels = raw40900step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40900step0 raw40900step0Labels permutation144 permutation6
    _ = mixedMoment B node2819 node2819Labels := by rfl

theorem canonical40901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40901 raw40901Labels = mixedMoment B node3676 node3676Labels := by
  calc
    mixedMoment B raw40901 raw40901Labels = mixedMoment B raw40901step0 raw40901step0Labels := by
      have ha : raw40901step0 = (fun i j => raw40901 (permutation413 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40901step0 raw40901; decide +kernel
      have hl : raw40901step0Labels = raw40901Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40901 raw40901Labels permutation413 permutation6
    _ = mixedMoment B node3676 node3676Labels := by rfl

theorem canonical40902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40902 raw40902Labels = mixedMoment B node2801 node2801Labels := by
  calc
    mixedMoment B raw40902 raw40902Labels = mixedMoment B raw40902step0 raw40902step0Labels := by
      have ha : raw40902step0 = (fun i j => raw40902 (permutation645 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40902step0 raw40902; decide +kernel
      have hl : raw40902step0Labels = raw40902Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40902 raw40902Labels permutation645 permutation6
    _ = mixedMoment B node2801 node2801Labels := by rfl

theorem canonical40903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40903 raw40903Labels = mixedMoment B node3673 node3673Labels := by
  calc
    mixedMoment B raw40903 raw40903Labels = mixedMoment B raw40903step0 raw40903step0Labels := by
      have ha : raw40903step0 = (fun i j => raw40903 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40903step0 raw40903; decide +kernel
      have hl : raw40903step0Labels = raw40903Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40903 raw40903Labels permutation393 permutation6
    _ = mixedMoment B node3673 node3673Labels := by rfl

theorem canonical40904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40904 raw40904Labels = mixedMoment B node3685 node3685Labels := by
  calc
    mixedMoment B raw40904 raw40904Labels = mixedMoment B raw40904step0 raw40904step0Labels := by
      have ha : raw40904step0 = (fun i j => raw40904 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40904step0 raw40904; decide +kernel
      have hl : raw40904step0Labels = raw40904Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40904 raw40904Labels permutation393 permutation6
    _ = mixedMoment B node3685 node3685Labels := by rfl

theorem canonical40905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40905 raw40905Labels = mixedMoment B node2745 node2745Labels := by
  calc
    mixedMoment B raw40905 raw40905Labels = mixedMoment B raw40905step0 raw40905step0Labels := by
      have ha : raw40905step0 = (fun i j => raw40905 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40905step0 raw40905; decide +kernel
      have hl : raw40905step0Labels = raw40905Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40905 raw40905Labels permutation640 permutation3
    mixedMoment B raw40905step0 raw40905step0Labels = mixedMoment B raw40905step1 raw40905step1Labels := by
      have ha : raw40905step1 = -raw40905step0 := by apply Matrix.ext; change ∀ i j, raw40905step1 i j = -(raw40905step0 i j); unfold raw40905step1 raw40905step0; decide +kernel
      have hl : raw40905step1Labels = raw40905step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2745 node2745Labels := by rfl

theorem canonical40906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40906 raw40906Labels = mixedMoment B node2898 node2898Labels := by
  calc
    mixedMoment B raw40906 raw40906Labels = mixedMoment B raw40906step0 raw40906step0Labels := by
      have ha : raw40906step0 = (fun i j => raw40906 (permutation639 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40906step0 raw40906; decide +kernel
      have hl : raw40906step0Labels = raw40906Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40906 raw40906Labels permutation639 permutation6
    _ = mixedMoment B node2898 node2898Labels := by rfl

theorem canonical40907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40907 raw40907Labels = mixedMoment B node2499 node2499Labels := by
  calc
    mixedMoment B raw40907 raw40907Labels = mixedMoment B raw40907step0 raw40907step0Labels := by
      have hz : ∀ j, raw40907 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40907step0 = (fun i j => raw40907 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40907step0 raw40907; decide +kernel
      have hl : raw40907step0Labels = raw40907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40907 raw40907Labels permutation434 hz
    mixedMoment B raw40907step0 raw40907step0Labels = mixedMoment B raw40907step1 raw40907step1Labels := by
      have ha : raw40907step1 = (fun i j => raw40907step0 (permutation120 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40907step1 raw40907step0; decide +kernel
      have hl : raw40907step1Labels = raw40907step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40907step0 raw40907step0Labels permutation120 permutation6
    _ = mixedMoment B node2499 node2499Labels := by rfl

theorem canonical40908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40908 raw40908Labels = mixedMoment B node1141 node1141Labels := by
  calc
    mixedMoment B raw40908 raw40908Labels = mixedMoment B raw40908step0 raw40908step0Labels := by
      have hz : ∀ j, raw40908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40908step0 = (fun i j => raw40908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40908step0 raw40908; decide +kernel
      have hl : raw40908step0Labels = raw40908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40908 raw40908Labels permutation434 hz
    mixedMoment B raw40908step0 raw40908step0Labels = mixedMoment B raw40908step1 raw40908step1Labels := by
      have ha : raw40908step1 = (fun i j => raw40908step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40908step1 raw40908step0; decide +kernel
      have hl : raw40908step1Labels = raw40908step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40908step0 raw40908step0Labels permutation144 permutation6
    _ = mixedMoment B node1141 node1141Labels := by rfl

theorem canonical40909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40909 raw40909Labels = mixedMoment B node2441 node2441Labels := by
  calc
    mixedMoment B raw40909 raw40909Labels = mixedMoment B raw40909step0 raw40909step0Labels := by
      have ha : raw40909step0 = (fun i j => raw40909 (permutation551 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40909step0 raw40909; decide +kernel
      have hl : raw40909step0Labels = raw40909Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40909 raw40909Labels permutation551 permutation6
    _ = mixedMoment B node2441 node2441Labels := by rfl

theorem canonical40910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40910 raw40910Labels = mixedMoment B node1117 node1117Labels := by
  calc
    mixedMoment B raw40910 raw40910Labels = mixedMoment B raw40910step0 raw40910step0Labels := by
      have ha : raw40910step0 = (fun i j => raw40910 (permutation645 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40910step0 raw40910; decide +kernel
      have hl : raw40910step0Labels = raw40910Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40910 raw40910Labels permutation645 permutation6
    _ = mixedMoment B node1117 node1117Labels := by rfl

theorem canonical40911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40911 raw40911Labels = mixedMoment B node2433 node2433Labels := by
  calc
    mixedMoment B raw40911 raw40911Labels = mixedMoment B raw40911step0 raw40911step0Labels := by
      have ha : raw40911step0 = (fun i j => raw40911 (permutation479 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40911step0 raw40911; decide +kernel
      have hl : raw40911step0Labels = raw40911Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40911 raw40911Labels permutation479 permutation6
    _ = mixedMoment B node2433 node2433Labels := by rfl

theorem canonical40912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40912 raw40912Labels = mixedMoment B node2473 node2473Labels := by
  calc
    mixedMoment B raw40912 raw40912Labels = mixedMoment B raw40912step0 raw40912step0Labels := by
      have ha : raw40912step0 = (fun i j => raw40912 (permutation479 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40912step0 raw40912; decide +kernel
      have hl : raw40912step0Labels = raw40912Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40912 raw40912Labels permutation479 permutation6
    _ = mixedMoment B node2473 node2473Labels := by rfl

theorem canonical40913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40913 raw40913Labels = mixedMoment B node1063 node1063Labels := by
  calc
    mixedMoment B raw40913 raw40913Labels = mixedMoment B raw40913step0 raw40913step0Labels := by
      have hz : ∀ j, raw40913 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40913step0 = (fun i j => raw40913 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40913step0 raw40913; decide +kernel
      have hl : raw40913step0Labels = raw40913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40913 raw40913Labels permutation434 hz
    mixedMoment B raw40913step0 raw40913step0Labels = mixedMoment B raw40913step1 raw40913step1Labels := by
      have hz : ∀ j, raw40913step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40913step1 = (fun i j => raw40913step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40913step1 raw40913step0; decide +kernel
      have hl : raw40913step1Labels = raw40913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40913step0 raw40913step0Labels permutation80 hz
    mixedMoment B raw40913step1 raw40913step1Labels = mixedMoment B raw40913step2 raw40913step2Labels := by
      have ha : raw40913step2 = (fun i j => raw40913step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40913step2 raw40913step1; decide +kernel
      have hl : raw40913step2Labels = raw40913step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40913step1 raw40913step1Labels permutation24 permutation6
    _ = mixedMoment B node1063 node1063Labels := by rfl

theorem canonical40914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40914 raw40914Labels = mixedMoment B node616 node616Labels := by
  calc
    mixedMoment B raw40914 raw40914Labels = mixedMoment B raw40914step0 raw40914step0Labels := by
      have hz : ∀ j, raw40914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40914step0 = (fun i j => raw40914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40914step0 raw40914; decide +kernel
      have hl : raw40914step0Labels = raw40914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40914 raw40914Labels permutation434 hz
    mixedMoment B raw40914step0 raw40914step0Labels = mixedMoment B raw40914step1 raw40914step1Labels := by
      have hz : ∀ j, raw40914step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40914step1 = (fun i j => raw40914step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40914step1 raw40914step0; decide +kernel
      have hl : raw40914step1Labels = raw40914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40914step0 raw40914step0Labels permutation80 hz
    mixedMoment B raw40914step1 raw40914step1Labels = mixedMoment B raw40914step2 raw40914step2Labels := by
      have ha : raw40914step2 = (fun i j => raw40914step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40914step2 raw40914step1; decide +kernel
      have hl : raw40914step2Labels = raw40914step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40914step1 raw40914step1Labels permutation30 permutation6
    _ = mixedMoment B node616 node616Labels := by rfl

theorem canonical40915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40915 raw40915Labels = mixedMoment B node950 node950Labels := by
  calc
    mixedMoment B raw40915 raw40915Labels = mixedMoment B raw40915step0 raw40915step0Labels := by
      have hz : ∀ j, raw40915 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40915step0 = (fun i j => raw40915 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40915step0 raw40915; decide +kernel
      have hl : raw40915step0Labels = raw40915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40915 raw40915Labels permutation346 hz
    mixedMoment B raw40915step0 raw40915step0Labels = mixedMoment B raw40915step1 raw40915step1Labels := by
      have ha : raw40915step1 = (fun i j => raw40915step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40915step1 raw40915step0; decide +kernel
      have hl : raw40915step1Labels = raw40915step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40915step0 raw40915step0Labels permutation126 permutation6
    _ = mixedMoment B node950 node950Labels := by rfl

theorem canonical40916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40916 raw40916Labels = mixedMoment B node586 node586Labels := by
  calc
    mixedMoment B raw40916 raw40916Labels = mixedMoment B raw40916step0 raw40916step0Labels := by
      have hz : ∀ j, raw40916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40916step0 = (fun i j => raw40916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40916step0 raw40916; decide +kernel
      have hl : raw40916step0Labels = raw40916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40916 raw40916Labels permutation346 hz
    mixedMoment B raw40916step0 raw40916step0Labels = mixedMoment B raw40916step1 raw40916step1Labels := by
      have ha : raw40916step1 = (fun i j => raw40916step0 (permutation150 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40916step1 raw40916step0; decide +kernel
      have hl : raw40916step1Labels = raw40916step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40916step0 raw40916step0Labels permutation150 permutation6
    _ = mixedMoment B node586 node586Labels := by rfl

theorem canonical40917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40917 raw40917Labels = mixedMoment B node1830 node1830Labels := by
  calc
    mixedMoment B raw40917 raw40917Labels = mixedMoment B raw40917step0 raw40917step0Labels := by
      have hz : ∀ j, raw40917 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40917step0 = (fun i j => raw40917 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40917step0 raw40917; decide +kernel
      have hl : raw40917step0Labels = raw40917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40917 raw40917Labels permutation520 hz
    mixedMoment B raw40917step0 raw40917step0Labels = mixedMoment B raw40917step1 raw40917step1Labels := by
      have hz : ∀ j, raw40917step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40917step1 = (fun i j => raw40917step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40917step1 raw40917step0; decide +kernel
      have hl : raw40917step1Labels = raw40917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40917step0 raw40917step0Labels permutation104 hz
    mixedMoment B raw40917step1 raw40917step1Labels = mixedMoment B raw40917step2 raw40917step2Labels := by
      have ha : raw40917step2 = (fun i j => raw40917step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40917step2 raw40917step1; decide +kernel
      have hl : raw40917step2Labels = raw40917step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40917step1 raw40917step1Labels permutation24 permutation6
    _ = mixedMoment B node1830 node1830Labels := by rfl

theorem canonical40918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40918 raw40918Labels = mixedMoment B node1978 node1978Labels := by
  calc
    mixedMoment B raw40918 raw40918Labels = mixedMoment B raw40918step0 raw40918step0Labels := by
      have hz : ∀ j, raw40918 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40918step0 = (fun i j => raw40918 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40918step0 raw40918; decide +kernel
      have hl : raw40918step0Labels = raw40918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40918 raw40918Labels permutation434 hz
    mixedMoment B raw40918step0 raw40918step0Labels = mixedMoment B raw40918step1 raw40918step1Labels := by
      have ha : raw40918step1 = (fun i j => raw40918step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40918step1 raw40918step0; decide +kernel
      have hl : raw40918step1Labels = raw40918step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40918step0 raw40918step0Labels permutation96 permutation6
    _ = mixedMoment B node1978 node1978Labels := by rfl

theorem canonical40919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40919 raw40919Labels = mixedMoment B node1795 node1795Labels := by
  calc
    mixedMoment B raw40919 raw40919Labels = mixedMoment B raw40919step0 raw40919step0Labels := by
      have hz : ∀ j, raw40919 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40919step0 = (fun i j => raw40919 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40919step0 raw40919; decide +kernel
      have hl : raw40919step0Labels = raw40919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40919 raw40919Labels permutation434 hz
    mixedMoment B raw40919step0 raw40919step0Labels = mixedMoment B raw40919step1 raw40919step1Labels := by
      have ha : raw40919step1 = (fun i j => raw40919step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40919step1 raw40919step0; decide +kernel
      have hl : raw40919step1Labels = raw40919step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40919step0 raw40919step0Labels permutation102 permutation6
    _ = mixedMoment B node1795 node1795Labels := by rfl

theorem canonical40920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40920 raw40920Labels = mixedMoment B node2362 node2362Labels := by
  calc
    mixedMoment B raw40920 raw40920Labels = mixedMoment B raw40920step0 raw40920step0Labels := by
      have hz : ∀ j, raw40920 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40920step0 = (fun i j => raw40920 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40920step0 raw40920; decide +kernel
      have hl : raw40920step0Labels = raw40920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40920 raw40920Labels permutation520 hz
    mixedMoment B raw40920step0 raw40920step0Labels = mixedMoment B raw40920step1 raw40920step1Labels := by
      have ha : raw40920step1 = (fun i j => raw40920step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40920step1 raw40920step0; decide +kernel
      have hl : raw40920step1Labels = raw40920step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40920step0 raw40920step0Labels permutation59 permutation6
    mixedMoment B raw40920step1 raw40920step1Labels = mixedMoment B raw40920step2 raw40920step2Labels := by
      have ha : raw40920step2 = -raw40920step1 := by apply Matrix.ext; change ∀ i j, raw40920step2 i j = -(raw40920step1 i j); unfold raw40920step2 raw40920step1; decide +kernel
      have hl : raw40920step2Labels = raw40920step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2362 node2362Labels := by rfl

theorem canonical40921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40921 raw40921Labels = mixedMoment B node2353 node2353Labels := by
  calc
    mixedMoment B raw40921 raw40921Labels = mixedMoment B raw40921step0 raw40921step0Labels := by
      have ha : raw40921step0 = (fun i j => raw40921 (permutation288 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40921step0 raw40921; decide +kernel
      have hl : raw40921step0Labels = raw40921Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40921 raw40921Labels permutation288 permutation6
    mixedMoment B raw40921step0 raw40921step0Labels = mixedMoment B raw40921step1 raw40921step1Labels := by
      have ha : raw40921step1 = -raw40921step0 := by apply Matrix.ext; change ∀ i j, raw40921step1 i j = -(raw40921step0 i j); unfold raw40921step1 raw40921step0; decide +kernel
      have hl : raw40921step1Labels = raw40921step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2353 node2353Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1472 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1472) =
      Integer.Sparse.eval keyMomentRow1472 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1472).leftCharge (GramAssembly.key 1472).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2094) := by
    have ha : gramCharges (GramAssembly.key 1472).leftCharge (GramAssembly.key 1472).rightCharge = raw40890 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40890Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40890 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1472).leftCharge (GramAssembly.key 1472).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1472, Integer.Sparse.eval]

theorem keyMoment1473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1473) =
      Integer.Sparse.eval keyMomentRow1473 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1473).leftCharge (GramAssembly.key 1473).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1816) := by
    have ha : gramCharges (GramAssembly.key 1473).leftCharge (GramAssembly.key 1473).rightCharge = raw40891 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40891Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40891 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1473).leftCharge (GramAssembly.key 1473).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1473, Integer.Sparse.eval]

theorem keyMoment1474 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1474) =
      Integer.Sparse.eval keyMomentRow1474 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1474).leftCharge (GramAssembly.key 1474).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1977) := by
    have ha : gramCharges (GramAssembly.key 1474).leftCharge (GramAssembly.key 1474).rightCharge = raw40892 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40892Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40892 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1474).leftCharge (GramAssembly.key 1474).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1474, Integer.Sparse.eval]

theorem keyMoment1475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1475) =
      Integer.Sparse.eval keyMomentRow1475 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1475).leftCharge (GramAssembly.key 1475).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1794) := by
    have ha : gramCharges (GramAssembly.key 1475).leftCharge (GramAssembly.key 1475).rightCharge = raw40893 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40893Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40893 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1475).leftCharge (GramAssembly.key 1475).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1475, Integer.Sparse.eval]

theorem keyMoment1476 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1476) =
      Integer.Sparse.eval keyMomentRow1476 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1476).leftCharge (GramAssembly.key 1476).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2758) := by
    have ha : gramCharges (GramAssembly.key 1476).leftCharge (GramAssembly.key 1476).rightCharge = raw40894 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40894Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40894 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1476).leftCharge (GramAssembly.key 1476).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1476, Integer.Sparse.eval]

theorem keyMoment1477 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1477) =
      Integer.Sparse.eval keyMomentRow1477 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1477).leftCharge (GramAssembly.key 1477).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3083) := by
    have ha : gramCharges (GramAssembly.key 1477).leftCharge (GramAssembly.key 1477).rightCharge = raw40895 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40895Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40895 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1477).leftCharge (GramAssembly.key 1477).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1477, Integer.Sparse.eval]

theorem keyMoment1478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1478) =
      Integer.Sparse.eval keyMomentRow1478 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1478).leftCharge (GramAssembly.key 1478).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3780) := by
    have ha : gramCharges (GramAssembly.key 1478).leftCharge (GramAssembly.key 1478).rightCharge = raw40896 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40896Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40896 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1478).leftCharge (GramAssembly.key 1478).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1478, Integer.Sparse.eval]

theorem keyMoment1479 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1479) =
      Integer.Sparse.eval keyMomentRow1479 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1479).leftCharge (GramAssembly.key 1479).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3783) := by
    have ha : gramCharges (GramAssembly.key 1479).leftCharge (GramAssembly.key 1479).rightCharge = raw40897 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40897Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40897 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1479).leftCharge (GramAssembly.key 1479).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1479, Integer.Sparse.eval]

theorem keyMoment1480 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1480) =
      Integer.Sparse.eval keyMomentRow1480 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1480).leftCharge (GramAssembly.key 1480).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3710) := by
    have ha : gramCharges (GramAssembly.key 1480).leftCharge (GramAssembly.key 1480).rightCharge = raw40898 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40898Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40898 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1480).leftCharge (GramAssembly.key 1480).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1480, Integer.Sparse.eval]

theorem keyMoment1481 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1481) =
      Integer.Sparse.eval keyMomentRow1481 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1481).leftCharge (GramAssembly.key 1481).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3699) := by
    have ha : gramCharges (GramAssembly.key 1481).leftCharge (GramAssembly.key 1481).rightCharge = raw40899 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40899Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40899 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1481).leftCharge (GramAssembly.key 1481).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1481, Integer.Sparse.eval]

theorem keyMoment1482 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1482) =
      Integer.Sparse.eval keyMomentRow1482 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1482).leftCharge (GramAssembly.key 1482).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2819) := by
    have ha : gramCharges (GramAssembly.key 1482).leftCharge (GramAssembly.key 1482).rightCharge = raw40900 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40900Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40900 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1482).leftCharge (GramAssembly.key 1482).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1482, Integer.Sparse.eval]

theorem keyMoment1483 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1483) =
      Integer.Sparse.eval keyMomentRow1483 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1483).leftCharge (GramAssembly.key 1483).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3676) := by
    have ha : gramCharges (GramAssembly.key 1483).leftCharge (GramAssembly.key 1483).rightCharge = raw40901 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40901Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40901 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1483).leftCharge (GramAssembly.key 1483).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1483, Integer.Sparse.eval]

theorem keyMoment1484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1484) =
      Integer.Sparse.eval keyMomentRow1484 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1484).leftCharge (GramAssembly.key 1484).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2801) := by
    have ha : gramCharges (GramAssembly.key 1484).leftCharge (GramAssembly.key 1484).rightCharge = raw40902 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40902Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40902 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1484).leftCharge (GramAssembly.key 1484).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1484, Integer.Sparse.eval]

theorem keyMoment1485 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1485) =
      Integer.Sparse.eval keyMomentRow1485 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1485).leftCharge (GramAssembly.key 1485).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3673) := by
    have ha : gramCharges (GramAssembly.key 1485).leftCharge (GramAssembly.key 1485).rightCharge = raw40903 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40903Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40903 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1485).leftCharge (GramAssembly.key 1485).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1485, Integer.Sparse.eval]

theorem keyMoment1486 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1486) =
      Integer.Sparse.eval keyMomentRow1486 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1486).leftCharge (GramAssembly.key 1486).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3685) := by
    have ha : gramCharges (GramAssembly.key 1486).leftCharge (GramAssembly.key 1486).rightCharge = raw40904 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40904Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40904 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1486).leftCharge (GramAssembly.key 1486).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1486, Integer.Sparse.eval]

theorem keyMoment1487 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1487) =
      Integer.Sparse.eval keyMomentRow1487 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1487).leftCharge (GramAssembly.key 1487).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2745) := by
    have ha : gramCharges (GramAssembly.key 1487).leftCharge (GramAssembly.key 1487).rightCharge = raw40905 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40905Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40905 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1487).leftCharge (GramAssembly.key 1487).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1487, Integer.Sparse.eval]

theorem keyMoment1488 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1488) =
      Integer.Sparse.eval keyMomentRow1488 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1488).leftCharge (GramAssembly.key 1488).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2898) := by
    have ha : gramCharges (GramAssembly.key 1488).leftCharge (GramAssembly.key 1488).rightCharge = raw40906 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40906Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40906 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1488).leftCharge (GramAssembly.key 1488).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1488, Integer.Sparse.eval]

theorem keyMoment1489 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1489) =
      Integer.Sparse.eval keyMomentRow1489 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1489).leftCharge (GramAssembly.key 1489).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2499) := by
    have ha : gramCharges (GramAssembly.key 1489).leftCharge (GramAssembly.key 1489).rightCharge = raw40907 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40907Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40907 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1489).leftCharge (GramAssembly.key 1489).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1489, Integer.Sparse.eval]

theorem keyMoment1490 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1490) =
      Integer.Sparse.eval keyMomentRow1490 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1490).leftCharge (GramAssembly.key 1490).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1141) := by
    have ha : gramCharges (GramAssembly.key 1490).leftCharge (GramAssembly.key 1490).rightCharge = raw40908 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40908Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40908 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1490).leftCharge (GramAssembly.key 1490).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1490, Integer.Sparse.eval]

theorem keyMoment1491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1491) =
      Integer.Sparse.eval keyMomentRow1491 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1491).leftCharge (GramAssembly.key 1491).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2441) := by
    have ha : gramCharges (GramAssembly.key 1491).leftCharge (GramAssembly.key 1491).rightCharge = raw40909 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40909Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40909 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1491).leftCharge (GramAssembly.key 1491).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1491, Integer.Sparse.eval]

theorem keyMoment1492 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1492) =
      Integer.Sparse.eval keyMomentRow1492 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1492).leftCharge (GramAssembly.key 1492).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1117) := by
    have ha : gramCharges (GramAssembly.key 1492).leftCharge (GramAssembly.key 1492).rightCharge = raw40910 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40910Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40910 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1492).leftCharge (GramAssembly.key 1492).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1492, Integer.Sparse.eval]

theorem keyMoment1493 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1493) =
      Integer.Sparse.eval keyMomentRow1493 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1493).leftCharge (GramAssembly.key 1493).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2433) := by
    have ha : gramCharges (GramAssembly.key 1493).leftCharge (GramAssembly.key 1493).rightCharge = raw40911 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40911Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40911 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1493).leftCharge (GramAssembly.key 1493).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1493, Integer.Sparse.eval]

theorem keyMoment1494 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1494) =
      Integer.Sparse.eval keyMomentRow1494 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1494).leftCharge (GramAssembly.key 1494).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2473) := by
    have ha : gramCharges (GramAssembly.key 1494).leftCharge (GramAssembly.key 1494).rightCharge = raw40912 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40912Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40912 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1494).leftCharge (GramAssembly.key 1494).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1494, Integer.Sparse.eval]

theorem keyMoment1495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1495) =
      Integer.Sparse.eval keyMomentRow1495 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1495).leftCharge (GramAssembly.key 1495).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1063) := by
    have ha : gramCharges (GramAssembly.key 1495).leftCharge (GramAssembly.key 1495).rightCharge = raw40913 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40913Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40913 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1495).leftCharge (GramAssembly.key 1495).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1495, Integer.Sparse.eval]

theorem keyMoment1496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1496) =
      Integer.Sparse.eval keyMomentRow1496 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1496).leftCharge (GramAssembly.key 1496).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 616) := by
    have ha : gramCharges (GramAssembly.key 1496).leftCharge (GramAssembly.key 1496).rightCharge = raw40914 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40914Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40914 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1496).leftCharge (GramAssembly.key 1496).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1496, Integer.Sparse.eval]

theorem keyMoment1497 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1497) =
      Integer.Sparse.eval keyMomentRow1497 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1497).leftCharge (GramAssembly.key 1497).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 950) := by
    have ha : gramCharges (GramAssembly.key 1497).leftCharge (GramAssembly.key 1497).rightCharge = raw40915 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40915Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40915 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1497).leftCharge (GramAssembly.key 1497).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1497, Integer.Sparse.eval]

theorem keyMoment1498 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1498) =
      Integer.Sparse.eval keyMomentRow1498 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1498).leftCharge (GramAssembly.key 1498).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 586) := by
    have ha : gramCharges (GramAssembly.key 1498).leftCharge (GramAssembly.key 1498).rightCharge = raw40916 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40916Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40916 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1498).leftCharge (GramAssembly.key 1498).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1498, Integer.Sparse.eval]

theorem keyMoment1499 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1499) =
      Integer.Sparse.eval keyMomentRow1499 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1499).leftCharge (GramAssembly.key 1499).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1830) := by
    have ha : gramCharges (GramAssembly.key 1499).leftCharge (GramAssembly.key 1499).rightCharge = raw40917 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40917Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40917 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1499).leftCharge (GramAssembly.key 1499).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1499, Integer.Sparse.eval]

theorem keyMoment1500 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1500) =
      Integer.Sparse.eval keyMomentRow1500 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1500).leftCharge (GramAssembly.key 1500).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1978) := by
    have ha : gramCharges (GramAssembly.key 1500).leftCharge (GramAssembly.key 1500).rightCharge = raw40918 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40918Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40918 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1500).leftCharge (GramAssembly.key 1500).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1500, Integer.Sparse.eval]

theorem keyMoment1501 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1501) =
      Integer.Sparse.eval keyMomentRow1501 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1501).leftCharge (GramAssembly.key 1501).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1795) := by
    have ha : gramCharges (GramAssembly.key 1501).leftCharge (GramAssembly.key 1501).rightCharge = raw40919 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40919Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40919 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1501).leftCharge (GramAssembly.key 1501).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1501, Integer.Sparse.eval]

theorem keyMoment1502 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1502) =
      Integer.Sparse.eval keyMomentRow1502 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1502).leftCharge (GramAssembly.key 1502).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2362) := by
    have ha : gramCharges (GramAssembly.key 1502).leftCharge (GramAssembly.key 1502).rightCharge = raw40920 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40920Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40920 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1502).leftCharge (GramAssembly.key 1502).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1502, Integer.Sparse.eval]

theorem keyMoment1503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1503) =
      Integer.Sparse.eval keyMomentRow1503 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1503).leftCharge (GramAssembly.key 1503).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2353) := by
    have ha : gramCharges (GramAssembly.key 1503).leftCharge (GramAssembly.key 1503).rightCharge = raw40921 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40921Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40921 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1503).leftCharge (GramAssembly.key 1503).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1503, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1472 : keyMomentRows (1472 : Fin 2886) =
    keyMomentRow1472 := by decide +kernel

theorem keyMomentRowsAt1473 : keyMomentRows (1473 : Fin 2886) =
    keyMomentRow1473 := by decide +kernel

theorem keyMomentRowsAt1474 : keyMomentRows (1474 : Fin 2886) =
    keyMomentRow1474 := by decide +kernel

theorem keyMomentRowsAt1475 : keyMomentRows (1475 : Fin 2886) =
    keyMomentRow1475 := by decide +kernel

theorem keyMomentRowsAt1476 : keyMomentRows (1476 : Fin 2886) =
    keyMomentRow1476 := by decide +kernel

theorem keyMomentRowsAt1477 : keyMomentRows (1477 : Fin 2886) =
    keyMomentRow1477 := by decide +kernel

theorem keyMomentRowsAt1478 : keyMomentRows (1478 : Fin 2886) =
    keyMomentRow1478 := by decide +kernel

theorem keyMomentRowsAt1479 : keyMomentRows (1479 : Fin 2886) =
    keyMomentRow1479 := by decide +kernel

theorem keyMomentRowsAt1480 : keyMomentRows (1480 : Fin 2886) =
    keyMomentRow1480 := by decide +kernel

theorem keyMomentRowsAt1481 : keyMomentRows (1481 : Fin 2886) =
    keyMomentRow1481 := by decide +kernel

theorem keyMomentRowsAt1482 : keyMomentRows (1482 : Fin 2886) =
    keyMomentRow1482 := by decide +kernel

theorem keyMomentRowsAt1483 : keyMomentRows (1483 : Fin 2886) =
    keyMomentRow1483 := by decide +kernel

theorem keyMomentRowsAt1484 : keyMomentRows (1484 : Fin 2886) =
    keyMomentRow1484 := by decide +kernel

theorem keyMomentRowsAt1485 : keyMomentRows (1485 : Fin 2886) =
    keyMomentRow1485 := by decide +kernel

theorem keyMomentRowsAt1486 : keyMomentRows (1486 : Fin 2886) =
    keyMomentRow1486 := by decide +kernel

theorem keyMomentRowsAt1487 : keyMomentRows (1487 : Fin 2886) =
    keyMomentRow1487 := by decide +kernel

theorem keyMomentRowsAt1488 : keyMomentRows (1488 : Fin 2886) =
    keyMomentRow1488 := by decide +kernel

theorem keyMomentRowsAt1489 : keyMomentRows (1489 : Fin 2886) =
    keyMomentRow1489 := by decide +kernel

theorem keyMomentRowsAt1490 : keyMomentRows (1490 : Fin 2886) =
    keyMomentRow1490 := by decide +kernel

theorem keyMomentRowsAt1491 : keyMomentRows (1491 : Fin 2886) =
    keyMomentRow1491 := by decide +kernel

theorem keyMomentRowsAt1492 : keyMomentRows (1492 : Fin 2886) =
    keyMomentRow1492 := by decide +kernel

theorem keyMomentRowsAt1493 : keyMomentRows (1493 : Fin 2886) =
    keyMomentRow1493 := by decide +kernel

theorem keyMomentRowsAt1494 : keyMomentRows (1494 : Fin 2886) =
    keyMomentRow1494 := by decide +kernel

theorem keyMomentRowsAt1495 : keyMomentRows (1495 : Fin 2886) =
    keyMomentRow1495 := by decide +kernel

theorem keyMomentRowsAt1496 : keyMomentRows (1496 : Fin 2886) =
    keyMomentRow1496 := by decide +kernel

theorem keyMomentRowsAt1497 : keyMomentRows (1497 : Fin 2886) =
    keyMomentRow1497 := by decide +kernel

theorem keyMomentRowsAt1498 : keyMomentRows (1498 : Fin 2886) =
    keyMomentRow1498 := by decide +kernel

theorem keyMomentRowsAt1499 : keyMomentRows (1499 : Fin 2886) =
    keyMomentRow1499 := by decide +kernel

theorem keyMomentRowsAt1500 : keyMomentRows (1500 : Fin 2886) =
    keyMomentRow1500 := by decide +kernel

theorem keyMomentRowsAt1501 : keyMomentRows (1501 : Fin 2886) =
    keyMomentRow1501 := by decide +kernel

theorem keyMomentRowsAt1502 : keyMomentRows (1502 : Fin 2886) =
    keyMomentRow1502 := by decide +kernel

theorem keyMomentRowsAt1503 : keyMomentRows (1503 : Fin 2886) =
    keyMomentRow1503 := by decide +kernel

theorem keyMomentChunkSound46_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 46) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1472 ∨ k.val = 1473 ∨ k.val = 1474 ∨ k.val = 1475 ∨ k.val = 1476 ∨ k.val = 1477 ∨ k.val = 1478 ∨ k.val = 1479 ∨ k.val = 1480 ∨ k.val = 1481 ∨ k.val = 1482 ∨ k.val = 1483 ∨ k.val = 1484 ∨ k.val = 1485 ∨ k.val = 1486 ∨ k.val = 1487 ∨ k.val = 1488 ∨ k.val = 1489 ∨ k.val = 1490 ∨ k.val = 1491 ∨ k.val = 1492 ∨ k.val = 1493 ∨ k.val = 1494 ∨ k.val = 1495 ∨ k.val = 1496 ∨ k.val = 1497 ∨ k.val = 1498 ∨ k.val = 1499 ∨ k.val = 1500 ∨ k.val = 1501 ∨ k.val = 1502 ∨ k.val = 1503 := by omega
  rcases heq with h1472 | h1473 | h1474 | h1475 | h1476 | h1477 | h1478 | h1479 | h1480 | h1481 | h1482 | h1483 | h1484 | h1485 | h1486 | h1487 | h1488 | h1489 | h1490 | h1491 | h1492 | h1493 | h1494 | h1495 | h1496 | h1497 | h1498 | h1499 | h1500 | h1501 | h1502 | h1503
  · have he : k = (1472 : Fin 2886) := Fin.ext h1472
    subst k
    rw [keyMomentRowsAt1472]
    exact keyMoment1472 B hB
  · have he : k = (1473 : Fin 2886) := Fin.ext h1473
    subst k
    rw [keyMomentRowsAt1473]
    exact keyMoment1473 B hB
  · have he : k = (1474 : Fin 2886) := Fin.ext h1474
    subst k
    rw [keyMomentRowsAt1474]
    exact keyMoment1474 B hB
  · have he : k = (1475 : Fin 2886) := Fin.ext h1475
    subst k
    rw [keyMomentRowsAt1475]
    exact keyMoment1475 B hB
  · have he : k = (1476 : Fin 2886) := Fin.ext h1476
    subst k
    rw [keyMomentRowsAt1476]
    exact keyMoment1476 B hB
  · have he : k = (1477 : Fin 2886) := Fin.ext h1477
    subst k
    rw [keyMomentRowsAt1477]
    exact keyMoment1477 B hB
  · have he : k = (1478 : Fin 2886) := Fin.ext h1478
    subst k
    rw [keyMomentRowsAt1478]
    exact keyMoment1478 B hB
  · have he : k = (1479 : Fin 2886) := Fin.ext h1479
    subst k
    rw [keyMomentRowsAt1479]
    exact keyMoment1479 B hB
  · have he : k = (1480 : Fin 2886) := Fin.ext h1480
    subst k
    rw [keyMomentRowsAt1480]
    exact keyMoment1480 B hB
  · have he : k = (1481 : Fin 2886) := Fin.ext h1481
    subst k
    rw [keyMomentRowsAt1481]
    exact keyMoment1481 B hB
  · have he : k = (1482 : Fin 2886) := Fin.ext h1482
    subst k
    rw [keyMomentRowsAt1482]
    exact keyMoment1482 B hB
  · have he : k = (1483 : Fin 2886) := Fin.ext h1483
    subst k
    rw [keyMomentRowsAt1483]
    exact keyMoment1483 B hB
  · have he : k = (1484 : Fin 2886) := Fin.ext h1484
    subst k
    rw [keyMomentRowsAt1484]
    exact keyMoment1484 B hB
  · have he : k = (1485 : Fin 2886) := Fin.ext h1485
    subst k
    rw [keyMomentRowsAt1485]
    exact keyMoment1485 B hB
  · have he : k = (1486 : Fin 2886) := Fin.ext h1486
    subst k
    rw [keyMomentRowsAt1486]
    exact keyMoment1486 B hB
  · have he : k = (1487 : Fin 2886) := Fin.ext h1487
    subst k
    rw [keyMomentRowsAt1487]
    exact keyMoment1487 B hB
  · have he : k = (1488 : Fin 2886) := Fin.ext h1488
    subst k
    rw [keyMomentRowsAt1488]
    exact keyMoment1488 B hB
  · have he : k = (1489 : Fin 2886) := Fin.ext h1489
    subst k
    rw [keyMomentRowsAt1489]
    exact keyMoment1489 B hB
  · have he : k = (1490 : Fin 2886) := Fin.ext h1490
    subst k
    rw [keyMomentRowsAt1490]
    exact keyMoment1490 B hB
  · have he : k = (1491 : Fin 2886) := Fin.ext h1491
    subst k
    rw [keyMomentRowsAt1491]
    exact keyMoment1491 B hB
  · have he : k = (1492 : Fin 2886) := Fin.ext h1492
    subst k
    rw [keyMomentRowsAt1492]
    exact keyMoment1492 B hB
  · have he : k = (1493 : Fin 2886) := Fin.ext h1493
    subst k
    rw [keyMomentRowsAt1493]
    exact keyMoment1493 B hB
  · have he : k = (1494 : Fin 2886) := Fin.ext h1494
    subst k
    rw [keyMomentRowsAt1494]
    exact keyMoment1494 B hB
  · have he : k = (1495 : Fin 2886) := Fin.ext h1495
    subst k
    rw [keyMomentRowsAt1495]
    exact keyMoment1495 B hB
  · have he : k = (1496 : Fin 2886) := Fin.ext h1496
    subst k
    rw [keyMomentRowsAt1496]
    exact keyMoment1496 B hB
  · have he : k = (1497 : Fin 2886) := Fin.ext h1497
    subst k
    rw [keyMomentRowsAt1497]
    exact keyMoment1497 B hB
  · have he : k = (1498 : Fin 2886) := Fin.ext h1498
    subst k
    rw [keyMomentRowsAt1498]
    exact keyMoment1498 B hB
  · have he : k = (1499 : Fin 2886) := Fin.ext h1499
    subst k
    rw [keyMomentRowsAt1499]
    exact keyMoment1499 B hB
  · have he : k = (1500 : Fin 2886) := Fin.ext h1500
    subst k
    rw [keyMomentRowsAt1500]
    exact keyMoment1500 B hB
  · have he : k = (1501 : Fin 2886) := Fin.ext h1501
    subst k
    rw [keyMomentRowsAt1501]
    exact keyMoment1501 B hB
  · have he : k = (1502 : Fin 2886) := Fin.ext h1502
    subst k
    rw [keyMomentRowsAt1502]
    exact keyMoment1502 B hB
  · have he : k = (1503 : Fin 2886) := Fin.ext h1503
    subst k
    rw [keyMomentRowsAt1503]
    exact keyMoment1503 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound46_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound46_e_oai
