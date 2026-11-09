-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound35_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:53:03.77805+00:00
-- url     : https://prove2.me/submissions/4959bb7a-cb08-4367-ae38-463936be0409

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E104
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2930 raw2930Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2930 raw2930Labels = mixedMoment B raw2930step0 raw2930step0Labels := by
      have hz : ∀ j, raw2930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2930step0 = (fun i j => raw2930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2930step0 raw2930; decide +kernel
      have hl : raw2930step0Labels = raw2930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2930 raw2930Labels permutation434 hz
    mixedMoment B raw2930step0 raw2930step0Labels = mixedMoment B raw2930step1 raw2930step1Labels := by
      have hz : ∀ j, raw2930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2930step1 = (fun i j => raw2930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2930step1 raw2930step0; decide +kernel
      have hl : raw2930step1Labels = raw2930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2930step0 raw2930step0Labels permutation80 hz
    mixedMoment B raw2930step1 raw2930step1Labels = mixedMoment B raw2930step2 raw2930step2Labels := by
      have hz : ∀ i, raw2930step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2930step2 = (fun i j => raw2930step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2930step2 raw2930step1; decide +kernel
      have hl : raw2930step2Labels = (fun j => raw2930step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2930step1 raw2930step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2935 raw2935Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2935 raw2935Labels = mixedMoment B raw2935step0 raw2935step0Labels := by
      have hz : ∀ j, raw2935 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2935step0 = (fun i j => raw2935 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2935step0 raw2935; decide +kernel
      have hl : raw2935step0Labels = raw2935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2935 raw2935Labels permutation520 hz
    mixedMoment B raw2935step0 raw2935step0Labels = mixedMoment B raw2935step1 raw2935step1Labels := by
      have hz : ∀ j, raw2935step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2935step1 = (fun i j => raw2935step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2935step1 raw2935step0; decide +kernel
      have hl : raw2935step1Labels = raw2935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2935step0 raw2935step0Labels permutation104 hz
    mixedMoment B raw2935step1 raw2935step1Labels = mixedMoment B raw2935step2 raw2935step2Labels := by
      have hz : ∀ j, raw2935step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2935step2 = (fun i j => raw2935step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2935step2 raw2935step1; decide +kernel
      have hl : raw2935step2Labels = raw2935step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2935step1 raw2935step1Labels permutation20 hz
    mixedMoment B raw2935step2 raw2935step2Labels = mixedMoment B raw2935step3 raw2935step3Labels := by
      have hz : ∀ i, raw2935step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2935step3 = (fun i j => raw2935step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2935step3 raw2935step2; decide +kernel
      have hl : raw2935step3Labels = (fun j => raw2935step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2935step2 raw2935step2Labels permutation6 hz
    mixedMoment B raw2935step3 raw2935step3Labels = mixedMoment B raw2935step4 raw2935step4Labels := by
      have ha : raw2935step4 = (fun i j => raw2935step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2935step4 raw2935step3; decide +kernel
      have hl : raw2935step4Labels = raw2935step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2935step3 raw2935step3Labels permutation7 permutation0
    mixedMoment B raw2935step4 raw2935step4Labels = mixedMoment B raw2935step5 raw2935step5Labels := by
      have ha : raw2935step5 = -raw2935step4 := by apply Matrix.ext; change ∀ i j, raw2935step5 i j = -(raw2935step4 i j); unfold raw2935step5 raw2935step4; decide +kernel
      have hl : raw2935step5Labels = raw2935step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical40559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40559 raw40559Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw40559 raw40559Labels = mixedMoment B raw40559step0 raw40559step0Labels := by
      have hz : ∀ j, raw40559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40559step0 = (fun i j => raw40559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40559step0 raw40559; decide +kernel
      have hl : raw40559step0Labels = raw40559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40559 raw40559Labels permutation346 hz
    mixedMoment B raw40559step0 raw40559step0Labels = mixedMoment B raw40559step1 raw40559step1Labels := by
      have ha : raw40559step1 = (fun i j => raw40559step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40559step1 raw40559step0; decide +kernel
      have hl : raw40559step1Labels = raw40559step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40559step0 raw40559step0Labels permutation32 permutation3
    _ = mixedMoment B node3535 node3535Labels := by rfl

theorem canonical40560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40560 raw40560Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw40560 raw40560Labels = mixedMoment B raw40560step0 raw40560step0Labels := by
      have hz : ∀ j, raw40560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40560step0 = (fun i j => raw40560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40560step0 raw40560; decide +kernel
      have hl : raw40560step0Labels = raw40560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40560 raw40560Labels permutation346 hz
    mixedMoment B raw40560step0 raw40560step0Labels = mixedMoment B raw40560step1 raw40560step1Labels := by
      have ha : raw40560step1 = (fun i j => raw40560step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40560step1 raw40560step0; decide +kernel
      have hl : raw40560step1Labels = raw40560step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40560step0 raw40560step0Labels permutation32 permutation3
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical40561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40561 raw40561Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw40561 raw40561Labels = mixedMoment B raw40561step0 raw40561step0Labels := by
      have ha : raw40561step0 = (fun i j => raw40561 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40561step0 raw40561; decide +kernel
      have hl : raw40561step0Labels = raw40561Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40561 raw40561Labels permutation152 permutation3
    _ = mixedMoment B node3525 node3525Labels := by rfl

theorem canonical40562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40562 raw40562Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw40562 raw40562Labels = mixedMoment B raw40562step0 raw40562step0Labels := by
      have ha : raw40562step0 = (fun i j => raw40562 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40562step0 raw40562; decide +kernel
      have hl : raw40562step0Labels = raw40562Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40562 raw40562Labels permutation152 permutation3
    _ = mixedMoment B node3526 node3526Labels := by rfl

theorem canonical40563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40563 raw40563Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw40563 raw40563Labels = mixedMoment B raw40563step0 raw40563step0Labels := by
      have hz : ∀ j, raw40563 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40563step0 = (fun i j => raw40563 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40563step0 raw40563; decide +kernel
      have hl : raw40563step0Labels = raw40563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40563 raw40563Labels permutation520 hz
    mixedMoment B raw40563step0 raw40563step0Labels = mixedMoment B raw40563step1 raw40563step1Labels := by
      have hz : ∀ j, raw40563step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40563step1 = (fun i j => raw40563step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40563step1 raw40563step0; decide +kernel
      have hl : raw40563step1Labels = raw40563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40563step0 raw40563step0Labels permutation104 hz
    mixedMoment B raw40563step1 raw40563step1Labels = mixedMoment B raw40563step2 raw40563step2Labels := by
      have hz : ∀ j, raw40563step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40563step2 = (fun i j => raw40563step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40563step2 raw40563step1; decide +kernel
      have hl : raw40563step2Labels = raw40563step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40563step1 raw40563step1Labels permutation20 hz
    mixedMoment B raw40563step2 raw40563step2Labels = mixedMoment B raw40563step3 raw40563step3Labels := by
      have ha : raw40563step3 = (fun i j => raw40563step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40563step3 raw40563step2; decide +kernel
      have hl : raw40563step3Labels = raw40563step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40563step2 raw40563step2Labels permutation7 permutation3
    mixedMoment B raw40563step3 raw40563step3Labels = mixedMoment B raw40563step4 raw40563step4Labels := by
      have ha : raw40563step4 = -raw40563step3 := by apply Matrix.ext; change ∀ i j, raw40563step4 i j = -(raw40563step3 i j); unfold raw40563step4 raw40563step3; decide +kernel
      have hl : raw40563step4Labels = raw40563step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2783 node2783Labels := by rfl

theorem canonical40564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40564 raw40564Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw40564 raw40564Labels = mixedMoment B raw40564step0 raw40564step0Labels := by
      have hz : ∀ j, raw40564 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40564step0 = (fun i j => raw40564 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40564step0 raw40564; decide +kernel
      have hl : raw40564step0Labels = raw40564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40564 raw40564Labels permutation434 hz
    mixedMoment B raw40564step0 raw40564step0Labels = mixedMoment B raw40564step1 raw40564step1Labels := by
      have hz : ∀ j, raw40564step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40564step1 = (fun i j => raw40564step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40564step1 raw40564step0; decide +kernel
      have hl : raw40564step1Labels = raw40564step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40564step0 raw40564step0Labels permutation80 hz
    mixedMoment B raw40564step1 raw40564step1Labels = mixedMoment B raw40564step2 raw40564step2Labels := by
      have ha : raw40564step2 = (fun i j => raw40564step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40564step2 raw40564step1; decide +kernel
      have hl : raw40564step2Labels = raw40564step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40564step1 raw40564step1Labels permutation31 permutation3
    mixedMoment B raw40564step2 raw40564step2Labels = mixedMoment B raw40564step3 raw40564step3Labels := by
      have ha : raw40564step3 = -raw40564step2 := by apply Matrix.ext; change ∀ i j, raw40564step3 i j = -(raw40564step2 i j); unfold raw40564step3 raw40564step2; decide +kernel
      have hl : raw40564step3Labels = raw40564step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3098 node3098Labels := by rfl

theorem canonical40565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40565 raw40565Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw40565 raw40565Labels = mixedMoment B raw40565step0 raw40565step0Labels := by
      have hz : ∀ j, raw40565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40565step0 = (fun i j => raw40565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40565step0 raw40565; decide +kernel
      have hl : raw40565step0Labels = raw40565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40565 raw40565Labels permutation434 hz
    mixedMoment B raw40565step0 raw40565step0Labels = mixedMoment B raw40565step1 raw40565step1Labels := by
      have hz : ∀ j, raw40565step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40565step1 = (fun i j => raw40565step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40565step1 raw40565step0; decide +kernel
      have hl : raw40565step1Labels = raw40565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40565step0 raw40565step0Labels permutation80 hz
    mixedMoment B raw40565step1 raw40565step1Labels = mixedMoment B raw40565step2 raw40565step2Labels := by
      have ha : raw40565step2 = (fun i j => raw40565step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40565step2 raw40565step1; decide +kernel
      have hl : raw40565step2Labels = raw40565step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40565step1 raw40565step1Labels permutation8 permutation3
    _ = mixedMoment B node3583 node3583Labels := by rfl

theorem canonical40566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40566 raw40566Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw40566 raw40566Labels = mixedMoment B raw40566step0 raw40566step0Labels := by
      have hz : ∀ j, raw40566 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40566step0 = (fun i j => raw40566 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40566step0 raw40566; decide +kernel
      have hl : raw40566step0Labels = raw40566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40566 raw40566Labels permutation434 hz
    mixedMoment B raw40566step0 raw40566step0Labels = mixedMoment B raw40566step1 raw40566step1Labels := by
      have hz : ∀ j, raw40566step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40566step1 = (fun i j => raw40566step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40566step1 raw40566step0; decide +kernel
      have hl : raw40566step1Labels = raw40566step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40566step0 raw40566step0Labels permutation80 hz
    mixedMoment B raw40566step1 raw40566step1Labels = mixedMoment B raw40566step2 raw40566step2Labels := by
      have ha : raw40566step2 = (fun i j => raw40566step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40566step2 raw40566step1; decide +kernel
      have hl : raw40566step2Labels = raw40566step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40566step1 raw40566step1Labels permutation8 permutation3
    _ = mixedMoment B node3584 node3584Labels := by rfl

theorem canonical40567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40567 raw40567Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw40567 raw40567Labels = mixedMoment B raw40567step0 raw40567step0Labels := by
      have hz : ∀ j, raw40567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40567step0 = (fun i j => raw40567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40567step0 raw40567; decide +kernel
      have hl : raw40567step0Labels = raw40567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40567 raw40567Labels permutation346 hz
    mixedMoment B raw40567step0 raw40567step0Labels = mixedMoment B raw40567step1 raw40567step1Labels := by
      have ha : raw40567step1 = (fun i j => raw40567step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40567step1 raw40567step0; decide +kernel
      have hl : raw40567step1Labels = raw40567step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40567step0 raw40567step0Labels permutation32 permutation3
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical40568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40568 raw40568Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw40568 raw40568Labels = mixedMoment B raw40568step0 raw40568step0Labels := by
      have hz : ∀ j, raw40568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40568step0 = (fun i j => raw40568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40568step0 raw40568; decide +kernel
      have hl : raw40568step0Labels = raw40568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40568 raw40568Labels permutation346 hz
    mixedMoment B raw40568step0 raw40568step0Labels = mixedMoment B raw40568step1 raw40568step1Labels := by
      have ha : raw40568step1 = (fun i j => raw40568step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40568step1 raw40568step0; decide +kernel
      have hl : raw40568step1Labels = raw40568step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40568step0 raw40568step0Labels permutation32 permutation3
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical40569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40569 raw40569Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw40569 raw40569Labels = mixedMoment B raw40569step0 raw40569step0Labels := by
      have hz : ∀ j, raw40569 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40569step0 = (fun i j => raw40569 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40569step0 raw40569; decide +kernel
      have hl : raw40569step0Labels = raw40569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40569 raw40569Labels permutation520 hz
    mixedMoment B raw40569step0 raw40569step0Labels = mixedMoment B raw40569step1 raw40569step1Labels := by
      have hz : ∀ j, raw40569step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40569step1 = (fun i j => raw40569step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40569step1 raw40569step0; decide +kernel
      have hl : raw40569step1Labels = raw40569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40569step0 raw40569step0Labels permutation104 hz
    mixedMoment B raw40569step1 raw40569step1Labels = mixedMoment B raw40569step2 raw40569step2Labels := by
      have hz : ∀ j, raw40569step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40569step2 = (fun i j => raw40569step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40569step2 raw40569step1; decide +kernel
      have hl : raw40569step2Labels = raw40569step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40569step1 raw40569step1Labels permutation20 hz
    mixedMoment B raw40569step2 raw40569step2Labels = mixedMoment B raw40569step3 raw40569step3Labels := by
      have ha : raw40569step3 = (fun i j => raw40569step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40569step3 raw40569step2; decide +kernel
      have hl : raw40569step3Labels = raw40569step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40569step2 raw40569step2Labels permutation4 permutation6
    mixedMoment B raw40569step3 raw40569step3Labels = mixedMoment B raw40569step4 raw40569step4Labels := by
      have ha : raw40569step4 = -raw40569step3 := by apply Matrix.ext; change ∀ i j, raw40569step4 i j = -(raw40569step3 i j); unfold raw40569step4 raw40569step3; decide +kernel
      have hl : raw40569step4Labels = raw40569step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2789 node2789Labels := by rfl

theorem canonical40570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40570 raw40570Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw40570 raw40570Labels = mixedMoment B raw40570step0 raw40570step0Labels := by
      have hz : ∀ j, raw40570 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40570step0 = (fun i j => raw40570 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40570step0 raw40570; decide +kernel
      have hl : raw40570step0Labels = raw40570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40570 raw40570Labels permutation434 hz
    mixedMoment B raw40570step0 raw40570step0Labels = mixedMoment B raw40570step1 raw40570step1Labels := by
      have hz : ∀ j, raw40570step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40570step1 = (fun i j => raw40570step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40570step1 raw40570step0; decide +kernel
      have hl : raw40570step1Labels = raw40570step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40570step0 raw40570step0Labels permutation80 hz
    mixedMoment B raw40570step1 raw40570step1Labels = mixedMoment B raw40570step2 raw40570step2Labels := by
      have ha : raw40570step2 = (fun i j => raw40570step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40570step2 raw40570step1; decide +kernel
      have hl : raw40570step2Labels = raw40570step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40570step1 raw40570step1Labels permutation16 permutation6
    mixedMoment B raw40570step2 raw40570step2Labels = mixedMoment B raw40570step3 raw40570step3Labels := by
      have ha : raw40570step3 = -raw40570step2 := by apply Matrix.ext; change ∀ i j, raw40570step3 i j = -(raw40570step2 i j); unfold raw40570step3 raw40570step2; decide +kernel
      have hl : raw40570step3Labels = raw40570step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2744 node2744Labels := by rfl

theorem canonical40571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40571 raw40571Labels = mixedMoment B node3636 node3636Labels := by
  calc
    mixedMoment B raw40571 raw40571Labels = mixedMoment B raw40571step0 raw40571step0Labels := by
      have hz : ∀ j, raw40571 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40571step0 = (fun i j => raw40571 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40571step0 raw40571; decide +kernel
      have hl : raw40571step0Labels = raw40571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40571 raw40571Labels permutation520 hz
    mixedMoment B raw40571step0 raw40571step0Labels = mixedMoment B raw40571step1 raw40571step1Labels := by
      have hz : ∀ j, raw40571step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40571step1 = (fun i j => raw40571step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40571step1 raw40571step0; decide +kernel
      have hl : raw40571step1Labels = raw40571step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40571step0 raw40571step0Labels permutation104 hz
    mixedMoment B raw40571step1 raw40571step1Labels = mixedMoment B raw40571step2 raw40571step2Labels := by
      have hz : ∀ j, raw40571step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40571step2 = (fun i j => raw40571step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40571step2 raw40571step1; decide +kernel
      have hl : raw40571step2Labels = raw40571step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40571step1 raw40571step1Labels permutation20 hz
    mixedMoment B raw40571step2 raw40571step2Labels = mixedMoment B raw40571step3 raw40571step3Labels := by
      have hz : ∀ j, raw40571step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw40571step3 = (fun i j => raw40571step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw40571step3 raw40571step2; decide +kernel
      have hl : raw40571step3Labels = raw40571step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40571step2 raw40571step2Labels permutation4 hz
    mixedMoment B raw40571step3 raw40571step3Labels = mixedMoment B raw40571step4 raw40571step4Labels := by
      have ha : raw40571step4 = (fun i j => raw40571step3 (permutation0 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40571step4 raw40571step3; decide +kernel
      have hl : raw40571step4Labels = raw40571step3Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40571step3 raw40571step3Labels permutation0 permutation3
    _ = mixedMoment B node3636 node3636Labels := by rfl

theorem canonical40572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40572 raw40572Labels = mixedMoment B node3629 node3629Labels := by
  calc
    mixedMoment B raw40572 raw40572Labels = mixedMoment B raw40572step0 raw40572step0Labels := by
      have hz : ∀ j, raw40572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40572step0 = (fun i j => raw40572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40572step0 raw40572; decide +kernel
      have hl : raw40572step0Labels = raw40572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40572 raw40572Labels permutation434 hz
    mixedMoment B raw40572step0 raw40572step0Labels = mixedMoment B raw40572step1 raw40572step1Labels := by
      have hz : ∀ j, raw40572step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40572step1 = (fun i j => raw40572step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40572step1 raw40572step0; decide +kernel
      have hl : raw40572step1Labels = raw40572step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40572step0 raw40572step0Labels permutation80 hz
    mixedMoment B raw40572step1 raw40572step1Labels = mixedMoment B raw40572step2 raw40572step2Labels := by
      have hz : ∀ j, raw40572step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40572step2 = (fun i j => raw40572step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40572step2 raw40572step1; decide +kernel
      have hl : raw40572step2Labels = raw40572step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40572step1 raw40572step1Labels permutation14 hz
    mixedMoment B raw40572step2 raw40572step2Labels = mixedMoment B raw40572step3 raw40572step3Labels := by
      have ha : raw40572step3 = (fun i j => raw40572step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40572step3 raw40572step2; decide +kernel
      have hl : raw40572step3Labels = raw40572step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40572step2 raw40572step2Labels permutation2 permutation3
    _ = mixedMoment B node3629 node3629Labels := by rfl

theorem canonical40573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40573 raw40573Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw40573 raw40573Labels = mixedMoment B raw40573step0 raw40573step0Labels := by
      have hz : ∀ j, raw40573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40573step0 = (fun i j => raw40573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40573step0 raw40573; decide +kernel
      have hl : raw40573step0Labels = raw40573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40573 raw40573Labels permutation434 hz
    mixedMoment B raw40573step0 raw40573step0Labels = mixedMoment B raw40573step1 raw40573step1Labels := by
      have hz : ∀ j, raw40573step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40573step1 = (fun i j => raw40573step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40573step1 raw40573step0; decide +kernel
      have hl : raw40573step1Labels = raw40573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40573step0 raw40573step0Labels permutation80 hz
    mixedMoment B raw40573step1 raw40573step1Labels = mixedMoment B raw40573step2 raw40573step2Labels := by
      have hz : ∀ j, raw40573step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40573step2 = (fun i j => raw40573step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40573step2 raw40573step1; decide +kernel
      have hl : raw40573step2Labels = raw40573step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40573step1 raw40573step1Labels permutation14 hz
    mixedMoment B raw40573step2 raw40573step2Labels = mixedMoment B raw40573step3 raw40573step3Labels := by
      have ha : raw40573step3 = (fun i j => raw40573step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40573step3 raw40573step2; decide +kernel
      have hl : raw40573step3Labels = raw40573step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40573step2 raw40573step2Labels permutation2 permutation3
    _ = mixedMoment B node3633 node3633Labels := by rfl

theorem canonical40574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40574 raw40574Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw40574 raw40574Labels = mixedMoment B raw40574step0 raw40574step0Labels := by
      have hz : ∀ j, raw40574 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40574step0 = (fun i j => raw40574 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40574step0 raw40574; decide +kernel
      have hl : raw40574step0Labels = raw40574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40574 raw40574Labels permutation434 hz
    mixedMoment B raw40574step0 raw40574step0Labels = mixedMoment B raw40574step1 raw40574step1Labels := by
      have hz : ∀ j, raw40574step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40574step1 = (fun i j => raw40574step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40574step1 raw40574step0; decide +kernel
      have hl : raw40574step1Labels = raw40574step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40574step0 raw40574step0Labels permutation80 hz
    mixedMoment B raw40574step1 raw40574step1Labels = mixedMoment B raw40574step2 raw40574step2Labels := by
      have hz : ∀ j, raw40574step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40574step2 = (fun i j => raw40574step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40574step2 raw40574step1; decide +kernel
      have hl : raw40574step2Labels = raw40574step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40574step1 raw40574step1Labels permutation14 hz
    mixedMoment B raw40574step2 raw40574step2Labels = mixedMoment B raw40574step3 raw40574step3Labels := by
      have ha : raw40574step3 = (fun i j => raw40574step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40574step3 raw40574step2; decide +kernel
      have hl : raw40574step3Labels = raw40574step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40574step2 raw40574step2Labels permutation4 permutation6
    mixedMoment B raw40574step3 raw40574step3Labels = mixedMoment B raw40574step4 raw40574step4Labels := by
      have ha : raw40574step4 = -raw40574step3 := by apply Matrix.ext; change ∀ i j, raw40574step4 i j = -(raw40574step3 i j); unfold raw40574step4 raw40574step3; decide +kernel
      have hl : raw40574step4Labels = raw40574step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2294 node2294Labels := by rfl

theorem canonical40575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40575 raw40575Labels = mixedMoment B node3635 node3635Labels := by
  calc
    mixedMoment B raw40575 raw40575Labels = mixedMoment B raw40575step0 raw40575step0Labels := by
      have hz : ∀ j, raw40575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40575step0 = (fun i j => raw40575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40575step0 raw40575; decide +kernel
      have hl : raw40575step0Labels = raw40575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40575 raw40575Labels permutation434 hz
    mixedMoment B raw40575step0 raw40575step0Labels = mixedMoment B raw40575step1 raw40575step1Labels := by
      have hz : ∀ j, raw40575step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40575step1 = (fun i j => raw40575step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40575step1 raw40575step0; decide +kernel
      have hl : raw40575step1Labels = raw40575step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40575step0 raw40575step0Labels permutation80 hz
    mixedMoment B raw40575step1 raw40575step1Labels = mixedMoment B raw40575step2 raw40575step2Labels := by
      have hz : ∀ j, raw40575step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40575step2 = (fun i j => raw40575step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40575step2 raw40575step1; decide +kernel
      have hl : raw40575step2Labels = raw40575step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40575step1 raw40575step1Labels permutation14 hz
    mixedMoment B raw40575step2 raw40575step2Labels = mixedMoment B raw40575step3 raw40575step3Labels := by
      have ha : raw40575step3 = (fun i j => raw40575step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40575step3 raw40575step2; decide +kernel
      have hl : raw40575step3Labels = raw40575step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40575step2 raw40575step2Labels permutation2 permutation3
    _ = mixedMoment B node3635 node3635Labels := by rfl

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

theorem canonical40576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40576 raw40576Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw40576 raw40576Labels = mixedMoment B raw40576step0 raw40576step0Labels := by
      have hz : ∀ j, raw40576 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40576step0 = (fun i j => raw40576 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40576step0 raw40576; decide +kernel
      have hl : raw40576step0Labels = raw40576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40576 raw40576Labels permutation346 hz
    mixedMoment B raw40576step0 raw40576step0Labels = mixedMoment B raw40576step1 raw40576step1Labels := by
      have hz : ∀ j, raw40576step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40576step1 = (fun i j => raw40576step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40576step1 raw40576step0; decide +kernel
      have hl : raw40576step1Labels = raw40576step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40576step0 raw40576step0Labels permutation56 hz
    mixedMoment B raw40576step1 raw40576step1Labels = mixedMoment B raw40576step2 raw40576step2Labels := by
      have ha : raw40576step2 = (fun i j => raw40576step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40576step2 raw40576step1; decide +kernel
      have hl : raw40576step2Labels = raw40576step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40576step1 raw40576step1Labels permutation8 permutation3
    _ = mixedMoment B node3623 node3623Labels := by rfl

theorem canonical40577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40577 raw40577Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw40577 raw40577Labels = mixedMoment B raw40577step0 raw40577step0Labels := by
      have hz : ∀ j, raw40577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40577step0 = (fun i j => raw40577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40577step0 raw40577; decide +kernel
      have hl : raw40577step0Labels = raw40577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40577 raw40577Labels permutation346 hz
    mixedMoment B raw40577step0 raw40577step0Labels = mixedMoment B raw40577step1 raw40577step1Labels := by
      have hz : ∀ j, raw40577step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40577step1 = (fun i j => raw40577step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40577step1 raw40577step0; decide +kernel
      have hl : raw40577step1Labels = raw40577step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40577step0 raw40577step0Labels permutation56 hz
    mixedMoment B raw40577step1 raw40577step1Labels = mixedMoment B raw40577step2 raw40577step2Labels := by
      have ha : raw40577step2 = (fun i j => raw40577step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40577step2 raw40577step1; decide +kernel
      have hl : raw40577step2Labels = raw40577step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40577step1 raw40577step1Labels permutation8 permutation3
    _ = mixedMoment B node3626 node3626Labels := by rfl

theorem canonical40578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40578 raw40578Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw40578 raw40578Labels = mixedMoment B raw40578step0 raw40578step0Labels := by
      have hz : ∀ j, raw40578 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40578step0 = (fun i j => raw40578 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40578step0 raw40578; decide +kernel
      have hl : raw40578step0Labels = raw40578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40578 raw40578Labels permutation346 hz
    mixedMoment B raw40578step0 raw40578step0Labels = mixedMoment B raw40578step1 raw40578step1Labels := by
      have hz : ∀ j, raw40578step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40578step1 = (fun i j => raw40578step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40578step1 raw40578step0; decide +kernel
      have hl : raw40578step1Labels = raw40578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40578step0 raw40578step0Labels permutation56 hz
    mixedMoment B raw40578step1 raw40578step1Labels = mixedMoment B raw40578step2 raw40578step2Labels := by
      have ha : raw40578step2 = (fun i j => raw40578step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40578step2 raw40578step1; decide +kernel
      have hl : raw40578step2Labels = raw40578step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40578step1 raw40578step1Labels permutation8 permutation3
    _ = mixedMoment B node3627 node3627Labels := by rfl

theorem canonical40579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40579 raw40579Labels = mixedMoment B node3628 node3628Labels := by
  calc
    mixedMoment B raw40579 raw40579Labels = mixedMoment B raw40579step0 raw40579step0Labels := by
      have hz : ∀ j, raw40579 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40579step0 = (fun i j => raw40579 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40579step0 raw40579; decide +kernel
      have hl : raw40579step0Labels = raw40579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40579 raw40579Labels permutation346 hz
    mixedMoment B raw40579step0 raw40579step0Labels = mixedMoment B raw40579step1 raw40579step1Labels := by
      have hz : ∀ j, raw40579step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40579step1 = (fun i j => raw40579step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40579step1 raw40579step0; decide +kernel
      have hl : raw40579step1Labels = raw40579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40579step0 raw40579step0Labels permutation56 hz
    mixedMoment B raw40579step1 raw40579step1Labels = mixedMoment B raw40579step2 raw40579step2Labels := by
      have ha : raw40579step2 = (fun i j => raw40579step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40579step2 raw40579step1; decide +kernel
      have hl : raw40579step2Labels = raw40579step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40579step1 raw40579step1Labels permutation8 permutation3
    _ = mixedMoment B node3628 node3628Labels := by rfl

theorem canonical40580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40580 raw40580Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw40580 raw40580Labels = mixedMoment B raw40580step0 raw40580step0Labels := by
      have hz : ∀ j, raw40580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40580step0 = (fun i j => raw40580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40580step0 raw40580; decide +kernel
      have hl : raw40580step0Labels = raw40580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40580 raw40580Labels permutation346 hz
    mixedMoment B raw40580step0 raw40580step0Labels = mixedMoment B raw40580step1 raw40580step1Labels := by
      have hz : ∀ j, raw40580step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40580step1 = (fun i j => raw40580step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40580step1 raw40580step0; decide +kernel
      have hl : raw40580step1Labels = raw40580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40580step0 raw40580step0Labels permutation56 hz
    mixedMoment B raw40580step1 raw40580step1Labels = mixedMoment B raw40580step2 raw40580step2Labels := by
      have ha : raw40580step2 = (fun i j => raw40580step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40580step2 raw40580step1; decide +kernel
      have hl : raw40580step2Labels = raw40580step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40580step1 raw40580step1Labels permutation8 permutation3
    _ = mixedMoment B node3632 node3632Labels := by rfl

theorem canonical40581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40581 raw40581Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw40581 raw40581Labels = mixedMoment B raw40581step0 raw40581step0Labels := by
      have hz : ∀ j, raw40581 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40581step0 = (fun i j => raw40581 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40581step0 raw40581; decide +kernel
      have hl : raw40581step0Labels = raw40581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40581 raw40581Labels permutation265 hz
    mixedMoment B raw40581step0 raw40581step0Labels = mixedMoment B raw40581step1 raw40581step1Labels := by
      have ha : raw40581step1 = (fun i j => raw40581step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40581step1 raw40581step0; decide +kernel
      have hl : raw40581step1Labels = raw40581step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40581step0 raw40581step0Labels permutation32 permutation3
    _ = mixedMoment B node3619 node3619Labels := by rfl

theorem canonical40582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40582 raw40582Labels = mixedMoment B node3622 node3622Labels := by
  calc
    mixedMoment B raw40582 raw40582Labels = mixedMoment B raw40582step0 raw40582step0Labels := by
      have hz : ∀ j, raw40582 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40582step0 = (fun i j => raw40582 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40582step0 raw40582; decide +kernel
      have hl : raw40582step0Labels = raw40582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40582 raw40582Labels permutation265 hz
    mixedMoment B raw40582step0 raw40582step0Labels = mixedMoment B raw40582step1 raw40582step1Labels := by
      have ha : raw40582step1 = (fun i j => raw40582step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40582step1 raw40582step0; decide +kernel
      have hl : raw40582step1Labels = raw40582step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40582step0 raw40582step0Labels permutation32 permutation3
    _ = mixedMoment B node3622 node3622Labels := by rfl

theorem canonical40583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40583 raw40583Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw40583 raw40583Labels = mixedMoment B raw40583step0 raw40583step0Labels := by
      have hz : ∀ j, raw40583 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40583step0 = (fun i j => raw40583 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40583step0 raw40583; decide +kernel
      have hl : raw40583step0Labels = raw40583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40583 raw40583Labels permutation265 hz
    mixedMoment B raw40583step0 raw40583step0Labels = mixedMoment B raw40583step1 raw40583step1Labels := by
      have ha : raw40583step1 = (fun i j => raw40583step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40583step1 raw40583step0; decide +kernel
      have hl : raw40583step1Labels = raw40583step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40583step0 raw40583step0Labels permutation32 permutation3
    _ = mixedMoment B node3625 node3625Labels := by rfl

theorem canonical40584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40584 raw40584Labels = mixedMoment B node3618 node3618Labels := by
  calc
    mixedMoment B raw40584 raw40584Labels = mixedMoment B raw40584step0 raw40584step0Labels := by
      have ha : raw40584step0 = (fun i j => raw40584 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40584step0 raw40584; decide +kernel
      have hl : raw40584step0Labels = raw40584Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40584 raw40584Labels permutation152 permutation3
    _ = mixedMoment B node3618 node3618Labels := by rfl

theorem canonical40585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40585 raw40585Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw40585 raw40585Labels = mixedMoment B raw40585step0 raw40585step0Labels := by
      have hz : ∀ j, raw40585 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40585step0 = (fun i j => raw40585 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40585step0 raw40585; decide +kernel
      have hl : raw40585step0Labels = raw40585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40585 raw40585Labels permutation434 hz
    mixedMoment B raw40585step0 raw40585step0Labels = mixedMoment B raw40585step1 raw40585step1Labels := by
      have hz : ∀ j, raw40585step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40585step1 = (fun i j => raw40585step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40585step1 raw40585step0; decide +kernel
      have hl : raw40585step1Labels = raw40585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40585step0 raw40585step0Labels permutation80 hz
    mixedMoment B raw40585step1 raw40585step1Labels = mixedMoment B raw40585step2 raw40585step2Labels := by
      have ha : raw40585step2 = (fun i j => raw40585step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40585step2 raw40585step1; decide +kernel
      have hl : raw40585step2Labels = raw40585step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40585step1 raw40585step1Labels permutation31 permutation3
    mixedMoment B raw40585step2 raw40585step2Labels = mixedMoment B raw40585step3 raw40585step3Labels := by
      have ha : raw40585step3 = -raw40585step2 := by apply Matrix.ext; change ∀ i j, raw40585step3 i j = -(raw40585step2 i j); unfold raw40585step3 raw40585step2; decide +kernel
      have hl : raw40585step3Labels = raw40585step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2742 node2742Labels := by rfl

theorem canonical40586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40586 raw40586Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw40586 raw40586Labels = mixedMoment B raw40586step0 raw40586step0Labels := by
      have hz : ∀ j, raw40586 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40586step0 = (fun i j => raw40586 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40586step0 raw40586; decide +kernel
      have hl : raw40586step0Labels = raw40586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40586 raw40586Labels permutation434 hz
    mixedMoment B raw40586step0 raw40586step0Labels = mixedMoment B raw40586step1 raw40586step1Labels := by
      have hz : ∀ j, raw40586step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40586step1 = (fun i j => raw40586step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40586step1 raw40586step0; decide +kernel
      have hl : raw40586step1Labels = raw40586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40586step0 raw40586step0Labels permutation80 hz
    mixedMoment B raw40586step1 raw40586step1Labels = mixedMoment B raw40586step2 raw40586step2Labels := by
      have ha : raw40586step2 = (fun i j => raw40586step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40586step2 raw40586step1; decide +kernel
      have hl : raw40586step2Labels = raw40586step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40586step1 raw40586step1Labels permutation31 permutation3
    mixedMoment B raw40586step2 raw40586step2Labels = mixedMoment B raw40586step3 raw40586step3Labels := by
      have ha : raw40586step3 = -raw40586step2 := by apply Matrix.ext; change ∀ i j, raw40586step3 i j = -(raw40586step2 i j); unfold raw40586step3 raw40586step2; decide +kernel
      have hl : raw40586step3Labels = raw40586step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical40587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40587 raw40587Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw40587 raw40587Labels = mixedMoment B raw40587step0 raw40587step0Labels := by
      have hz : ∀ j, raw40587 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40587step0 = (fun i j => raw40587 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40587step0 raw40587; decide +kernel
      have hl : raw40587step0Labels = raw40587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40587 raw40587Labels permutation434 hz
    mixedMoment B raw40587step0 raw40587step0Labels = mixedMoment B raw40587step1 raw40587step1Labels := by
      have hz : ∀ j, raw40587step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40587step1 = (fun i j => raw40587step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40587step1 raw40587step0; decide +kernel
      have hl : raw40587step1Labels = raw40587step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40587step0 raw40587step0Labels permutation80 hz
    mixedMoment B raw40587step1 raw40587step1Labels = mixedMoment B raw40587step2 raw40587step2Labels := by
      have ha : raw40587step2 = (fun i j => raw40587step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40587step2 raw40587step1; decide +kernel
      have hl : raw40587step2Labels = raw40587step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40587step1 raw40587step1Labels permutation8 permutation3
    _ = mixedMoment B node3817 node3817Labels := by rfl

theorem canonical40588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40588 raw40588Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw40588 raw40588Labels = mixedMoment B raw40588step0 raw40588step0Labels := by
      have hz : ∀ j, raw40588 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40588step0 = (fun i j => raw40588 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40588step0 raw40588; decide +kernel
      have hl : raw40588step0Labels = raw40588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40588 raw40588Labels permutation434 hz
    mixedMoment B raw40588step0 raw40588step0Labels = mixedMoment B raw40588step1 raw40588step1Labels := by
      have hz : ∀ j, raw40588step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40588step1 = (fun i j => raw40588step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40588step1 raw40588step0; decide +kernel
      have hl : raw40588step1Labels = raw40588step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40588step0 raw40588step0Labels permutation80 hz
    mixedMoment B raw40588step1 raw40588step1Labels = mixedMoment B raw40588step2 raw40588step2Labels := by
      have ha : raw40588step2 = (fun i j => raw40588step1 (permutation22 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40588step2 raw40588step1; decide +kernel
      have hl : raw40588step2Labels = raw40588step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40588step1 raw40588step1Labels permutation22 permutation6
    mixedMoment B raw40588step2 raw40588step2Labels = mixedMoment B raw40588step3 raw40588step3Labels := by
      have ha : raw40588step3 = -raw40588step2 := by apply Matrix.ext; change ∀ i j, raw40588step3 i j = -(raw40588step2 i j); unfold raw40588step3 raw40588step2; decide +kernel
      have hl : raw40588step3Labels = raw40588step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3626 node3626Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1120 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1120) =
      Integer.Sparse.eval keyMomentRow1120 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1120).leftCharge (GramAssembly.key 1120).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3535) := by
    have ha : gramCharges (GramAssembly.key 1120).leftCharge (GramAssembly.key 1120).rightCharge = raw40559 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40559Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40559 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1120).leftCharge (GramAssembly.key 1120).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1120, Integer.Sparse.eval]

theorem keyMoment1121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1121) =
      Integer.Sparse.eval keyMomentRow1121 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1121).leftCharge (GramAssembly.key 1121).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3541) := by
    have ha : gramCharges (GramAssembly.key 1121).leftCharge (GramAssembly.key 1121).rightCharge = raw40560 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40560Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40560 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1121).leftCharge (GramAssembly.key 1121).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1121, Integer.Sparse.eval]

theorem keyMoment1122 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1122) =
      Integer.Sparse.eval keyMomentRow1122 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1122).leftCharge (GramAssembly.key 1122).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3525) := by
    have ha : gramCharges (GramAssembly.key 1122).leftCharge (GramAssembly.key 1122).rightCharge = raw40561 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40561Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40561 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1122).leftCharge (GramAssembly.key 1122).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1122, Integer.Sparse.eval]

theorem keyMoment1123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1123) =
      Integer.Sparse.eval keyMomentRow1123 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1123).leftCharge (GramAssembly.key 1123).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3526) := by
    have ha : gramCharges (GramAssembly.key 1123).leftCharge (GramAssembly.key 1123).rightCharge = raw40562 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40562Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40562 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1123).leftCharge (GramAssembly.key 1123).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1123, Integer.Sparse.eval]

theorem keyMoment1124 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1124) =
      Integer.Sparse.eval keyMomentRow1124 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1124).leftCharge (GramAssembly.key 1124).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2783) := by
    have ha : gramCharges (GramAssembly.key 1124).leftCharge (GramAssembly.key 1124).rightCharge = raw40563 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40563Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40563 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1124).leftCharge (GramAssembly.key 1124).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1124, Integer.Sparse.eval]

theorem keyMoment1125 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1125) =
      Integer.Sparse.eval keyMomentRow1125 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1125).leftCharge (GramAssembly.key 1125).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3098) := by
    have ha : gramCharges (GramAssembly.key 1125).leftCharge (GramAssembly.key 1125).rightCharge = raw40564 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40564Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40564 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1125).leftCharge (GramAssembly.key 1125).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1125, Integer.Sparse.eval]

theorem keyMoment1126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1126) =
      Integer.Sparse.eval keyMomentRow1126 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1126).leftCharge (GramAssembly.key 1126).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3583) := by
    have ha : gramCharges (GramAssembly.key 1126).leftCharge (GramAssembly.key 1126).rightCharge = raw40565 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40565Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40565 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1126).leftCharge (GramAssembly.key 1126).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1126, Integer.Sparse.eval]

theorem keyMoment1127 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1127) =
      Integer.Sparse.eval keyMomentRow1127 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1127).leftCharge (GramAssembly.key 1127).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3584) := by
    have ha : gramCharges (GramAssembly.key 1127).leftCharge (GramAssembly.key 1127).rightCharge = raw40566 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40566Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40566 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1127).leftCharge (GramAssembly.key 1127).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1127, Integer.Sparse.eval]

theorem keyMoment1128 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1128) =
      Integer.Sparse.eval keyMomentRow1128 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1128).leftCharge (GramAssembly.key 1128).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3572) := by
    have ha : gramCharges (GramAssembly.key 1128).leftCharge (GramAssembly.key 1128).rightCharge = raw40567 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40567Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40567 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1128).leftCharge (GramAssembly.key 1128).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1128, Integer.Sparse.eval]

theorem keyMoment1129 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1129) =
      Integer.Sparse.eval keyMomentRow1129 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1129).leftCharge (GramAssembly.key 1129).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3573) := by
    have ha : gramCharges (GramAssembly.key 1129).leftCharge (GramAssembly.key 1129).rightCharge = raw40568 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40568Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40568 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1129).leftCharge (GramAssembly.key 1129).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1129, Integer.Sparse.eval]

theorem keyMoment1130 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1130) =
      Integer.Sparse.eval keyMomentRow1130 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1130).leftCharge (GramAssembly.key 1130).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2789) := by
    have ha : gramCharges (GramAssembly.key 1130).leftCharge (GramAssembly.key 1130).rightCharge = raw40569 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40569Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40569 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1130).leftCharge (GramAssembly.key 1130).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1130, Integer.Sparse.eval]

theorem keyMoment1131 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1131) =
      Integer.Sparse.eval keyMomentRow1131 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1131).leftCharge (GramAssembly.key 1131).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2744) := by
    have ha : gramCharges (GramAssembly.key 1131).leftCharge (GramAssembly.key 1131).rightCharge = raw40570 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40570Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40570 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1131).leftCharge (GramAssembly.key 1131).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1131, Integer.Sparse.eval]

theorem keyMoment1132 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1132) =
      Integer.Sparse.eval keyMomentRow1132 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1132).leftCharge (GramAssembly.key 1132).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3636) := by
    have ha : gramCharges (GramAssembly.key 1132).leftCharge (GramAssembly.key 1132).rightCharge = raw40571 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40571Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40571 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1132).leftCharge (GramAssembly.key 1132).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1132, Integer.Sparse.eval]

theorem keyMoment1133 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1133) =
      Integer.Sparse.eval keyMomentRow1133 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1133).leftCharge (GramAssembly.key 1133).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3629) := by
    have ha : gramCharges (GramAssembly.key 1133).leftCharge (GramAssembly.key 1133).rightCharge = raw40572 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40572Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40572 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1133).leftCharge (GramAssembly.key 1133).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1133, Integer.Sparse.eval]

theorem keyMoment1134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1134) =
      Integer.Sparse.eval keyMomentRow1134 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1134).leftCharge (GramAssembly.key 1134).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3633) := by
    have ha : gramCharges (GramAssembly.key 1134).leftCharge (GramAssembly.key 1134).rightCharge = raw40573 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40573Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40573 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1134).leftCharge (GramAssembly.key 1134).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1134, Integer.Sparse.eval]

theorem keyMoment1135 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1135) =
      Integer.Sparse.eval keyMomentRow1135 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1135).leftCharge (GramAssembly.key 1135).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2294) := by
    have ha : gramCharges (GramAssembly.key 1135).leftCharge (GramAssembly.key 1135).rightCharge = raw40574 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40574Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40574 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1135).leftCharge (GramAssembly.key 1135).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1135, Integer.Sparse.eval]

theorem keyMoment1136 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1136) =
      Integer.Sparse.eval keyMomentRow1136 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1136).leftCharge (GramAssembly.key 1136).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3635) := by
    have ha : gramCharges (GramAssembly.key 1136).leftCharge (GramAssembly.key 1136).rightCharge = raw40575 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40575Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40575 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1136).leftCharge (GramAssembly.key 1136).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1136, Integer.Sparse.eval]

theorem keyMoment1137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1137) =
      Integer.Sparse.eval keyMomentRow1137 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1137).leftCharge (GramAssembly.key 1137).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3623) := by
    have ha : gramCharges (GramAssembly.key 1137).leftCharge (GramAssembly.key 1137).rightCharge = raw40576 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40576Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40576 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1137).leftCharge (GramAssembly.key 1137).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1137, Integer.Sparse.eval]

theorem keyMoment1138 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1138) =
      Integer.Sparse.eval keyMomentRow1138 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1138).leftCharge (GramAssembly.key 1138).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3626) := by
    have ha : gramCharges (GramAssembly.key 1138).leftCharge (GramAssembly.key 1138).rightCharge = raw40577 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40577Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40577 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1138).leftCharge (GramAssembly.key 1138).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1138, Integer.Sparse.eval]

theorem keyMoment1139 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1139) =
      Integer.Sparse.eval keyMomentRow1139 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1139).leftCharge (GramAssembly.key 1139).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3627) := by
    have ha : gramCharges (GramAssembly.key 1139).leftCharge (GramAssembly.key 1139).rightCharge = raw40578 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40578Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40578 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1139).leftCharge (GramAssembly.key 1139).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1139, Integer.Sparse.eval]

theorem keyMoment1140 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1140) =
      Integer.Sparse.eval keyMomentRow1140 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1140).leftCharge (GramAssembly.key 1140).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3628) := by
    have ha : gramCharges (GramAssembly.key 1140).leftCharge (GramAssembly.key 1140).rightCharge = raw40579 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40579Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40579 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1140).leftCharge (GramAssembly.key 1140).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1140, Integer.Sparse.eval]

theorem keyMoment1141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1141) =
      Integer.Sparse.eval keyMomentRow1141 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1141).leftCharge (GramAssembly.key 1141).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3632) := by
    have ha : gramCharges (GramAssembly.key 1141).leftCharge (GramAssembly.key 1141).rightCharge = raw40580 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40580Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40580 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1141).leftCharge (GramAssembly.key 1141).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1141, Integer.Sparse.eval]

theorem keyMoment1142 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1142) =
      Integer.Sparse.eval keyMomentRow1142 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1142).leftCharge (GramAssembly.key 1142).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3619) := by
    have ha : gramCharges (GramAssembly.key 1142).leftCharge (GramAssembly.key 1142).rightCharge = raw40581 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40581Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40581 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1142).leftCharge (GramAssembly.key 1142).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1142, Integer.Sparse.eval]

theorem keyMoment1143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1143) =
      Integer.Sparse.eval keyMomentRow1143 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1143).leftCharge (GramAssembly.key 1143).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3622) := by
    have ha : gramCharges (GramAssembly.key 1143).leftCharge (GramAssembly.key 1143).rightCharge = raw40582 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40582Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40582 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1143).leftCharge (GramAssembly.key 1143).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1143, Integer.Sparse.eval]

theorem keyMoment1144 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1144) =
      Integer.Sparse.eval keyMomentRow1144 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1144).leftCharge (GramAssembly.key 1144).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3625) := by
    have ha : gramCharges (GramAssembly.key 1144).leftCharge (GramAssembly.key 1144).rightCharge = raw40583 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40583Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40583 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1144).leftCharge (GramAssembly.key 1144).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1144, Integer.Sparse.eval]

theorem keyMoment1145 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1145) =
      Integer.Sparse.eval keyMomentRow1145 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1145).leftCharge (GramAssembly.key 1145).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3618) := by
    have ha : gramCharges (GramAssembly.key 1145).leftCharge (GramAssembly.key 1145).rightCharge = raw40584 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40584Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40584 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1145).leftCharge (GramAssembly.key 1145).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1145, Integer.Sparse.eval]

theorem keyMoment1146 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1146) =
      Integer.Sparse.eval keyMomentRow1146 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1146).leftCharge (GramAssembly.key 1146).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4084) := by
    have ha : gramCharges (GramAssembly.key 1146).leftCharge (GramAssembly.key 1146).rightCharge = raw2935 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw2935Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical2935 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1146).leftCharge (GramAssembly.key 1146).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1146, Integer.Sparse.eval]

theorem keyMoment1147 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1147) =
      Integer.Sparse.eval keyMomentRow1147 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1147).leftCharge (GramAssembly.key 1147).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2742) := by
    have ha : gramCharges (GramAssembly.key 1147).leftCharge (GramAssembly.key 1147).rightCharge = raw40585 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40585Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40585 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1147).leftCharge (GramAssembly.key 1147).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1147, Integer.Sparse.eval]

theorem keyMoment1148 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1148) =
      Integer.Sparse.eval keyMomentRow1148 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1148).leftCharge (GramAssembly.key 1148).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3054) := by
    have ha : gramCharges (GramAssembly.key 1148).leftCharge (GramAssembly.key 1148).rightCharge = raw40586 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40586Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40586 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1148).leftCharge (GramAssembly.key 1148).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1148, Integer.Sparse.eval]

theorem keyMoment1149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1149) =
      Integer.Sparse.eval keyMomentRow1149 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1149).leftCharge (GramAssembly.key 1149).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4092) := by
    have ha : gramCharges (GramAssembly.key 1149).leftCharge (GramAssembly.key 1149).rightCharge = raw2930 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw2930Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical2930 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1149).leftCharge (GramAssembly.key 1149).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1149, Integer.Sparse.eval]

theorem keyMoment1150 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1150) =
      Integer.Sparse.eval keyMomentRow1150 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1150).leftCharge (GramAssembly.key 1150).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3817) := by
    have ha : gramCharges (GramAssembly.key 1150).leftCharge (GramAssembly.key 1150).rightCharge = raw40587 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40587Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40587 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1150).leftCharge (GramAssembly.key 1150).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1150, Integer.Sparse.eval]

theorem keyMoment1151 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1151) =
      Integer.Sparse.eval keyMomentRow1151 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1151).leftCharge (GramAssembly.key 1151).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3626) := by
    have ha : gramCharges (GramAssembly.key 1151).leftCharge (GramAssembly.key 1151).rightCharge = raw40588 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40588Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40588 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1151).leftCharge (GramAssembly.key 1151).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1151, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1120 : keyMomentRows (1120 : Fin 2886) =
    keyMomentRow1120 := by decide +kernel

theorem keyMomentRowsAt1121 : keyMomentRows (1121 : Fin 2886) =
    keyMomentRow1121 := by decide +kernel

theorem keyMomentRowsAt1122 : keyMomentRows (1122 : Fin 2886) =
    keyMomentRow1122 := by decide +kernel

theorem keyMomentRowsAt1123 : keyMomentRows (1123 : Fin 2886) =
    keyMomentRow1123 := by decide +kernel

theorem keyMomentRowsAt1124 : keyMomentRows (1124 : Fin 2886) =
    keyMomentRow1124 := by decide +kernel

theorem keyMomentRowsAt1125 : keyMomentRows (1125 : Fin 2886) =
    keyMomentRow1125 := by decide +kernel

theorem keyMomentRowsAt1126 : keyMomentRows (1126 : Fin 2886) =
    keyMomentRow1126 := by decide +kernel

theorem keyMomentRowsAt1127 : keyMomentRows (1127 : Fin 2886) =
    keyMomentRow1127 := by decide +kernel

theorem keyMomentRowsAt1128 : keyMomentRows (1128 : Fin 2886) =
    keyMomentRow1128 := by decide +kernel

theorem keyMomentRowsAt1129 : keyMomentRows (1129 : Fin 2886) =
    keyMomentRow1129 := by decide +kernel

theorem keyMomentRowsAt1130 : keyMomentRows (1130 : Fin 2886) =
    keyMomentRow1130 := by decide +kernel

theorem keyMomentRowsAt1131 : keyMomentRows (1131 : Fin 2886) =
    keyMomentRow1131 := by decide +kernel

theorem keyMomentRowsAt1132 : keyMomentRows (1132 : Fin 2886) =
    keyMomentRow1132 := by decide +kernel

theorem keyMomentRowsAt1133 : keyMomentRows (1133 : Fin 2886) =
    keyMomentRow1133 := by decide +kernel

theorem keyMomentRowsAt1134 : keyMomentRows (1134 : Fin 2886) =
    keyMomentRow1134 := by decide +kernel

theorem keyMomentRowsAt1135 : keyMomentRows (1135 : Fin 2886) =
    keyMomentRow1135 := by decide +kernel

theorem keyMomentRowsAt1136 : keyMomentRows (1136 : Fin 2886) =
    keyMomentRow1136 := by decide +kernel

theorem keyMomentRowsAt1137 : keyMomentRows (1137 : Fin 2886) =
    keyMomentRow1137 := by decide +kernel

theorem keyMomentRowsAt1138 : keyMomentRows (1138 : Fin 2886) =
    keyMomentRow1138 := by decide +kernel

theorem keyMomentRowsAt1139 : keyMomentRows (1139 : Fin 2886) =
    keyMomentRow1139 := by decide +kernel

theorem keyMomentRowsAt1140 : keyMomentRows (1140 : Fin 2886) =
    keyMomentRow1140 := by decide +kernel

theorem keyMomentRowsAt1141 : keyMomentRows (1141 : Fin 2886) =
    keyMomentRow1141 := by decide +kernel

theorem keyMomentRowsAt1142 : keyMomentRows (1142 : Fin 2886) =
    keyMomentRow1142 := by decide +kernel

theorem keyMomentRowsAt1143 : keyMomentRows (1143 : Fin 2886) =
    keyMomentRow1143 := by decide +kernel

theorem keyMomentRowsAt1144 : keyMomentRows (1144 : Fin 2886) =
    keyMomentRow1144 := by decide +kernel

theorem keyMomentRowsAt1145 : keyMomentRows (1145 : Fin 2886) =
    keyMomentRow1145 := by decide +kernel

theorem keyMomentRowsAt1146 : keyMomentRows (1146 : Fin 2886) =
    keyMomentRow1146 := by decide +kernel

theorem keyMomentRowsAt1147 : keyMomentRows (1147 : Fin 2886) =
    keyMomentRow1147 := by decide +kernel

theorem keyMomentRowsAt1148 : keyMomentRows (1148 : Fin 2886) =
    keyMomentRow1148 := by decide +kernel

theorem keyMomentRowsAt1149 : keyMomentRows (1149 : Fin 2886) =
    keyMomentRow1149 := by decide +kernel

theorem keyMomentRowsAt1150 : keyMomentRows (1150 : Fin 2886) =
    keyMomentRow1150 := by decide +kernel

theorem keyMomentRowsAt1151 : keyMomentRows (1151 : Fin 2886) =
    keyMomentRow1151 := by decide +kernel

theorem keyMomentChunkSound35_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 35) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1120 ∨ k.val = 1121 ∨ k.val = 1122 ∨ k.val = 1123 ∨ k.val = 1124 ∨ k.val = 1125 ∨ k.val = 1126 ∨ k.val = 1127 ∨ k.val = 1128 ∨ k.val = 1129 ∨ k.val = 1130 ∨ k.val = 1131 ∨ k.val = 1132 ∨ k.val = 1133 ∨ k.val = 1134 ∨ k.val = 1135 ∨ k.val = 1136 ∨ k.val = 1137 ∨ k.val = 1138 ∨ k.val = 1139 ∨ k.val = 1140 ∨ k.val = 1141 ∨ k.val = 1142 ∨ k.val = 1143 ∨ k.val = 1144 ∨ k.val = 1145 ∨ k.val = 1146 ∨ k.val = 1147 ∨ k.val = 1148 ∨ k.val = 1149 ∨ k.val = 1150 ∨ k.val = 1151 := by omega
  rcases heq with h1120 | h1121 | h1122 | h1123 | h1124 | h1125 | h1126 | h1127 | h1128 | h1129 | h1130 | h1131 | h1132 | h1133 | h1134 | h1135 | h1136 | h1137 | h1138 | h1139 | h1140 | h1141 | h1142 | h1143 | h1144 | h1145 | h1146 | h1147 | h1148 | h1149 | h1150 | h1151
  · have he : k = (1120 : Fin 2886) := Fin.ext h1120
    subst k
    rw [keyMomentRowsAt1120]
    exact keyMoment1120 B hB
  · have he : k = (1121 : Fin 2886) := Fin.ext h1121
    subst k
    rw [keyMomentRowsAt1121]
    exact keyMoment1121 B hB
  · have he : k = (1122 : Fin 2886) := Fin.ext h1122
    subst k
    rw [keyMomentRowsAt1122]
    exact keyMoment1122 B hB
  · have he : k = (1123 : Fin 2886) := Fin.ext h1123
    subst k
    rw [keyMomentRowsAt1123]
    exact keyMoment1123 B hB
  · have he : k = (1124 : Fin 2886) := Fin.ext h1124
    subst k
    rw [keyMomentRowsAt1124]
    exact keyMoment1124 B hB
  · have he : k = (1125 : Fin 2886) := Fin.ext h1125
    subst k
    rw [keyMomentRowsAt1125]
    exact keyMoment1125 B hB
  · have he : k = (1126 : Fin 2886) := Fin.ext h1126
    subst k
    rw [keyMomentRowsAt1126]
    exact keyMoment1126 B hB
  · have he : k = (1127 : Fin 2886) := Fin.ext h1127
    subst k
    rw [keyMomentRowsAt1127]
    exact keyMoment1127 B hB
  · have he : k = (1128 : Fin 2886) := Fin.ext h1128
    subst k
    rw [keyMomentRowsAt1128]
    exact keyMoment1128 B hB
  · have he : k = (1129 : Fin 2886) := Fin.ext h1129
    subst k
    rw [keyMomentRowsAt1129]
    exact keyMoment1129 B hB
  · have he : k = (1130 : Fin 2886) := Fin.ext h1130
    subst k
    rw [keyMomentRowsAt1130]
    exact keyMoment1130 B hB
  · have he : k = (1131 : Fin 2886) := Fin.ext h1131
    subst k
    rw [keyMomentRowsAt1131]
    exact keyMoment1131 B hB
  · have he : k = (1132 : Fin 2886) := Fin.ext h1132
    subst k
    rw [keyMomentRowsAt1132]
    exact keyMoment1132 B hB
  · have he : k = (1133 : Fin 2886) := Fin.ext h1133
    subst k
    rw [keyMomentRowsAt1133]
    exact keyMoment1133 B hB
  · have he : k = (1134 : Fin 2886) := Fin.ext h1134
    subst k
    rw [keyMomentRowsAt1134]
    exact keyMoment1134 B hB
  · have he : k = (1135 : Fin 2886) := Fin.ext h1135
    subst k
    rw [keyMomentRowsAt1135]
    exact keyMoment1135 B hB
  · have he : k = (1136 : Fin 2886) := Fin.ext h1136
    subst k
    rw [keyMomentRowsAt1136]
    exact keyMoment1136 B hB
  · have he : k = (1137 : Fin 2886) := Fin.ext h1137
    subst k
    rw [keyMomentRowsAt1137]
    exact keyMoment1137 B hB
  · have he : k = (1138 : Fin 2886) := Fin.ext h1138
    subst k
    rw [keyMomentRowsAt1138]
    exact keyMoment1138 B hB
  · have he : k = (1139 : Fin 2886) := Fin.ext h1139
    subst k
    rw [keyMomentRowsAt1139]
    exact keyMoment1139 B hB
  · have he : k = (1140 : Fin 2886) := Fin.ext h1140
    subst k
    rw [keyMomentRowsAt1140]
    exact keyMoment1140 B hB
  · have he : k = (1141 : Fin 2886) := Fin.ext h1141
    subst k
    rw [keyMomentRowsAt1141]
    exact keyMoment1141 B hB
  · have he : k = (1142 : Fin 2886) := Fin.ext h1142
    subst k
    rw [keyMomentRowsAt1142]
    exact keyMoment1142 B hB
  · have he : k = (1143 : Fin 2886) := Fin.ext h1143
    subst k
    rw [keyMomentRowsAt1143]
    exact keyMoment1143 B hB
  · have he : k = (1144 : Fin 2886) := Fin.ext h1144
    subst k
    rw [keyMomentRowsAt1144]
    exact keyMoment1144 B hB
  · have he : k = (1145 : Fin 2886) := Fin.ext h1145
    subst k
    rw [keyMomentRowsAt1145]
    exact keyMoment1145 B hB
  · have he : k = (1146 : Fin 2886) := Fin.ext h1146
    subst k
    rw [keyMomentRowsAt1146]
    exact keyMoment1146 B hB
  · have he : k = (1147 : Fin 2886) := Fin.ext h1147
    subst k
    rw [keyMomentRowsAt1147]
    exact keyMoment1147 B hB
  · have he : k = (1148 : Fin 2886) := Fin.ext h1148
    subst k
    rw [keyMomentRowsAt1148]
    exact keyMoment1148 B hB
  · have he : k = (1149 : Fin 2886) := Fin.ext h1149
    subst k
    rw [keyMomentRowsAt1149]
    exact keyMoment1149 B hB
  · have he : k = (1150 : Fin 2886) := Fin.ext h1150
    subst k
    rw [keyMomentRowsAt1150]
    exact keyMoment1150 B hB
  · have he : k = (1151 : Fin 2886) := Fin.ext h1151
    subst k
    rw [keyMomentRowsAt1151]
    exact keyMoment1151 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound35_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound35_e_oai
