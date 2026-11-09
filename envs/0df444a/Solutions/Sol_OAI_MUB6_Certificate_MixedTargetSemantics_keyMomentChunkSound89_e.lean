-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound89_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:06:35.091755+00:00
-- url     : https://prove2.me/submissions/97bfefc9-c6aa-4123-8f97-cc7bc899114f

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical336
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical43008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43008 raw43008Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw43008 raw43008Labels = mixedMoment B raw43008step0 raw43008step0Labels := by
      have ha : raw43008step0 = (fun i j => raw43008 (permutation448 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43008step0 raw43008; decide +kernel
      have hl : raw43008step0Labels = raw43008Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43008 raw43008Labels permutation448 permutation4
    mixedMoment B raw43008step0 raw43008step0Labels = mixedMoment B raw43008step1 raw43008step1Labels := by
      have ha : raw43008step1 = -raw43008step0 := by apply Matrix.ext; change ∀ i j, raw43008step1 i j = -(raw43008step0 i j); unfold raw43008step1 raw43008step0; decide +kernel
      have hl : raw43008step1Labels = raw43008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43008step1 raw43008step1Labels = mixedMoment B raw43008step2 raw43008step2Labels := by
      have ha : raw43008step2 = raw43008step1 := by apply Matrix.ext; unfold raw43008step2 raw43008step1; decide +kernel
      have hl : raw43008step1Labels = labelEmbedding1 ∘ raw43008step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43008step1 raw43008step1Labels raw43008step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

theorem canonical43009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43009 raw43009Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw43009 raw43009Labels = mixedMoment B raw43009step0 raw43009step0Labels := by
      have ha : raw43009step0 = (fun i j => raw43009 (permutation506 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43009step0 raw43009; decide +kernel
      have hl : raw43009step0Labels = raw43009Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43009 raw43009Labels permutation506 permutation6
    _ = mixedMoment B node5379 node5379Labels := by rfl

theorem canonical43010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43010 raw43010Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw43010 raw43010Labels = mixedMoment B raw43010step0 raw43010step0Labels := by
      have ha : raw43010step0 = (fun i j => raw43010 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw43010step0 raw43010; decide +kernel
      have hl : raw43010step0Labels = raw43010Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43010 raw43010Labels permutation683 permutation2
    mixedMoment B raw43010step0 raw43010step0Labels = mixedMoment B raw43010step1 raw43010step1Labels := by
      have ha : raw43010step1 = -raw43010step0 := by apply Matrix.ext; change ∀ i j, raw43010step1 i j = -(raw43010step0 i j); unfold raw43010step1 raw43010step0; decide +kernel
      have hl : raw43010step1Labels = raw43010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43010step1 raw43010step1Labels = mixedMoment B raw43010step2 raw43010step2Labels := by
      have ha : raw43010step2 = raw43010step1 := by apply Matrix.ext; unfold raw43010step2 raw43010step1; decide +kernel
      have hl : raw43010step1Labels = labelEmbedding1 ∘ raw43010step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43010step1 raw43010step1Labels raw43010step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4024 node4024Labels := by rfl

theorem canonical43011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43011 raw43011Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw43011 raw43011Labels = mixedMoment B raw43011step0 raw43011step0Labels := by
      have ha : raw43011step0 = (fun i j => raw43011 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw43011step0 raw43011; decide +kernel
      have hl : raw43011step0Labels = raw43011Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43011 raw43011Labels permutation688 permutation3
    mixedMoment B raw43011step0 raw43011step0Labels = mixedMoment B raw43011step1 raw43011step1Labels := by
      have ha : raw43011step1 = -raw43011step0 := by apply Matrix.ext; change ∀ i j, raw43011step1 i j = -(raw43011step0 i j); unfold raw43011step1 raw43011step0; decide +kernel
      have hl : raw43011step1Labels = raw43011step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43011step1 raw43011step1Labels = mixedMoment B raw43011step2 raw43011step2Labels := by
      have ha : raw43011step2 = raw43011step1 := by apply Matrix.ext; unfold raw43011step2 raw43011step1; decide +kernel
      have hl : raw43011step1Labels = labelEmbedding7 ∘ raw43011step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43011step1 raw43011step1Labels raw43011step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical43012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43012 raw43012Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw43012 raw43012Labels = mixedMoment B raw43012step0 raw43012step0Labels := by
      have hz : ∀ j, raw43012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43012step0 = (fun i j => raw43012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43012step0 raw43012; decide +kernel
      have hl : raw43012step0Labels = raw43012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43012 raw43012Labels permutation434 hz
    mixedMoment B raw43012step0 raw43012step0Labels = mixedMoment B raw43012step1 raw43012step1Labels := by
      have ha : raw43012step1 = (fun i j => raw43012step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43012step1 raw43012step0; decide +kernel
      have hl : raw43012step1Labels = raw43012step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43012step0 raw43012step0Labels permutation104 permutation4
    mixedMoment B raw43012step1 raw43012step1Labels = mixedMoment B raw43012step2 raw43012step2Labels := by
      have ha : raw43012step2 = -raw43012step1 := by apply Matrix.ext; change ∀ i j, raw43012step2 i j = -(raw43012step1 i j); unfold raw43012step2 raw43012step1; decide +kernel
      have hl : raw43012step2Labels = raw43012step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43012step2 raw43012step2Labels = mixedMoment B raw43012step3 raw43012step3Labels := by
      have ha : raw43012step3 = raw43012step2 := by apply Matrix.ext; unfold raw43012step3 raw43012step2; decide +kernel
      have hl : raw43012step2Labels = labelEmbedding1 ∘ raw43012step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43012step2 raw43012step2Labels raw43012step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

theorem canonical43013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43013 raw43013Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw43013 raw43013Labels = mixedMoment B raw43013step0 raw43013step0Labels := by
      have hz : ∀ j, raw43013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43013step0 = (fun i j => raw43013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43013step0 raw43013; decide +kernel
      have hl : raw43013step0Labels = raw43013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43013 raw43013Labels permutation434 hz
    mixedMoment B raw43013step0 raw43013step0Labels = mixedMoment B raw43013step1 raw43013step1Labels := by
      have ha : raw43013step1 = (fun i j => raw43013step0 (permutation108 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43013step1 raw43013step0; decide +kernel
      have hl : raw43013step1Labels = raw43013step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43013step0 raw43013step0Labels permutation108 permutation6
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical43014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43014 raw43014Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw43014 raw43014Labels = mixedMoment B raw43014step0 raw43014step0Labels := by
      have hz : ∀ j, raw43014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43014step0 = (fun i j => raw43014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43014step0 raw43014; decide +kernel
      have hl : raw43014step0Labels = raw43014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43014 raw43014Labels permutation434 hz
    mixedMoment B raw43014step0 raw43014step0Labels = mixedMoment B raw43014step1 raw43014step1Labels := by
      have ha : raw43014step1 = (fun i j => raw43014step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43014step1 raw43014step0; decide +kernel
      have hl : raw43014step1Labels = raw43014step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43014step0 raw43014step0Labels permutation128 permutation4
    mixedMoment B raw43014step1 raw43014step1Labels = mixedMoment B raw43014step2 raw43014step2Labels := by
      have ha : raw43014step2 = -raw43014step1 := by apply Matrix.ext; change ∀ i j, raw43014step2 i j = -(raw43014step1 i j); unfold raw43014step2 raw43014step1; decide +kernel
      have hl : raw43014step2Labels = raw43014step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43014step2 raw43014step2Labels = mixedMoment B raw43014step3 raw43014step3Labels := by
      have ha : raw43014step3 = raw43014step2 := by apply Matrix.ext; unfold raw43014step3 raw43014step2; decide +kernel
      have hl : raw43014step2Labels = labelEmbedding1 ∘ raw43014step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43014step2 raw43014step2Labels raw43014step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical43015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43015 raw43015Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw43015 raw43015Labels = mixedMoment B raw43015step0 raw43015step0Labels := by
      have hz : ∀ j, raw43015 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43015step0 = (fun i j => raw43015 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43015step0 raw43015; decide +kernel
      have hl : raw43015step0Labels = raw43015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43015 raw43015Labels permutation434 hz
    mixedMoment B raw43015step0 raw43015step0Labels = mixedMoment B raw43015step1 raw43015step1Labels := by
      have ha : raw43015step1 = (fun i j => raw43015step0 (permutation129 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43015step1 raw43015step0; decide +kernel
      have hl : raw43015step1Labels = raw43015step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43015step0 raw43015step0Labels permutation129 permutation6
    _ = mixedMoment B node4603 node4603Labels := by rfl

theorem canonical43016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43016 raw43016Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw43016 raw43016Labels = mixedMoment B raw43016step0 raw43016step0Labels := by
      have ha : raw43016step0 = (fun i j => raw43016 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw43016step0 raw43016; decide +kernel
      have hl : raw43016step0Labels = raw43016Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43016 raw43016Labels permutation683 permutation2
    mixedMoment B raw43016step0 raw43016step0Labels = mixedMoment B raw43016step1 raw43016step1Labels := by
      have ha : raw43016step1 = -raw43016step0 := by apply Matrix.ext; change ∀ i j, raw43016step1 i j = -(raw43016step0 i j); unfold raw43016step1 raw43016step0; decide +kernel
      have hl : raw43016step1Labels = raw43016step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43016step1 raw43016step1Labels = mixedMoment B raw43016step2 raw43016step2Labels := by
      have ha : raw43016step2 = raw43016step1 := by apply Matrix.ext; unfold raw43016step2 raw43016step1; decide +kernel
      have hl : raw43016step1Labels = labelEmbedding1 ∘ raw43016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43016step1 raw43016step1Labels raw43016step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

theorem canonical43017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43017 raw43017Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw43017 raw43017Labels = mixedMoment B raw43017step0 raw43017step0Labels := by
      have ha : raw43017step0 = (fun i j => raw43017 (permutation600 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43017step0 raw43017; decide +kernel
      have hl : raw43017step0Labels = raw43017Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43017 raw43017Labels permutation600 permutation6
    _ = mixedMoment B node4590 node4590Labels := by rfl

theorem canonical43018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43018 raw43018Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw43018 raw43018Labels = mixedMoment B raw43018step0 raw43018step0Labels := by
      have ha : raw43018step0 = (fun i j => raw43018 (permutation405 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43018step0 raw43018; decide +kernel
      have hl : raw43018step0Labels = raw43018Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43018 raw43018Labels permutation405 permutation4
    mixedMoment B raw43018step0 raw43018step0Labels = mixedMoment B raw43018step1 raw43018step1Labels := by
      have ha : raw43018step1 = raw43018step0 := by apply Matrix.ext; unfold raw43018step1 raw43018step0; decide +kernel
      have hl : raw43018step0Labels = labelEmbedding1 ∘ raw43018step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43018step0 raw43018step0Labels raw43018step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical43019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43019 raw43019Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw43019 raw43019Labels = mixedMoment B raw43019step0 raw43019step0Labels := by
      have ha : raw43019step0 = (fun i j => raw43019 (permutation376 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43019step0 raw43019; decide +kernel
      have hl : raw43019step0Labels = raw43019Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43019 raw43019Labels permutation376 permutation6
    mixedMoment B raw43019step0 raw43019step0Labels = mixedMoment B raw43019step1 raw43019step1Labels := by
      have ha : raw43019step1 = -raw43019step0 := by apply Matrix.ext; change ∀ i j, raw43019step1 i j = -(raw43019step0 i j); unfold raw43019step1 raw43019step0; decide +kernel
      have hl : raw43019step1Labels = raw43019step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5129 node5129Labels := by rfl

theorem canonical43020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43020 raw43020Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw43020 raw43020Labels = mixedMoment B raw43020step0 raw43020step0Labels := by
      have hz : ∀ j, raw43020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43020step0 = (fun i j => raw43020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43020step0 raw43020; decide +kernel
      have hl : raw43020step0Labels = raw43020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43020 raw43020Labels permutation434 hz
    mixedMoment B raw43020step0 raw43020step0Labels = mixedMoment B raw43020step1 raw43020step1Labels := by
      have ha : raw43020step1 = (fun i j => raw43020step0 (permutation129 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43020step1 raw43020step0; decide +kernel
      have hl : raw43020step1Labels = raw43020step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43020step0 raw43020step0Labels permutation129 permutation4
    mixedMoment B raw43020step1 raw43020step1Labels = mixedMoment B raw43020step2 raw43020step2Labels := by
      have ha : raw43020step2 = -raw43020step1 := by apply Matrix.ext; change ∀ i j, raw43020step2 i j = -(raw43020step1 i j); unfold raw43020step2 raw43020step1; decide +kernel
      have hl : raw43020step2Labels = raw43020step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43020step2 raw43020step2Labels = mixedMoment B raw43020step3 raw43020step3Labels := by
      have ha : raw43020step3 = raw43020step2 := by apply Matrix.ext; unfold raw43020step3 raw43020step2; decide +kernel
      have hl : raw43020step2Labels = labelEmbedding1 ∘ raw43020step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43020step2 raw43020step2Labels raw43020step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical43021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43021 raw43021Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw43021 raw43021Labels = mixedMoment B raw43021step0 raw43021step0Labels := by
      have hz : ∀ j, raw43021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43021step0 = (fun i j => raw43021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43021step0 raw43021; decide +kernel
      have hl : raw43021step0Labels = raw43021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43021 raw43021Labels permutation434 hz
    mixedMoment B raw43021step0 raw43021step0Labels = mixedMoment B raw43021step1 raw43021step1Labels := by
      have ha : raw43021step1 = (fun i j => raw43021step0 (permutation132 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43021step1 raw43021step0; decide +kernel
      have hl : raw43021step1Labels = raw43021step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43021step0 raw43021step0Labels permutation132 permutation6
    _ = mixedMoment B node4591 node4591Labels := by rfl

theorem canonical43022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43022 raw43022Labels = mixedMoment B node3835 node3835Labels := by
  calc
    mixedMoment B raw43022 raw43022Labels = mixedMoment B raw43022step0 raw43022step0Labels := by
      have ha : raw43022step0 = (fun i j => raw43022 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw43022step0 raw43022; decide +kernel
      have hl : raw43022step0Labels = raw43022Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43022 raw43022Labels permutation683 permutation2
    mixedMoment B raw43022step0 raw43022step0Labels = mixedMoment B raw43022step1 raw43022step1Labels := by
      have ha : raw43022step1 = -raw43022step0 := by apply Matrix.ext; change ∀ i j, raw43022step1 i j = -(raw43022step0 i j); unfold raw43022step1 raw43022step0; decide +kernel
      have hl : raw43022step1Labels = raw43022step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43022step1 raw43022step1Labels = mixedMoment B raw43022step2 raw43022step2Labels := by
      have ha : raw43022step2 = raw43022step1 := by apply Matrix.ext; unfold raw43022step2 raw43022step1; decide +kernel
      have hl : raw43022step1Labels = labelEmbedding1 ∘ raw43022step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43022step1 raw43022step1Labels raw43022step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3835 node3835Labels := by rfl

theorem canonical43023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43023 raw43023Labels = mixedMoment B node5377 node5377Labels := by
  calc
    mixedMoment B raw43023 raw43023Labels = mixedMoment B raw43023step0 raw43023step0Labels := by
      have ha : raw43023step0 = (fun i j => raw43023 (permutation507 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43023step0 raw43023; decide +kernel
      have hl : raw43023step0Labels = raw43023Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43023 raw43023Labels permutation507 permutation6
    _ = mixedMoment B node5377 node5377Labels := by rfl

theorem canonical43024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43024 raw43024Labels = mixedMoment B node3297 node3297Labels := by
  calc
    mixedMoment B raw43024 raw43024Labels = mixedMoment B raw43024step0 raw43024step0Labels := by
      have hz : ∀ j, raw43024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43024step0 = (fun i j => raw43024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43024step0 raw43024; decide +kernel
      have hl : raw43024step0Labels = raw43024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43024 raw43024Labels permutation434 hz
    mixedMoment B raw43024step0 raw43024step0Labels = mixedMoment B raw43024step1 raw43024step1Labels := by
      have ha : raw43024step1 = (fun i j => raw43024step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw43024step1 raw43024step0; decide +kernel
      have hl : raw43024step1Labels = raw43024step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43024step0 raw43024step0Labels permutation146 permutation2
    mixedMoment B raw43024step1 raw43024step1Labels = mixedMoment B raw43024step2 raw43024step2Labels := by
      have ha : raw43024step2 = -raw43024step1 := by apply Matrix.ext; change ∀ i j, raw43024step2 i j = -(raw43024step1 i j); unfold raw43024step2 raw43024step1; decide +kernel
      have hl : raw43024step2Labels = raw43024step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43024step2 raw43024step2Labels = mixedMoment B raw43024step3 raw43024step3Labels := by
      have ha : raw43024step3 = raw43024step2 := by apply Matrix.ext; unfold raw43024step3 raw43024step2; decide +kernel
      have hl : raw43024step2Labels = labelEmbedding1 ∘ raw43024step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43024step2 raw43024step2Labels raw43024step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3297 node3297Labels := by rfl

theorem canonical43025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43025 raw43025Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw43025 raw43025Labels = mixedMoment B raw43025step0 raw43025step0Labels := by
      have hz : ∀ j, raw43025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43025step0 = (fun i j => raw43025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43025step0 raw43025; decide +kernel
      have hl : raw43025step0Labels = raw43025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43025 raw43025Labels permutation434 hz
    mixedMoment B raw43025step0 raw43025step0Labels = mixedMoment B raw43025step1 raw43025step1Labels := by
      have ha : raw43025step1 = (fun i j => raw43025step0 (permutation132 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43025step1 raw43025step0; decide +kernel
      have hl : raw43025step1Labels = raw43025step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43025step0 raw43025step0Labels permutation132 permutation6
    _ = mixedMoment B node4593 node4593Labels := by rfl

theorem canonical43026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43026 raw43026Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw43026 raw43026Labels = mixedMoment B raw43026step0 raw43026step0Labels := by
      have hz : ∀ j, raw43026 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw43026step0 = (fun i j => raw43026 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw43026step0 raw43026; decide +kernel
      have hl : raw43026step0Labels = raw43026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43026 raw43026Labels permutation520 hz
    mixedMoment B raw43026step0 raw43026step0Labels = mixedMoment B raw43026step1 raw43026step1Labels := by
      have ha : raw43026step1 = (fun i j => raw43026step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43026step1 raw43026step0; decide +kernel
      have hl : raw43026step1Labels = raw43026step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43026step0 raw43026step0Labels permutation104 permutation4
    mixedMoment B raw43026step1 raw43026step1Labels = mixedMoment B raw43026step2 raw43026step2Labels := by
      have ha : raw43026step2 = -raw43026step1 := by apply Matrix.ext; change ∀ i j, raw43026step2 i j = -(raw43026step1 i j); unfold raw43026step2 raw43026step1; decide +kernel
      have hl : raw43026step2Labels = raw43026step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43026step2 raw43026step2Labels = mixedMoment B raw43026step3 raw43026step3Labels := by
      have ha : raw43026step3 = raw43026step2 := by apply Matrix.ext; unfold raw43026step3 raw43026step2; decide +kernel
      have hl : raw43026step2Labels = labelEmbedding1 ∘ raw43026step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43026step2 raw43026step2Labels raw43026step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2235 node2235Labels := by rfl

theorem canonical43027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43027 raw43027Labels = mixedMoment B node4886 node4886Labels := by
  calc
    mixedMoment B raw43027 raw43027Labels = mixedMoment B raw43027step0 raw43027step0Labels := by
      have hz : ∀ j, raw43027 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw43027step0 = (fun i j => raw43027 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw43027step0 raw43027; decide +kernel
      have hl : raw43027step0Labels = raw43027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43027 raw43027Labels permutation520 hz
    mixedMoment B raw43027step0 raw43027step0Labels = mixedMoment B raw43027step1 raw43027step1Labels := by
      have ha : raw43027step1 = (fun i j => raw43027step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43027step1 raw43027step0; decide +kernel
      have hl : raw43027step1Labels = raw43027step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43027step0 raw43027step0Labels permutation104 permutation4
    mixedMoment B raw43027step1 raw43027step1Labels = mixedMoment B raw43027step2 raw43027step2Labels := by
      have ha : raw43027step2 = -raw43027step1 := by apply Matrix.ext; change ∀ i j, raw43027step2 i j = -(raw43027step1 i j); unfold raw43027step2 raw43027step1; decide +kernel
      have hl : raw43027step2Labels = raw43027step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43027step2 raw43027step2Labels = mixedMoment B raw43027step3 raw43027step3Labels := by
      have ha : raw43027step3 = raw43027step2 := by apply Matrix.ext; unfold raw43027step3 raw43027step2; decide +kernel
      have hl : raw43027step2Labels = labelEmbedding10 ∘ raw43027step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43027step2 raw43027step2Labels raw43027step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4886 node4886Labels := by rfl

theorem canonical43028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43028 raw43028Labels = mixedMoment B node2187 node2187Labels := by
  calc
    mixedMoment B raw43028 raw43028Labels = mixedMoment B raw43028step0 raw43028step0Labels := by
      have ha : raw43028step0 = (fun i j => raw43028 (permutation484 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43028step0 raw43028; decide +kernel
      have hl : raw43028step0Labels = raw43028Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43028 raw43028Labels permutation484 permutation4
    mixedMoment B raw43028step0 raw43028step0Labels = mixedMoment B raw43028step1 raw43028step1Labels := by
      have ha : raw43028step1 = -raw43028step0 := by apply Matrix.ext; change ∀ i j, raw43028step1 i j = -(raw43028step0 i j); unfold raw43028step1 raw43028step0; decide +kernel
      have hl : raw43028step1Labels = raw43028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43028step1 raw43028step1Labels = mixedMoment B raw43028step2 raw43028step2Labels := by
      have ha : raw43028step2 = raw43028step1 := by apply Matrix.ext; unfold raw43028step2 raw43028step1; decide +kernel
      have hl : raw43028step1Labels = labelEmbedding1 ∘ raw43028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43028step1 raw43028step1Labels raw43028step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2187 node2187Labels := by rfl

theorem canonical43029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43029 raw43029Labels = mixedMoment B node4830 node4830Labels := by
  calc
    mixedMoment B raw43029 raw43029Labels = mixedMoment B raw43029step0 raw43029step0Labels := by
      have ha : raw43029step0 = (fun i j => raw43029 (permutation484 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43029step0 raw43029; decide +kernel
      have hl : raw43029step0Labels = raw43029Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43029 raw43029Labels permutation484 permutation6
    _ = mixedMoment B node4830 node4830Labels := by rfl

theorem canonical43030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43030 raw43030Labels = mixedMoment B node2233 node2233Labels := by
  calc
    mixedMoment B raw43030 raw43030Labels = mixedMoment B raw43030step0 raw43030step0Labels := by
      have ha : raw43030step0 = (fun i j => raw43030 (permutation434 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43030step0 raw43030; decide +kernel
      have hl : raw43030step0Labels = raw43030Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43030 raw43030Labels permutation434 permutation4
    mixedMoment B raw43030step0 raw43030step0Labels = mixedMoment B raw43030step1 raw43030step1Labels := by
      have ha : raw43030step1 = -raw43030step0 := by apply Matrix.ext; change ∀ i j, raw43030step1 i j = -(raw43030step0 i j); unfold raw43030step1 raw43030step0; decide +kernel
      have hl : raw43030step1Labels = raw43030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43030step1 raw43030step1Labels = mixedMoment B raw43030step2 raw43030step2Labels := by
      have ha : raw43030step2 = raw43030step1 := by apply Matrix.ext; unfold raw43030step2 raw43030step1; decide +kernel
      have hl : raw43030step1Labels = labelEmbedding1 ∘ raw43030step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43030step1 raw43030step1Labels raw43030step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2233 node2233Labels := by rfl

theorem canonical43031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43031 raw43031Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw43031 raw43031Labels = mixedMoment B raw43031step0 raw43031step0Labels := by
      have ha : raw43031step0 = (fun i j => raw43031 (permutation434 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43031step0 raw43031; decide +kernel
      have hl : raw43031step0Labels = raw43031Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43031 raw43031Labels permutation434 permutation4
    mixedMoment B raw43031step0 raw43031step0Labels = mixedMoment B raw43031step1 raw43031step1Labels := by
      have ha : raw43031step1 = -raw43031step0 := by apply Matrix.ext; change ∀ i j, raw43031step1 i j = -(raw43031step0 i j); unfold raw43031step1 raw43031step0; decide +kernel
      have hl : raw43031step1Labels = raw43031step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43031step1 raw43031step1Labels = mixedMoment B raw43031step2 raw43031step2Labels := by
      have ha : raw43031step2 = raw43031step1 := by apply Matrix.ext; unfold raw43031step2 raw43031step1; decide +kernel
      have hl : raw43031step1Labels = labelEmbedding10 ∘ raw43031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43031step1 raw43031step1Labels raw43031step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

theorem canonical43032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43032 raw43032Labels = mixedMoment B node2232 node2232Labels := by
  calc
    mixedMoment B raw43032 raw43032Labels = mixedMoment B raw43032step0 raw43032step0Labels := by
      have ha : raw43032step0 = (fun i j => raw43032 (permutation435 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43032step0 raw43032; decide +kernel
      have hl : raw43032step0Labels = raw43032Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43032 raw43032Labels permutation435 permutation4
    mixedMoment B raw43032step0 raw43032step0Labels = mixedMoment B raw43032step1 raw43032step1Labels := by
      have ha : raw43032step1 = -raw43032step0 := by apply Matrix.ext; change ∀ i j, raw43032step1 i j = -(raw43032step0 i j); unfold raw43032step1 raw43032step0; decide +kernel
      have hl : raw43032step1Labels = raw43032step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43032step1 raw43032step1Labels = mixedMoment B raw43032step2 raw43032step2Labels := by
      have ha : raw43032step2 = raw43032step1 := by apply Matrix.ext; unfold raw43032step2 raw43032step1; decide +kernel
      have hl : raw43032step1Labels = labelEmbedding1 ∘ raw43032step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43032step1 raw43032step1Labels raw43032step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2232 node2232Labels := by rfl

theorem canonical43033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43033 raw43033Labels = mixedMoment B node4863 node4863Labels := by
  calc
    mixedMoment B raw43033 raw43033Labels = mixedMoment B raw43033step0 raw43033step0Labels := by
      have ha : raw43033step0 = (fun i j => raw43033 (permutation505 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43033step0 raw43033; decide +kernel
      have hl : raw43033step0Labels = raw43033Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43033 raw43033Labels permutation505 permutation6
    _ = mixedMoment B node4863 node4863Labels := by rfl

theorem canonical43034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43034 raw43034Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw43034 raw43034Labels = mixedMoment B raw43034step0 raw43034step0Labels := by
      have ha : raw43034step0 = (fun i j => raw43034 (permutation659 i) (permutation2 j)) := by apply Matrix.ext; unfold raw43034step0 raw43034; decide +kernel
      have hl : raw43034step0Labels = raw43034Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43034 raw43034Labels permutation659 permutation2
    mixedMoment B raw43034step0 raw43034step0Labels = mixedMoment B raw43034step1 raw43034step1Labels := by
      have ha : raw43034step1 = -raw43034step0 := by apply Matrix.ext; change ∀ i j, raw43034step1 i j = -(raw43034step0 i j); unfold raw43034step1 raw43034step0; decide +kernel
      have hl : raw43034step1Labels = raw43034step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43034step1 raw43034step1Labels = mixedMoment B raw43034step2 raw43034step2Labels := by
      have ha : raw43034step2 = raw43034step1 := by apply Matrix.ext; unfold raw43034step2 raw43034step1; decide +kernel
      have hl : raw43034step1Labels = labelEmbedding1 ∘ raw43034step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43034step1 raw43034step1Labels raw43034step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3221 node3221Labels := by rfl

theorem canonical43035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43035 raw43035Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw43035 raw43035Labels = mixedMoment B raw43035step0 raw43035step0Labels := by
      have ha : raw43035step0 = (fun i j => raw43035 (permutation591 i) (permutation5 j)) := by apply Matrix.ext; unfold raw43035step0 raw43035; decide +kernel
      have hl : raw43035step0Labels = raw43035Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43035 raw43035Labels permutation591 permutation5
    mixedMoment B raw43035step0 raw43035step0Labels = mixedMoment B raw43035step1 raw43035step1Labels := by
      have ha : raw43035step1 = raw43035step0 := by apply Matrix.ext; unfold raw43035step1 raw43035step0; decide +kernel
      have hl : raw43035step0Labels = labelEmbedding9 ∘ raw43035step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43035step0 raw43035step0Labels raw43035step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

theorem canonical43036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43036 raw43036Labels = mixedMoment B node3059 node3059Labels := by
  calc
    mixedMoment B raw43036 raw43036Labels = mixedMoment B raw43036step0 raw43036step0Labels := by
      have ha : raw43036step0 = (fun i j => raw43036 (permutation591 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43036step0 raw43036; decide +kernel
      have hl : raw43036step0Labels = raw43036Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43036 raw43036Labels permutation591 permutation4
    mixedMoment B raw43036step0 raw43036step0Labels = mixedMoment B raw43036step1 raw43036step1Labels := by
      have ha : raw43036step1 = raw43036step0 := by apply Matrix.ext; unfold raw43036step1 raw43036step0; decide +kernel
      have hl : raw43036step0Labels = labelEmbedding1 ∘ raw43036step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43036step0 raw43036step0Labels raw43036step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3059 node3059Labels := by rfl

theorem canonical43037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43037 raw43037Labels = mixedMoment B node5277 node5277Labels := by
  calc
    mixedMoment B raw43037 raw43037Labels = mixedMoment B raw43037step0 raw43037step0Labels := by
      have ha : raw43037step0 = (fun i j => raw43037 (permutation591 i) (permutation5 j)) := by apply Matrix.ext; unfold raw43037step0 raw43037; decide +kernel
      have hl : raw43037step0Labels = raw43037Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43037 raw43037Labels permutation591 permutation5
    mixedMoment B raw43037step0 raw43037step0Labels = mixedMoment B raw43037step1 raw43037step1Labels := by
      have ha : raw43037step1 = raw43037step0 := by apply Matrix.ext; unfold raw43037step1 raw43037step0; decide +kernel
      have hl : raw43037step0Labels = labelEmbedding9 ∘ raw43037step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43037step0 raw43037step0Labels raw43037step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5277 node5277Labels := by rfl

theorem canonical43038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43038 raw43038Labels = mixedMoment B node2690 node2690Labels := by
  calc
    mixedMoment B raw43038 raw43038Labels = mixedMoment B raw43038step0 raw43038step0Labels := by
      have ha : raw43038step0 = (fun i j => raw43038 (permutation521 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43038step0 raw43038; decide +kernel
      have hl : raw43038step0Labels = raw43038Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43038 raw43038Labels permutation521 permutation4
    mixedMoment B raw43038step0 raw43038step0Labels = mixedMoment B raw43038step1 raw43038step1Labels := by
      have ha : raw43038step1 = raw43038step0 := by apply Matrix.ext; unfold raw43038step1 raw43038step0; decide +kernel
      have hl : raw43038step0Labels = labelEmbedding1 ∘ raw43038step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43038step0 raw43038step0Labels raw43038step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2690 node2690Labels := by rfl

theorem canonical43039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43039 raw43039Labels = mixedMoment B node4975 node4975Labels := by
  calc
    mixedMoment B raw43039 raw43039Labels = mixedMoment B raw43039step0 raw43039step0Labels := by
      have ha : raw43039step0 = (fun i j => raw43039 (permutation647 i) (permutation7 j)) := by apply Matrix.ext; unfold raw43039step0 raw43039; decide +kernel
      have hl : raw43039step0Labels = raw43039Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43039 raw43039Labels permutation647 permutation7
    mixedMoment B raw43039step0 raw43039step0Labels = mixedMoment B raw43039step1 raw43039step1Labels := by
      have ha : raw43039step1 = raw43039step0 := by apply Matrix.ext; unfold raw43039step1 raw43039step0; decide +kernel
      have hl : raw43039step0Labels = labelEmbedding6 ∘ raw43039step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43039step0 raw43039step0Labels raw43039step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4975 node4975Labels := by rfl

theorem canonical43040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43040 raw43040Labels = mixedMoment B node3058 node3058Labels := by
  calc
    mixedMoment B raw43040 raw43040Labels = mixedMoment B raw43040step0 raw43040step0Labels := by
      have ha : raw43040step0 = (fun i j => raw43040 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43040step0 raw43040; decide +kernel
      have hl : raw43040step0Labels = raw43040Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43040 raw43040Labels permutation590 permutation4
    mixedMoment B raw43040step0 raw43040step0Labels = mixedMoment B raw43040step1 raw43040step1Labels := by
      have ha : raw43040step1 = raw43040step0 := by apply Matrix.ext; unfold raw43040step1 raw43040step0; decide +kernel
      have hl : raw43040step0Labels = labelEmbedding1 ∘ raw43040step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43040step0 raw43040step0Labels raw43040step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3058 node3058Labels := by rfl

theorem canonical43041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43041 raw43041Labels = mixedMoment B node5097 node5097Labels := by
  calc
    mixedMoment B raw43041 raw43041Labels = mixedMoment B raw43041step0 raw43041step0Labels := by
      have ha : raw43041step0 = (fun i j => raw43041 (permutation553 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43041step0 raw43041; decide +kernel
      have hl : raw43041step0Labels = raw43041Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43041 raw43041Labels permutation553 permutation6
    _ = mixedMoment B node5097 node5097Labels := by rfl

theorem canonical43042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43042 raw43042Labels = mixedMoment B node2688 node2688Labels := by
  calc
    mixedMoment B raw43042 raw43042Labels = mixedMoment B raw43042step0 raw43042step0Labels := by
      have ha : raw43042step0 = (fun i j => raw43042 (permutation520 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43042step0 raw43042; decide +kernel
      have hl : raw43042step0Labels = raw43042Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43042 raw43042Labels permutation520 permutation4
    mixedMoment B raw43042step0 raw43042step0Labels = mixedMoment B raw43042step1 raw43042step1Labels := by
      have ha : raw43042step1 = raw43042step0 := by apply Matrix.ext; unfold raw43042step1 raw43042step0; decide +kernel
      have hl : raw43042step0Labels = labelEmbedding1 ∘ raw43042step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43042step0 raw43042step0Labels raw43042step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2688 node2688Labels := by rfl

theorem canonical43043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43043 raw43043Labels = mixedMoment B node4540 node4540Labels := by
  calc
    mixedMoment B raw43043 raw43043Labels = mixedMoment B raw43043step0 raw43043step0Labels := by
      have ha : raw43043step0 = (fun i j => raw43043 (permutation647 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43043step0 raw43043; decide +kernel
      have hl : raw43043step0Labels = raw43043Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43043 raw43043Labels permutation647 permutation6
    _ = mixedMoment B node4540 node4540Labels := by rfl

theorem canonical43044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43044 raw43044Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw43044 raw43044Labels = mixedMoment B raw43044step0 raw43044step0Labels := by
      have hz : ∀ j, raw43044 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43044step0 = (fun i j => raw43044 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43044step0 raw43044; decide +kernel
      have hl : raw43044step0Labels = raw43044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43044 raw43044Labels permutation434 hz
    mixedMoment B raw43044step0 raw43044step0Labels = mixedMoment B raw43044step1 raw43044step1Labels := by
      have ha : raw43044step1 = (fun i j => raw43044step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43044step1 raw43044step0; decide +kernel
      have hl : raw43044step1Labels = raw43044step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43044step0 raw43044step0Labels permutation104 permutation4
    mixedMoment B raw43044step1 raw43044step1Labels = mixedMoment B raw43044step2 raw43044step2Labels := by
      have ha : raw43044step2 = -raw43044step1 := by apply Matrix.ext; change ∀ i j, raw43044step2 i j = -(raw43044step1 i j); unfold raw43044step2 raw43044step1; decide +kernel
      have hl : raw43044step2Labels = raw43044step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43044step2 raw43044step2Labels = mixedMoment B raw43044step3 raw43044step3Labels := by
      have ha : raw43044step3 = raw43044step2 := by apply Matrix.ext; unfold raw43044step3 raw43044step2; decide +kernel
      have hl : raw43044step2Labels = labelEmbedding1 ∘ raw43044step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43044step2 raw43044step2Labels raw43044step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1700 node1700Labels := by rfl

theorem canonical43045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43045 raw43045Labels = mixedMoment B node4494 node4494Labels := by
  calc
    mixedMoment B raw43045 raw43045Labels = mixedMoment B raw43045step0 raw43045step0Labels := by
      have hz : ∀ j, raw43045 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43045step0 = (fun i j => raw43045 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43045step0 raw43045; decide +kernel
      have hl : raw43045step0Labels = raw43045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43045 raw43045Labels permutation434 hz
    mixedMoment B raw43045step0 raw43045step0Labels = mixedMoment B raw43045step1 raw43045step1Labels := by
      have ha : raw43045step1 = (fun i j => raw43045step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43045step1 raw43045step0; decide +kernel
      have hl : raw43045step1Labels = raw43045step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43045step0 raw43045step0Labels permutation104 permutation6
    _ = mixedMoment B node4494 node4494Labels := by rfl

theorem canonical43046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43046 raw43046Labels = mixedMoment B node1699 node1699Labels := by
  calc
    mixedMoment B raw43046 raw43046Labels = mixedMoment B raw43046step0 raw43046step0Labels := by
      have ha : raw43046step0 = (fun i j => raw43046 (permutation520 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43046step0 raw43046; decide +kernel
      have hl : raw43046step0Labels = raw43046Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43046 raw43046Labels permutation520 permutation4
    mixedMoment B raw43046step0 raw43046step0Labels = mixedMoment B raw43046step1 raw43046step1Labels := by
      have ha : raw43046step1 = -raw43046step0 := by apply Matrix.ext; change ∀ i j, raw43046step1 i j = -(raw43046step0 i j); unfold raw43046step1 raw43046step0; decide +kernel
      have hl : raw43046step1Labels = raw43046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43046step1 raw43046step1Labels = mixedMoment B raw43046step2 raw43046step2Labels := by
      have ha : raw43046step2 = raw43046step1 := by apply Matrix.ext; unfold raw43046step2 raw43046step1; decide +kernel
      have hl : raw43046step1Labels = labelEmbedding1 ∘ raw43046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43046step1 raw43046step1Labels raw43046step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1699 node1699Labels := by rfl

theorem canonical43047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43047 raw43047Labels = mixedMoment B node4473 node4473Labels := by
  calc
    mixedMoment B raw43047 raw43047Labels = mixedMoment B raw43047step0 raw43047step0Labels := by
      have ha : raw43047step0 = (fun i j => raw43047 (permutation569 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43047step0 raw43047; decide +kernel
      have hl : raw43047step0Labels = raw43047Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43047 raw43047Labels permutation569 permutation6
    _ = mixedMoment B node4473 node4473Labels := by rfl

theorem canonical43048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43048 raw43048Labels = mixedMoment B node1502 node1502Labels := by
  calc
    mixedMoment B raw43048 raw43048Labels = mixedMoment B raw43048step0 raw43048step0Labels := by
      have ha : raw43048step0 = (fun i j => raw43048 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43048step0 raw43048; decide +kernel
      have hl : raw43048step0Labels = raw43048Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43048 raw43048Labels permutation590 permutation4
    mixedMoment B raw43048step0 raw43048step0Labels = mixedMoment B raw43048step1 raw43048step1Labels := by
      have ha : raw43048step1 = -raw43048step0 := by apply Matrix.ext; change ∀ i j, raw43048step1 i j = -(raw43048step0 i j); unfold raw43048step1 raw43048step0; decide +kernel
      have hl : raw43048step1Labels = raw43048step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43048step1 raw43048step1Labels = mixedMoment B raw43048step2 raw43048step2Labels := by
      have ha : raw43048step2 = raw43048step1 := by apply Matrix.ext; unfold raw43048step2 raw43048step1; decide +kernel
      have hl : raw43048step1Labels = labelEmbedding1 ∘ raw43048step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43048step1 raw43048step1Labels raw43048step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1502 node1502Labels := by rfl

theorem canonical43049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43049 raw43049Labels = mixedMoment B node4169 node4169Labels := by
  calc
    mixedMoment B raw43049 raw43049Labels = mixedMoment B raw43049step0 raw43049step0Labels := by
      have ha : raw43049step0 = (fun i j => raw43049 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43049step0 raw43049; decide +kernel
      have hl : raw43049step0Labels = raw43049Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43049 raw43049Labels permutation590 permutation6
    _ = mixedMoment B node4169 node4169Labels := by rfl

theorem canonical43050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43050 raw43050Labels = mixedMoment B node1501 node1501Labels := by
  calc
    mixedMoment B raw43050 raw43050Labels = mixedMoment B raw43050step0 raw43050step0Labels := by
      have ha : raw43050step0 = (fun i j => raw43050 (permutation591 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43050step0 raw43050; decide +kernel
      have hl : raw43050step0Labels = raw43050Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43050 raw43050Labels permutation591 permutation4
    mixedMoment B raw43050step0 raw43050step0Labels = mixedMoment B raw43050step1 raw43050step1Labels := by
      have ha : raw43050step1 = -raw43050step0 := by apply Matrix.ext; change ∀ i j, raw43050step1 i j = -(raw43050step0 i j); unfold raw43050step1 raw43050step0; decide +kernel
      have hl : raw43050step1Labels = raw43050step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43050step1 raw43050step1Labels = mixedMoment B raw43050step2 raw43050step2Labels := by
      have ha : raw43050step2 = raw43050step1 := by apply Matrix.ext; unfold raw43050step2 raw43050step1; decide +kernel
      have hl : raw43050step1Labels = labelEmbedding1 ∘ raw43050step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43050step1 raw43050step1Labels raw43050step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1501 node1501Labels := by rfl

theorem canonical43051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43051 raw43051Labels = mixedMoment B node4149 node4149Labels := by
  calc
    mixedMoment B raw43051 raw43051Labels = mixedMoment B raw43051step0 raw43051step0Labels := by
      have ha : raw43051step0 = (fun i j => raw43051 (permutation665 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43051step0 raw43051; decide +kernel
      have hl : raw43051step0Labels = raw43051Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43051 raw43051Labels permutation665 permutation6
    _ = mixedMoment B node4149 node4149Labels := by rfl

theorem canonical43052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43052 raw43052Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw43052 raw43052Labels = mixedMoment B raw43052step0 raw43052step0Labels := by
      have ha : raw43052step0 = (fun i j => raw43052 (permutation484 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43052step0 raw43052; decide +kernel
      have hl : raw43052step0Labels = raw43052Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43052 raw43052Labels permutation484 permutation4
    mixedMoment B raw43052step0 raw43052step0Labels = mixedMoment B raw43052step1 raw43052step1Labels := by
      have ha : raw43052step1 = -raw43052step0 := by apply Matrix.ext; change ∀ i j, raw43052step1 i j = -(raw43052step0 i j); unfold raw43052step1 raw43052step0; decide +kernel
      have hl : raw43052step1Labels = raw43052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43052step1 raw43052step1Labels = mixedMoment B raw43052step2 raw43052step2Labels := by
      have ha : raw43052step2 = raw43052step1 := by apply Matrix.ext; unfold raw43052step2 raw43052step1; decide +kernel
      have hl : raw43052step1Labels = labelEmbedding1 ∘ raw43052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43052step1 raw43052step1Labels raw43052step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2192 node2192Labels := by rfl

theorem canonical43053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43053 raw43053Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw43053 raw43053Labels = mixedMoment B raw43053step0 raw43053step0Labels := by
      have ha : raw43053step0 = (fun i j => raw43053 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43053step0 raw43053; decide +kernel
      have hl : raw43053step0Labels = raw43053Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43053 raw43053Labels permutation499 permutation6
    _ = mixedMoment B node4815 node4815Labels := by rfl

theorem canonical43054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43054 raw43054Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw43054 raw43054Labels = mixedMoment B raw43054step0 raw43054step0Labels := by
      have ha : raw43054step0 = (fun i j => raw43054 (permutation439 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43054step0 raw43054; decide +kernel
      have hl : raw43054step0Labels = raw43054Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43054 raw43054Labels permutation439 permutation4
    mixedMoment B raw43054step0 raw43054step0Labels = mixedMoment B raw43054step1 raw43054step1Labels := by
      have ha : raw43054step1 = -raw43054step0 := by apply Matrix.ext; change ∀ i j, raw43054step1 i j = -(raw43054step0 i j); unfold raw43054step1 raw43054step0; decide +kernel
      have hl : raw43054step1Labels = raw43054step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43054step1 raw43054step1Labels = mixedMoment B raw43054step2 raw43054step2Labels := by
      have ha : raw43054step2 = raw43054step1 := by apply Matrix.ext; unfold raw43054step2 raw43054step1; decide +kernel
      have hl : raw43054step1Labels = labelEmbedding1 ∘ raw43054step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43054step1 raw43054step1Labels raw43054step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

theorem canonical43055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43055 raw43055Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw43055 raw43055Labels = mixedMoment B raw43055step0 raw43055step0Labels := by
      have ha : raw43055step0 = (fun i j => raw43055 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43055step0 raw43055; decide +kernel
      have hl : raw43055step0Labels = raw43055Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43055 raw43055Labels permutation514 permutation6
    _ = mixedMoment B node4851 node4851Labels := by rfl

theorem canonical43056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43056 raw43056Labels = mixedMoment B node2142 node2142Labels := by
  calc
    mixedMoment B raw43056 raw43056Labels = mixedMoment B raw43056step0 raw43056step0Labels := by
      have ha : raw43056step0 = (fun i j => raw43056 (permutation505 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43056step0 raw43056; decide +kernel
      have hl : raw43056step0Labels = raw43056Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43056 raw43056Labels permutation505 permutation4
    mixedMoment B raw43056step0 raw43056step0Labels = mixedMoment B raw43056step1 raw43056step1Labels := by
      have ha : raw43056step1 = -raw43056step0 := by apply Matrix.ext; change ∀ i j, raw43056step1 i j = -(raw43056step0 i j); unfold raw43056step1 raw43056step0; decide +kernel
      have hl : raw43056step1Labels = raw43056step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43056step1 raw43056step1Labels = mixedMoment B raw43056step2 raw43056step2Labels := by
      have ha : raw43056step2 = raw43056step1 := by apply Matrix.ext; unfold raw43056step2 raw43056step1; decide +kernel
      have hl : raw43056step1Labels = labelEmbedding1 ∘ raw43056step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43056step1 raw43056step1Labels raw43056step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2142 node2142Labels := by rfl

theorem canonical43057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43057 raw43057Labels = mixedMoment B node4677 node4677Labels := by
  calc
    mixedMoment B raw43057 raw43057Labels = mixedMoment B raw43057step0 raw43057step0Labels := by
      have ha : raw43057step0 = (fun i j => raw43057 (permutation506 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43057step0 raw43057; decide +kernel
      have hl : raw43057step0Labels = raw43057Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43057 raw43057Labels permutation506 permutation6
    _ = mixedMoment B node4677 node4677Labels := by rfl

theorem canonical43058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43058 raw43058Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw43058 raw43058Labels = mixedMoment B raw43058step0 raw43058step0Labels := by
      have ha : raw43058step0 = (fun i j => raw43058 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw43058step0 raw43058; decide +kernel
      have hl : raw43058step0Labels = raw43058Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43058 raw43058Labels permutation683 permutation2
    mixedMoment B raw43058step0 raw43058step0Labels = mixedMoment B raw43058step1 raw43058step1Labels := by
      have ha : raw43058step1 = -raw43058step0 := by apply Matrix.ext; change ∀ i j, raw43058step1 i j = -(raw43058step0 i j); unfold raw43058step1 raw43058step0; decide +kernel
      have hl : raw43058step1Labels = raw43058step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43058step1 raw43058step1Labels = mixedMoment B raw43058step2 raw43058step2Labels := by
      have ha : raw43058step2 = raw43058step1 := by apply Matrix.ext; unfold raw43058step2 raw43058step1; decide +kernel
      have hl : raw43058step1Labels = labelEmbedding1 ∘ raw43058step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43058step1 raw43058step1Labels raw43058step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

theorem canonical43059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43059 raw43059Labels = mixedMoment B node4964 node4964Labels := by
  calc
    mixedMoment B raw43059 raw43059Labels = mixedMoment B raw43059step0 raw43059step0Labels := by
      have ha : raw43059step0 = (fun i j => raw43059 (permutation659 i) (permutation7 j)) := by apply Matrix.ext; unfold raw43059step0 raw43059; decide +kernel
      have hl : raw43059step0Labels = raw43059Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43059 raw43059Labels permutation659 permutation7
    mixedMoment B raw43059step0 raw43059step0Labels = mixedMoment B raw43059step1 raw43059step1Labels := by
      have ha : raw43059step1 = raw43059step0 := by apply Matrix.ext; unfold raw43059step1 raw43059step0; decide +kernel
      have hl : raw43059step0Labels = labelEmbedding6 ∘ raw43059step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43059step0 raw43059step0Labels raw43059step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4964 node4964Labels := by rfl

theorem canonical43060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43060 raw43060Labels = mixedMoment B node3257 node3257Labels := by
  calc
    mixedMoment B raw43060 raw43060Labels = mixedMoment B raw43060step0 raw43060step0Labels := by
      have ha : raw43060step0 = (fun i j => raw43060 (permutation647 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43060step0 raw43060; decide +kernel
      have hl : raw43060step0Labels = raw43060Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43060 raw43060Labels permutation647 permutation4
    mixedMoment B raw43060step0 raw43060step0Labels = mixedMoment B raw43060step1 raw43060step1Labels := by
      have ha : raw43060step1 = -raw43060step0 := by apply Matrix.ext; change ∀ i j, raw43060step1 i j = -(raw43060step0 i j); unfold raw43060step1 raw43060step0; decide +kernel
      have hl : raw43060step1Labels = raw43060step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43060step1 raw43060step1Labels = mixedMoment B raw43060step2 raw43060step2Labels := by
      have ha : raw43060step2 = raw43060step1 := by apply Matrix.ext; unfold raw43060step2 raw43060step1; decide +kernel
      have hl : raw43060step1Labels = labelEmbedding1 ∘ raw43060step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43060step1 raw43060step1Labels raw43060step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3257 node3257Labels := by rfl

theorem canonical43061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43061 raw43061Labels = mixedMoment B node4542 node4542Labels := by
  calc
    mixedMoment B raw43061 raw43061Labels = mixedMoment B raw43061step0 raw43061step0Labels := by
      have ha : raw43061step0 = (fun i j => raw43061 (permutation648 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43061step0 raw43061; decide +kernel
      have hl : raw43061step0Labels = raw43061Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43061 raw43061Labels permutation648 permutation6
    _ = mixedMoment B node4542 node4542Labels := by rfl

theorem canonical43062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43062 raw43062Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw43062 raw43062Labels = mixedMoment B raw43062step0 raw43062step0Labels := by
      have hz : ∀ j, raw43062 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43062step0 = (fun i j => raw43062 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43062step0 raw43062; decide +kernel
      have hl : raw43062step0Labels = raw43062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43062 raw43062Labels permutation434 hz
    mixedMoment B raw43062step0 raw43062step0Labels = mixedMoment B raw43062step1 raw43062step1Labels := by
      have ha : raw43062step1 = (fun i j => raw43062step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43062step1 raw43062step0; decide +kernel
      have hl : raw43062step1Labels = raw43062step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43062step0 raw43062step0Labels permutation104 permutation4
    mixedMoment B raw43062step1 raw43062step1Labels = mixedMoment B raw43062step2 raw43062step2Labels := by
      have ha : raw43062step2 = -raw43062step1 := by apply Matrix.ext; change ∀ i j, raw43062step2 i j = -(raw43062step1 i j); unfold raw43062step2 raw43062step1; decide +kernel
      have hl : raw43062step2Labels = raw43062step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43062step2 raw43062step2Labels = mixedMoment B raw43062step3 raw43062step3Labels := by
      have ha : raw43062step3 = raw43062step2 := by apply Matrix.ext; unfold raw43062step3 raw43062step2; decide +kernel
      have hl : raw43062step2Labels = labelEmbedding1 ∘ raw43062step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43062step2 raw43062step2Labels raw43062step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

theorem canonical43063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43063 raw43063Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw43063 raw43063Labels = mixedMoment B raw43063step0 raw43063step0Labels := by
      have hz : ∀ j, raw43063 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43063step0 = (fun i j => raw43063 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43063step0 raw43063; decide +kernel
      have hl : raw43063step0Labels = raw43063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43063 raw43063Labels permutation434 hz
    mixedMoment B raw43063step0 raw43063step0Labels = mixedMoment B raw43063step1 raw43063step1Labels := by
      have ha : raw43063step1 = (fun i j => raw43063step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43063step1 raw43063step0; decide +kernel
      have hl : raw43063step1Labels = raw43063step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43063step0 raw43063step0Labels permutation122 permutation6
    _ = mixedMoment B node4474 node4474Labels := by rfl

theorem canonical43064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43064 raw43064Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw43064 raw43064Labels = mixedMoment B raw43064step0 raw43064step0Labels := by
      have hz : ∀ j, raw43064 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43064step0 = (fun i j => raw43064 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43064step0 raw43064; decide +kernel
      have hl : raw43064step0Labels = raw43064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43064 raw43064Labels permutation434 hz
    mixedMoment B raw43064step0 raw43064step0Labels = mixedMoment B raw43064step1 raw43064step1Labels := by
      have ha : raw43064step1 = (fun i j => raw43064step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43064step1 raw43064step0; decide +kernel
      have hl : raw43064step1Labels = raw43064step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43064step0 raw43064step0Labels permutation128 permutation4
    mixedMoment B raw43064step1 raw43064step1Labels = mixedMoment B raw43064step2 raw43064step2Labels := by
      have ha : raw43064step2 = -raw43064step1 := by apply Matrix.ext; change ∀ i j, raw43064step2 i j = -(raw43064step1 i j); unfold raw43064step2 raw43064step1; decide +kernel
      have hl : raw43064step2Labels = raw43064step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43064step2 raw43064step2Labels = mixedMoment B raw43064step3 raw43064step3Labels := by
      have ha : raw43064step3 = raw43064step2 := by apply Matrix.ext; unfold raw43064step3 raw43064step2; decide +kernel
      have hl : raw43064step2Labels = labelEmbedding1 ∘ raw43064step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43064step2 raw43064step2Labels raw43064step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1508 node1508Labels := by rfl

theorem canonical43065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43065 raw43065Labels = mixedMoment B node4173 node4173Labels := by
  calc
    mixedMoment B raw43065 raw43065Labels = mixedMoment B raw43065step0 raw43065step0Labels := by
      have hz : ∀ j, raw43065 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43065step0 = (fun i j => raw43065 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43065step0 raw43065; decide +kernel
      have hl : raw43065step0Labels = raw43065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43065 raw43065Labels permutation434 hz
    mixedMoment B raw43065step0 raw43065step0Labels = mixedMoment B raw43065step1 raw43065step1Labels := by
      have ha : raw43065step1 = (fun i j => raw43065step0 (permutation129 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43065step1 raw43065step0; decide +kernel
      have hl : raw43065step1Labels = raw43065step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43065step0 raw43065step0Labels permutation129 permutation6
    _ = mixedMoment B node4173 node4173Labels := by rfl

theorem canonical43066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43066 raw43066Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw43066 raw43066Labels = mixedMoment B raw43066step0 raw43066step0Labels := by
      have ha : raw43066step0 = (fun i j => raw43066 (permutation594 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43066step0 raw43066; decide +kernel
      have hl : raw43066step0Labels = raw43066Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43066 raw43066Labels permutation594 permutation4
    mixedMoment B raw43066step0 raw43066step0Labels = mixedMoment B raw43066step1 raw43066step1Labels := by
      have ha : raw43066step1 = -raw43066step0 := by apply Matrix.ext; change ∀ i j, raw43066step1 i j = -(raw43066step0 i j); unfold raw43066step1 raw43066step0; decide +kernel
      have hl : raw43066step1Labels = raw43066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43066step1 raw43066step1Labels = mixedMoment B raw43066step2 raw43066step2Labels := by
      have ha : raw43066step2 = raw43066step1 := by apply Matrix.ext; unfold raw43066step2 raw43066step1; decide +kernel
      have hl : raw43066step1Labels = labelEmbedding1 ∘ raw43066step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43066step1 raw43066step1Labels raw43066step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

theorem canonical43067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43067 raw43067Labels = mixedMoment B node4150 node4150Labels := by
  calc
    mixedMoment B raw43067 raw43067Labels = mixedMoment B raw43067step0 raw43067step0Labels := by
      have ha : raw43067step0 = (fun i j => raw43067 (permutation666 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43067step0 raw43067; decide +kernel
      have hl : raw43067step0Labels = raw43067Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43067 raw43067Labels permutation666 permutation6
    _ = mixedMoment B node4150 node4150Labels := by rfl

theorem canonical43068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43068 raw43068Labels = mixedMoment B node2140 node2140Labels := by
  calc
    mixedMoment B raw43068 raw43068Labels = mixedMoment B raw43068step0 raw43068step0Labels := by
      have ha : raw43068step0 = (fun i j => raw43068 (permutation506 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43068step0 raw43068; decide +kernel
      have hl : raw43068step0Labels = raw43068Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43068 raw43068Labels permutation506 permutation4
    mixedMoment B raw43068step0 raw43068step0Labels = mixedMoment B raw43068step1 raw43068step1Labels := by
      have ha : raw43068step1 = -raw43068step0 := by apply Matrix.ext; change ∀ i j, raw43068step1 i j = -(raw43068step0 i j); unfold raw43068step1 raw43068step0; decide +kernel
      have hl : raw43068step1Labels = raw43068step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43068step1 raw43068step1Labels = mixedMoment B raw43068step2 raw43068step2Labels := by
      have ha : raw43068step2 = raw43068step1 := by apply Matrix.ext; unfold raw43068step2 raw43068step1; decide +kernel
      have hl : raw43068step1Labels = labelEmbedding1 ∘ raw43068step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43068step1 raw43068step1Labels raw43068step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2140 node2140Labels := by rfl

theorem canonical43069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43069 raw43069Labels = mixedMoment B node4663 node4663Labels := by
  calc
    mixedMoment B raw43069 raw43069Labels = mixedMoment B raw43069step0 raw43069step0Labels := by
      have ha : raw43069step0 = (fun i j => raw43069 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43069step0 raw43069; decide +kernel
      have hl : raw43069step0Labels = raw43069Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43069 raw43069Labels permutation514 permutation6
    _ = mixedMoment B node4663 node4663Labels := by rfl

theorem canonical43070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43070 raw43070Labels = mixedMoment B node3510 node3510Labels := by
  calc
    mixedMoment B raw43070 raw43070Labels = mixedMoment B raw43070step0 raw43070step0Labels := by
      have ha : raw43070step0 = (fun i j => raw43070 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw43070step0 raw43070; decide +kernel
      have hl : raw43070step0Labels = raw43070Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43070 raw43070Labels permutation683 permutation2
    mixedMoment B raw43070step0 raw43070step0Labels = mixedMoment B raw43070step1 raw43070step1Labels := by
      have ha : raw43070step1 = -raw43070step0 := by apply Matrix.ext; change ∀ i j, raw43070step1 i j = -(raw43070step0 i j); unfold raw43070step1 raw43070step0; decide +kernel
      have hl : raw43070step1Labels = raw43070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43070step1 raw43070step1Labels = mixedMoment B raw43070step2 raw43070step2Labels := by
      have ha : raw43070step2 = raw43070step1 := by apply Matrix.ext; unfold raw43070step2 raw43070step1; decide +kernel
      have hl : raw43070step1Labels = labelEmbedding1 ∘ raw43070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43070step1 raw43070step1Labels raw43070step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3510 node3510Labels := by rfl

theorem canonical43071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43071 raw43071Labels = mixedMoment B node4956 node4956Labels := by
  calc
    mixedMoment B raw43071 raw43071Labels = mixedMoment B raw43071step0 raw43071step0Labels := by
      have ha : raw43071step0 = (fun i j => raw43071 (permutation659 i) (permutation7 j)) := by apply Matrix.ext; unfold raw43071step0 raw43071; decide +kernel
      have hl : raw43071step0Labels = raw43071Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43071 raw43071Labels permutation659 permutation7
    mixedMoment B raw43071step0 raw43071step0Labels = mixedMoment B raw43071step1 raw43071step1Labels := by
      have ha : raw43071step1 = raw43071step0 := by apply Matrix.ext; unfold raw43071step1 raw43071step0; decide +kernel
      have hl : raw43071step0Labels = labelEmbedding6 ∘ raw43071step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43071step0 raw43071step0Labels raw43071step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4956 node4956Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2848 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2848) =
      Integer.Sparse.eval keyMomentRow2848 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2848).leftCharge (GramAssembly.key 2848).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3832) := by
    have ha : gramCharges (GramAssembly.key 2848).leftCharge (GramAssembly.key 2848).rightCharge = raw43008 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43008Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43008 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2848).leftCharge (GramAssembly.key 2848).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5379) := by
    have ha : gramCharges (GramAssembly.key 2848).leftCharge (GramAssembly.key 2848).rightCharge = raw43009 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43009Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43009 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2848).leftCharge (GramAssembly.key 2848).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2848).leftCharge (GramAssembly.key 2848).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2848, Integer.Sparse.eval]
  ring

theorem keyMoment2849 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2849) =
      Integer.Sparse.eval keyMomentRow2849 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2849).leftCharge (GramAssembly.key 2849).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4024) := by
    have ha : gramCharges (GramAssembly.key 2849).leftCharge (GramAssembly.key 2849).rightCharge = raw43010 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43010Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43010 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2849).leftCharge (GramAssembly.key 2849).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5445) := by
    have ha : gramCharges (GramAssembly.key 2849).leftCharge (GramAssembly.key 2849).rightCharge = raw43011 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43011Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43011 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2849).leftCharge (GramAssembly.key 2849).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2849).leftCharge (GramAssembly.key 2849).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2849, Integer.Sparse.eval]
  ring

theorem keyMoment2850 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2850) =
      Integer.Sparse.eval keyMomentRow2850 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2850).leftCharge (GramAssembly.key 2850).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3535) := by
    have ha : gramCharges (GramAssembly.key 2850).leftCharge (GramAssembly.key 2850).rightCharge = raw43012 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43012Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43012 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2850).leftCharge (GramAssembly.key 2850).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5266) := by
    have ha : gramCharges (GramAssembly.key 2850).leftCharge (GramAssembly.key 2850).rightCharge = raw43013 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43013Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43013 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2850).leftCharge (GramAssembly.key 2850).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2850).leftCharge (GramAssembly.key 2850).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2850, Integer.Sparse.eval]
  ring

theorem keyMoment2851 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2851) =
      Integer.Sparse.eval keyMomentRow2851 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2851).leftCharge (GramAssembly.key 2851).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3294) := by
    have ha : gramCharges (GramAssembly.key 2851).leftCharge (GramAssembly.key 2851).rightCharge = raw43014 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43014Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43014 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2851).leftCharge (GramAssembly.key 2851).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4603) := by
    have ha : gramCharges (GramAssembly.key 2851).leftCharge (GramAssembly.key 2851).rightCharge = raw43015 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43015Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43015 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2851).leftCharge (GramAssembly.key 2851).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2851).leftCharge (GramAssembly.key 2851).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2851, Integer.Sparse.eval]
  ring

theorem keyMoment2852 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2852) =
      Integer.Sparse.eval keyMomentRow2852 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2852).leftCharge (GramAssembly.key 2852).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3290) := by
    have ha : gramCharges (GramAssembly.key 2852).leftCharge (GramAssembly.key 2852).rightCharge = raw43016 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43016Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43016 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2852).leftCharge (GramAssembly.key 2852).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4590) := by
    have ha : gramCharges (GramAssembly.key 2852).leftCharge (GramAssembly.key 2852).rightCharge = raw43017 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43017Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43017 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2852).leftCharge (GramAssembly.key 2852).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2852).leftCharge (GramAssembly.key 2852).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2852, Integer.Sparse.eval]
  ring

theorem keyMoment2853 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2853) =
      Integer.Sparse.eval keyMomentRow2853 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2853).leftCharge (GramAssembly.key 2853).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3516) := by
    have ha : gramCharges (GramAssembly.key 2853).leftCharge (GramAssembly.key 2853).rightCharge = raw43018 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43018Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43018 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2853).leftCharge (GramAssembly.key 2853).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5129) := by
    have ha : gramCharges (GramAssembly.key 2853).leftCharge (GramAssembly.key 2853).rightCharge = raw43019 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43019Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43019 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2853).leftCharge (GramAssembly.key 2853).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2853).leftCharge (GramAssembly.key 2853).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2853, Integer.Sparse.eval]
  ring

theorem keyMoment2854 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2854) =
      Integer.Sparse.eval keyMomentRow2854 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2854).leftCharge (GramAssembly.key 2854).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3291) := by
    have ha : gramCharges (GramAssembly.key 2854).leftCharge (GramAssembly.key 2854).rightCharge = raw43020 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43020Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43020 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2854).leftCharge (GramAssembly.key 2854).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4591) := by
    have ha : gramCharges (GramAssembly.key 2854).leftCharge (GramAssembly.key 2854).rightCharge = raw43021 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43021Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43021 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2854).leftCharge (GramAssembly.key 2854).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2854).leftCharge (GramAssembly.key 2854).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2854, Integer.Sparse.eval]
  ring

theorem keyMoment2855 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2855) =
      Integer.Sparse.eval keyMomentRow2855 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2855).leftCharge (GramAssembly.key 2855).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3835) := by
    have ha : gramCharges (GramAssembly.key 2855).leftCharge (GramAssembly.key 2855).rightCharge = raw43022 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43022Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43022 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2855).leftCharge (GramAssembly.key 2855).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5377) := by
    have ha : gramCharges (GramAssembly.key 2855).leftCharge (GramAssembly.key 2855).rightCharge = raw43023 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43023Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43023 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2855).leftCharge (GramAssembly.key 2855).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2855).leftCharge (GramAssembly.key 2855).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2855, Integer.Sparse.eval]
  ring

theorem keyMoment2856 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2856) =
      Integer.Sparse.eval keyMomentRow2856 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2856).leftCharge (GramAssembly.key 2856).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3297) := by
    have ha : gramCharges (GramAssembly.key 2856).leftCharge (GramAssembly.key 2856).rightCharge = raw43024 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43024Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43024 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2856).leftCharge (GramAssembly.key 2856).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4593) := by
    have ha : gramCharges (GramAssembly.key 2856).leftCharge (GramAssembly.key 2856).rightCharge = raw43025 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43025Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43025 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2856).leftCharge (GramAssembly.key 2856).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2856).leftCharge (GramAssembly.key 2856).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2856, Integer.Sparse.eval]
  ring

theorem keyMoment2857 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2857) =
      Integer.Sparse.eval keyMomentRow2857 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2857).leftCharge (GramAssembly.key 2857).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2235) := by
    have ha : gramCharges (GramAssembly.key 2857).leftCharge (GramAssembly.key 2857).rightCharge = raw43026 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43026Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43026 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2857).leftCharge (GramAssembly.key 2857).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4886) := by
    have ha : gramCharges (GramAssembly.key 2857).leftCharge (GramAssembly.key 2857).rightCharge = raw43027 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43027Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43027 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2857).leftCharge (GramAssembly.key 2857).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2857).leftCharge (GramAssembly.key 2857).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2857, Integer.Sparse.eval]
  ring

theorem keyMoment2858 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2858) =
      Integer.Sparse.eval keyMomentRow2858 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2858).leftCharge (GramAssembly.key 2858).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2187) := by
    have ha : gramCharges (GramAssembly.key 2858).leftCharge (GramAssembly.key 2858).rightCharge = raw43028 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43028Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43028 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2858).leftCharge (GramAssembly.key 2858).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4830) := by
    have ha : gramCharges (GramAssembly.key 2858).leftCharge (GramAssembly.key 2858).rightCharge = raw43029 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43029Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43029 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2858).leftCharge (GramAssembly.key 2858).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2858).leftCharge (GramAssembly.key 2858).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2858, Integer.Sparse.eval]
  ring

theorem keyMoment2859 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2859) =
      Integer.Sparse.eval keyMomentRow2859 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2859).leftCharge (GramAssembly.key 2859).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2233) := by
    have ha : gramCharges (GramAssembly.key 2859).leftCharge (GramAssembly.key 2859).rightCharge = raw43030 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43030Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43030 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2859).leftCharge (GramAssembly.key 2859).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4885) := by
    have ha : gramCharges (GramAssembly.key 2859).leftCharge (GramAssembly.key 2859).rightCharge = raw43031 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43031Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43031 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2859).leftCharge (GramAssembly.key 2859).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2859).leftCharge (GramAssembly.key 2859).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2859, Integer.Sparse.eval]
  ring

theorem keyMoment2860 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2860) =
      Integer.Sparse.eval keyMomentRow2860 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2860).leftCharge (GramAssembly.key 2860).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2232) := by
    have ha : gramCharges (GramAssembly.key 2860).leftCharge (GramAssembly.key 2860).rightCharge = raw43032 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43032Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43032 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2860).leftCharge (GramAssembly.key 2860).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4863) := by
    have ha : gramCharges (GramAssembly.key 2860).leftCharge (GramAssembly.key 2860).rightCharge = raw43033 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43033Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43033 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2860).leftCharge (GramAssembly.key 2860).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2860).leftCharge (GramAssembly.key 2860).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2860, Integer.Sparse.eval]
  ring

theorem keyMoment2861 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2861) =
      Integer.Sparse.eval keyMomentRow2861 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2861).leftCharge (GramAssembly.key 2861).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3221) := by
    have ha : gramCharges (GramAssembly.key 2861).leftCharge (GramAssembly.key 2861).rightCharge = raw43034 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43034Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43034 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2861).leftCharge (GramAssembly.key 2861).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4885) := by
    have ha : gramCharges (GramAssembly.key 2861).leftCharge (GramAssembly.key 2861).rightCharge = raw43035 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43035Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43035 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2861).leftCharge (GramAssembly.key 2861).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2861).leftCharge (GramAssembly.key 2861).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2861, Integer.Sparse.eval]
  ring

theorem keyMoment2862 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2862) =
      Integer.Sparse.eval keyMomentRow2862 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2862).leftCharge (GramAssembly.key 2862).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3059) := by
    have ha : gramCharges (GramAssembly.key 2862).leftCharge (GramAssembly.key 2862).rightCharge = raw43036 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43036Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43036 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2862).leftCharge (GramAssembly.key 2862).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5277) := by
    have ha : gramCharges (GramAssembly.key 2862).leftCharge (GramAssembly.key 2862).rightCharge = raw43037 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43037Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43037 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2862).leftCharge (GramAssembly.key 2862).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2862).leftCharge (GramAssembly.key 2862).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2862, Integer.Sparse.eval]
  ring

theorem keyMoment2863 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2863) =
      Integer.Sparse.eval keyMomentRow2863 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2863).leftCharge (GramAssembly.key 2863).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2690) := by
    have ha : gramCharges (GramAssembly.key 2863).leftCharge (GramAssembly.key 2863).rightCharge = raw43038 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43038Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43038 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2863).leftCharge (GramAssembly.key 2863).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4975) := by
    have ha : gramCharges (GramAssembly.key 2863).leftCharge (GramAssembly.key 2863).rightCharge = raw43039 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43039Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43039 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2863).leftCharge (GramAssembly.key 2863).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2863).leftCharge (GramAssembly.key 2863).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2863, Integer.Sparse.eval]
  ring

theorem keyMoment2864 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2864) =
      Integer.Sparse.eval keyMomentRow2864 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2864).leftCharge (GramAssembly.key 2864).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3058) := by
    have ha : gramCharges (GramAssembly.key 2864).leftCharge (GramAssembly.key 2864).rightCharge = raw43040 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43040Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43040 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2864).leftCharge (GramAssembly.key 2864).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5097) := by
    have ha : gramCharges (GramAssembly.key 2864).leftCharge (GramAssembly.key 2864).rightCharge = raw43041 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43041Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43041 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2864).leftCharge (GramAssembly.key 2864).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2864).leftCharge (GramAssembly.key 2864).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2864, Integer.Sparse.eval]
  ring

theorem keyMoment2865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2865) =
      Integer.Sparse.eval keyMomentRow2865 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2865).leftCharge (GramAssembly.key 2865).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2688) := by
    have ha : gramCharges (GramAssembly.key 2865).leftCharge (GramAssembly.key 2865).rightCharge = raw43042 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43042Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43042 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2865).leftCharge (GramAssembly.key 2865).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4540) := by
    have ha : gramCharges (GramAssembly.key 2865).leftCharge (GramAssembly.key 2865).rightCharge = raw43043 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43043Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43043 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2865).leftCharge (GramAssembly.key 2865).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2865).leftCharge (GramAssembly.key 2865).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2865, Integer.Sparse.eval]
  ring

theorem keyMoment2866 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2866) =
      Integer.Sparse.eval keyMomentRow2866 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2866).leftCharge (GramAssembly.key 2866).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1700) := by
    have ha : gramCharges (GramAssembly.key 2866).leftCharge (GramAssembly.key 2866).rightCharge = raw43044 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43044Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43044 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2866).leftCharge (GramAssembly.key 2866).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4494) := by
    have ha : gramCharges (GramAssembly.key 2866).leftCharge (GramAssembly.key 2866).rightCharge = raw43045 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43045Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43045 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2866).leftCharge (GramAssembly.key 2866).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2866).leftCharge (GramAssembly.key 2866).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2866, Integer.Sparse.eval]
  ring

theorem keyMoment2867 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2867) =
      Integer.Sparse.eval keyMomentRow2867 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2867).leftCharge (GramAssembly.key 2867).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1699) := by
    have ha : gramCharges (GramAssembly.key 2867).leftCharge (GramAssembly.key 2867).rightCharge = raw43046 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43046Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43046 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2867).leftCharge (GramAssembly.key 2867).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4473) := by
    have ha : gramCharges (GramAssembly.key 2867).leftCharge (GramAssembly.key 2867).rightCharge = raw43047 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43047Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43047 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2867).leftCharge (GramAssembly.key 2867).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2867).leftCharge (GramAssembly.key 2867).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2867, Integer.Sparse.eval]
  ring

theorem keyMoment2868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2868) =
      Integer.Sparse.eval keyMomentRow2868 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2868).leftCharge (GramAssembly.key 2868).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1502) := by
    have ha : gramCharges (GramAssembly.key 2868).leftCharge (GramAssembly.key 2868).rightCharge = raw43048 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43048Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43048 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2868).leftCharge (GramAssembly.key 2868).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4169) := by
    have ha : gramCharges (GramAssembly.key 2868).leftCharge (GramAssembly.key 2868).rightCharge = raw43049 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43049Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43049 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2868).leftCharge (GramAssembly.key 2868).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2868).leftCharge (GramAssembly.key 2868).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2868, Integer.Sparse.eval]
  ring

theorem keyMoment2869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2869) =
      Integer.Sparse.eval keyMomentRow2869 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2869).leftCharge (GramAssembly.key 2869).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1501) := by
    have ha : gramCharges (GramAssembly.key 2869).leftCharge (GramAssembly.key 2869).rightCharge = raw43050 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43050Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43050 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2869).leftCharge (GramAssembly.key 2869).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4149) := by
    have ha : gramCharges (GramAssembly.key 2869).leftCharge (GramAssembly.key 2869).rightCharge = raw43051 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43051Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43051 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2869).leftCharge (GramAssembly.key 2869).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2869).leftCharge (GramAssembly.key 2869).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2869, Integer.Sparse.eval]
  ring

theorem keyMoment2870 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2870) =
      Integer.Sparse.eval keyMomentRow2870 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2870).leftCharge (GramAssembly.key 2870).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2192) := by
    have ha : gramCharges (GramAssembly.key 2870).leftCharge (GramAssembly.key 2870).rightCharge = raw43052 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43052Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43052 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2870).leftCharge (GramAssembly.key 2870).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4815) := by
    have ha : gramCharges (GramAssembly.key 2870).leftCharge (GramAssembly.key 2870).rightCharge = raw43053 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43053Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43053 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2870).leftCharge (GramAssembly.key 2870).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2870).leftCharge (GramAssembly.key 2870).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2870, Integer.Sparse.eval]
  ring

theorem keyMoment2871 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2871) =
      Integer.Sparse.eval keyMomentRow2871 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2871).leftCharge (GramAssembly.key 2871).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2240) := by
    have ha : gramCharges (GramAssembly.key 2871).leftCharge (GramAssembly.key 2871).rightCharge = raw43054 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43054Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43054 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2871).leftCharge (GramAssembly.key 2871).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4851) := by
    have ha : gramCharges (GramAssembly.key 2871).leftCharge (GramAssembly.key 2871).rightCharge = raw43055 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43055Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43055 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2871).leftCharge (GramAssembly.key 2871).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2871).leftCharge (GramAssembly.key 2871).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2871, Integer.Sparse.eval]
  ring

theorem keyMoment2872 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2872) =
      Integer.Sparse.eval keyMomentRow2872 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2872).leftCharge (GramAssembly.key 2872).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2142) := by
    have ha : gramCharges (GramAssembly.key 2872).leftCharge (GramAssembly.key 2872).rightCharge = raw43056 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43056Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43056 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2872).leftCharge (GramAssembly.key 2872).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4677) := by
    have ha : gramCharges (GramAssembly.key 2872).leftCharge (GramAssembly.key 2872).rightCharge = raw43057 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43057Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43057 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2872).leftCharge (GramAssembly.key 2872).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2872).leftCharge (GramAssembly.key 2872).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2872, Integer.Sparse.eval]
  ring

theorem keyMoment2873 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2873) =
      Integer.Sparse.eval keyMomentRow2873 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2873).leftCharge (GramAssembly.key 2873).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3554) := by
    have ha : gramCharges (GramAssembly.key 2873).leftCharge (GramAssembly.key 2873).rightCharge = raw43058 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43058Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43058 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2873).leftCharge (GramAssembly.key 2873).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4964) := by
    have ha : gramCharges (GramAssembly.key 2873).leftCharge (GramAssembly.key 2873).rightCharge = raw43059 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43059Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43059 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2873).leftCharge (GramAssembly.key 2873).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2873).leftCharge (GramAssembly.key 2873).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2873, Integer.Sparse.eval]
  ring

theorem keyMoment2874 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2874) =
      Integer.Sparse.eval keyMomentRow2874 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2874).leftCharge (GramAssembly.key 2874).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3257) := by
    have ha : gramCharges (GramAssembly.key 2874).leftCharge (GramAssembly.key 2874).rightCharge = raw43060 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43060Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43060 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2874).leftCharge (GramAssembly.key 2874).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4542) := by
    have ha : gramCharges (GramAssembly.key 2874).leftCharge (GramAssembly.key 2874).rightCharge = raw43061 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43061Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43061 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2874).leftCharge (GramAssembly.key 2874).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2874).leftCharge (GramAssembly.key 2874).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2874, Integer.Sparse.eval]
  ring

theorem keyMoment2875 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2875) =
      Integer.Sparse.eval keyMomentRow2875 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2875).leftCharge (GramAssembly.key 2875).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1709) := by
    have ha : gramCharges (GramAssembly.key 2875).leftCharge (GramAssembly.key 2875).rightCharge = raw43062 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43062Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43062 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2875).leftCharge (GramAssembly.key 2875).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4474) := by
    have ha : gramCharges (GramAssembly.key 2875).leftCharge (GramAssembly.key 2875).rightCharge = raw43063 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43063Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43063 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2875).leftCharge (GramAssembly.key 2875).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2875).leftCharge (GramAssembly.key 2875).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2875, Integer.Sparse.eval]
  ring

theorem keyMoment2876 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2876) =
      Integer.Sparse.eval keyMomentRow2876 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2876).leftCharge (GramAssembly.key 2876).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1508) := by
    have ha : gramCharges (GramAssembly.key 2876).leftCharge (GramAssembly.key 2876).rightCharge = raw43064 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43064Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43064 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2876).leftCharge (GramAssembly.key 2876).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4173) := by
    have ha : gramCharges (GramAssembly.key 2876).leftCharge (GramAssembly.key 2876).rightCharge = raw43065 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43065Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43065 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2876).leftCharge (GramAssembly.key 2876).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2876).leftCharge (GramAssembly.key 2876).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2876, Integer.Sparse.eval]
  ring

theorem keyMoment2877 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2877) =
      Integer.Sparse.eval keyMomentRow2877 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2877).leftCharge (GramAssembly.key 2877).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1504) := by
    have ha : gramCharges (GramAssembly.key 2877).leftCharge (GramAssembly.key 2877).rightCharge = raw43066 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43066Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43066 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2877).leftCharge (GramAssembly.key 2877).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4150) := by
    have ha : gramCharges (GramAssembly.key 2877).leftCharge (GramAssembly.key 2877).rightCharge = raw43067 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43067Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43067 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2877).leftCharge (GramAssembly.key 2877).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2877).leftCharge (GramAssembly.key 2877).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2877, Integer.Sparse.eval]
  ring

theorem keyMoment2878 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2878) =
      Integer.Sparse.eval keyMomentRow2878 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2878).leftCharge (GramAssembly.key 2878).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2140) := by
    have ha : gramCharges (GramAssembly.key 2878).leftCharge (GramAssembly.key 2878).rightCharge = raw43068 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43068Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43068 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2878).leftCharge (GramAssembly.key 2878).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4663) := by
    have ha : gramCharges (GramAssembly.key 2878).leftCharge (GramAssembly.key 2878).rightCharge = raw43069 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43069Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43069 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2878).leftCharge (GramAssembly.key 2878).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2878).leftCharge (GramAssembly.key 2878).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2878, Integer.Sparse.eval]
  ring

theorem keyMoment2879 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2879) =
      Integer.Sparse.eval keyMomentRow2879 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2879).leftCharge (GramAssembly.key 2879).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3510) := by
    have ha : gramCharges (GramAssembly.key 2879).leftCharge (GramAssembly.key 2879).rightCharge = raw43070 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43070Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43070 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2879).leftCharge (GramAssembly.key 2879).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4956) := by
    have ha : gramCharges (GramAssembly.key 2879).leftCharge (GramAssembly.key 2879).rightCharge = raw43071 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43071Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43071 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2879).leftCharge (GramAssembly.key 2879).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2879).leftCharge (GramAssembly.key 2879).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2879, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2848 : keyMomentRows (2848 : Fin 2886) =
    keyMomentRow2848 := by decide +kernel

theorem keyMomentRowsAt2849 : keyMomentRows (2849 : Fin 2886) =
    keyMomentRow2849 := by decide +kernel

theorem keyMomentRowsAt2850 : keyMomentRows (2850 : Fin 2886) =
    keyMomentRow2850 := by decide +kernel

theorem keyMomentRowsAt2851 : keyMomentRows (2851 : Fin 2886) =
    keyMomentRow2851 := by decide +kernel

theorem keyMomentRowsAt2852 : keyMomentRows (2852 : Fin 2886) =
    keyMomentRow2852 := by decide +kernel

theorem keyMomentRowsAt2853 : keyMomentRows (2853 : Fin 2886) =
    keyMomentRow2853 := by decide +kernel

theorem keyMomentRowsAt2854 : keyMomentRows (2854 : Fin 2886) =
    keyMomentRow2854 := by decide +kernel

theorem keyMomentRowsAt2855 : keyMomentRows (2855 : Fin 2886) =
    keyMomentRow2855 := by decide +kernel

theorem keyMomentRowsAt2856 : keyMomentRows (2856 : Fin 2886) =
    keyMomentRow2856 := by decide +kernel

theorem keyMomentRowsAt2857 : keyMomentRows (2857 : Fin 2886) =
    keyMomentRow2857 := by decide +kernel

theorem keyMomentRowsAt2858 : keyMomentRows (2858 : Fin 2886) =
    keyMomentRow2858 := by decide +kernel

theorem keyMomentRowsAt2859 : keyMomentRows (2859 : Fin 2886) =
    keyMomentRow2859 := by decide +kernel

theorem keyMomentRowsAt2860 : keyMomentRows (2860 : Fin 2886) =
    keyMomentRow2860 := by decide +kernel

theorem keyMomentRowsAt2861 : keyMomentRows (2861 : Fin 2886) =
    keyMomentRow2861 := by decide +kernel

theorem keyMomentRowsAt2862 : keyMomentRows (2862 : Fin 2886) =
    keyMomentRow2862 := by decide +kernel

theorem keyMomentRowsAt2863 : keyMomentRows (2863 : Fin 2886) =
    keyMomentRow2863 := by decide +kernel

theorem keyMomentRowsAt2864 : keyMomentRows (2864 : Fin 2886) =
    keyMomentRow2864 := by decide +kernel

theorem keyMomentRowsAt2865 : keyMomentRows (2865 : Fin 2886) =
    keyMomentRow2865 := by decide +kernel

theorem keyMomentRowsAt2866 : keyMomentRows (2866 : Fin 2886) =
    keyMomentRow2866 := by decide +kernel

theorem keyMomentRowsAt2867 : keyMomentRows (2867 : Fin 2886) =
    keyMomentRow2867 := by decide +kernel

theorem keyMomentRowsAt2868 : keyMomentRows (2868 : Fin 2886) =
    keyMomentRow2868 := by decide +kernel

theorem keyMomentRowsAt2869 : keyMomentRows (2869 : Fin 2886) =
    keyMomentRow2869 := by decide +kernel

theorem keyMomentRowsAt2870 : keyMomentRows (2870 : Fin 2886) =
    keyMomentRow2870 := by decide +kernel

theorem keyMomentRowsAt2871 : keyMomentRows (2871 : Fin 2886) =
    keyMomentRow2871 := by decide +kernel

theorem keyMomentRowsAt2872 : keyMomentRows (2872 : Fin 2886) =
    keyMomentRow2872 := by decide +kernel

theorem keyMomentRowsAt2873 : keyMomentRows (2873 : Fin 2886) =
    keyMomentRow2873 := by decide +kernel

theorem keyMomentRowsAt2874 : keyMomentRows (2874 : Fin 2886) =
    keyMomentRow2874 := by decide +kernel

theorem keyMomentRowsAt2875 : keyMomentRows (2875 : Fin 2886) =
    keyMomentRow2875 := by decide +kernel

theorem keyMomentRowsAt2876 : keyMomentRows (2876 : Fin 2886) =
    keyMomentRow2876 := by decide +kernel

theorem keyMomentRowsAt2877 : keyMomentRows (2877 : Fin 2886) =
    keyMomentRow2877 := by decide +kernel

theorem keyMomentRowsAt2878 : keyMomentRows (2878 : Fin 2886) =
    keyMomentRow2878 := by decide +kernel

theorem keyMomentRowsAt2879 : keyMomentRows (2879 : Fin 2886) =
    keyMomentRow2879 := by decide +kernel

theorem keyMomentChunkSound89_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 89) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2848 ∨ k.val = 2849 ∨ k.val = 2850 ∨ k.val = 2851 ∨ k.val = 2852 ∨ k.val = 2853 ∨ k.val = 2854 ∨ k.val = 2855 ∨ k.val = 2856 ∨ k.val = 2857 ∨ k.val = 2858 ∨ k.val = 2859 ∨ k.val = 2860 ∨ k.val = 2861 ∨ k.val = 2862 ∨ k.val = 2863 ∨ k.val = 2864 ∨ k.val = 2865 ∨ k.val = 2866 ∨ k.val = 2867 ∨ k.val = 2868 ∨ k.val = 2869 ∨ k.val = 2870 ∨ k.val = 2871 ∨ k.val = 2872 ∨ k.val = 2873 ∨ k.val = 2874 ∨ k.val = 2875 ∨ k.val = 2876 ∨ k.val = 2877 ∨ k.val = 2878 ∨ k.val = 2879 := by omega
  rcases heq with h2848 | h2849 | h2850 | h2851 | h2852 | h2853 | h2854 | h2855 | h2856 | h2857 | h2858 | h2859 | h2860 | h2861 | h2862 | h2863 | h2864 | h2865 | h2866 | h2867 | h2868 | h2869 | h2870 | h2871 | h2872 | h2873 | h2874 | h2875 | h2876 | h2877 | h2878 | h2879
  · have he : k = (2848 : Fin 2886) := Fin.ext h2848
    subst k
    rw [keyMomentRowsAt2848]
    exact keyMoment2848 B hB
  · have he : k = (2849 : Fin 2886) := Fin.ext h2849
    subst k
    rw [keyMomentRowsAt2849]
    exact keyMoment2849 B hB
  · have he : k = (2850 : Fin 2886) := Fin.ext h2850
    subst k
    rw [keyMomentRowsAt2850]
    exact keyMoment2850 B hB
  · have he : k = (2851 : Fin 2886) := Fin.ext h2851
    subst k
    rw [keyMomentRowsAt2851]
    exact keyMoment2851 B hB
  · have he : k = (2852 : Fin 2886) := Fin.ext h2852
    subst k
    rw [keyMomentRowsAt2852]
    exact keyMoment2852 B hB
  · have he : k = (2853 : Fin 2886) := Fin.ext h2853
    subst k
    rw [keyMomentRowsAt2853]
    exact keyMoment2853 B hB
  · have he : k = (2854 : Fin 2886) := Fin.ext h2854
    subst k
    rw [keyMomentRowsAt2854]
    exact keyMoment2854 B hB
  · have he : k = (2855 : Fin 2886) := Fin.ext h2855
    subst k
    rw [keyMomentRowsAt2855]
    exact keyMoment2855 B hB
  · have he : k = (2856 : Fin 2886) := Fin.ext h2856
    subst k
    rw [keyMomentRowsAt2856]
    exact keyMoment2856 B hB
  · have he : k = (2857 : Fin 2886) := Fin.ext h2857
    subst k
    rw [keyMomentRowsAt2857]
    exact keyMoment2857 B hB
  · have he : k = (2858 : Fin 2886) := Fin.ext h2858
    subst k
    rw [keyMomentRowsAt2858]
    exact keyMoment2858 B hB
  · have he : k = (2859 : Fin 2886) := Fin.ext h2859
    subst k
    rw [keyMomentRowsAt2859]
    exact keyMoment2859 B hB
  · have he : k = (2860 : Fin 2886) := Fin.ext h2860
    subst k
    rw [keyMomentRowsAt2860]
    exact keyMoment2860 B hB
  · have he : k = (2861 : Fin 2886) := Fin.ext h2861
    subst k
    rw [keyMomentRowsAt2861]
    exact keyMoment2861 B hB
  · have he : k = (2862 : Fin 2886) := Fin.ext h2862
    subst k
    rw [keyMomentRowsAt2862]
    exact keyMoment2862 B hB
  · have he : k = (2863 : Fin 2886) := Fin.ext h2863
    subst k
    rw [keyMomentRowsAt2863]
    exact keyMoment2863 B hB
  · have he : k = (2864 : Fin 2886) := Fin.ext h2864
    subst k
    rw [keyMomentRowsAt2864]
    exact keyMoment2864 B hB
  · have he : k = (2865 : Fin 2886) := Fin.ext h2865
    subst k
    rw [keyMomentRowsAt2865]
    exact keyMoment2865 B hB
  · have he : k = (2866 : Fin 2886) := Fin.ext h2866
    subst k
    rw [keyMomentRowsAt2866]
    exact keyMoment2866 B hB
  · have he : k = (2867 : Fin 2886) := Fin.ext h2867
    subst k
    rw [keyMomentRowsAt2867]
    exact keyMoment2867 B hB
  · have he : k = (2868 : Fin 2886) := Fin.ext h2868
    subst k
    rw [keyMomentRowsAt2868]
    exact keyMoment2868 B hB
  · have he : k = (2869 : Fin 2886) := Fin.ext h2869
    subst k
    rw [keyMomentRowsAt2869]
    exact keyMoment2869 B hB
  · have he : k = (2870 : Fin 2886) := Fin.ext h2870
    subst k
    rw [keyMomentRowsAt2870]
    exact keyMoment2870 B hB
  · have he : k = (2871 : Fin 2886) := Fin.ext h2871
    subst k
    rw [keyMomentRowsAt2871]
    exact keyMoment2871 B hB
  · have he : k = (2872 : Fin 2886) := Fin.ext h2872
    subst k
    rw [keyMomentRowsAt2872]
    exact keyMoment2872 B hB
  · have he : k = (2873 : Fin 2886) := Fin.ext h2873
    subst k
    rw [keyMomentRowsAt2873]
    exact keyMoment2873 B hB
  · have he : k = (2874 : Fin 2886) := Fin.ext h2874
    subst k
    rw [keyMomentRowsAt2874]
    exact keyMoment2874 B hB
  · have he : k = (2875 : Fin 2886) := Fin.ext h2875
    subst k
    rw [keyMomentRowsAt2875]
    exact keyMoment2875 B hB
  · have he : k = (2876 : Fin 2886) := Fin.ext h2876
    subst k
    rw [keyMomentRowsAt2876]
    exact keyMoment2876 B hB
  · have he : k = (2877 : Fin 2886) := Fin.ext h2877
    subst k
    rw [keyMomentRowsAt2877]
    exact keyMoment2877 B hB
  · have he : k = (2878 : Fin 2886) := Fin.ext h2878
    subst k
    rw [keyMomentRowsAt2878]
    exact keyMoment2878 B hB
  · have he : k = (2879 : Fin 2886) := Fin.ext h2879
    subst k
    rw [keyMomentRowsAt2879]
    exact keyMoment2879 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound89_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound89_e_oai
