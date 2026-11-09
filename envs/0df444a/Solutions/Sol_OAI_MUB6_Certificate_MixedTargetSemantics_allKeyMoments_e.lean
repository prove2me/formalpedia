-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.allKeyMoments_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:22:01.779573+00:00
-- url     : https://prove2.me/submissions/26661041-ca08-4f89-a139-a94873f6a3ad

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E111
import Definitions.Def_OAIQ106E112
import Definitions.Def_OAIQ106E114
import Definitions.Def_OAIQ106E130
import Definitions.Def_OAIQ106E137
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E151
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound0_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound10_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound11_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound13_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound14_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound15_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound16_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound17_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound18_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound19_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound1_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound20_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound21_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound22_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound23_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound24_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound25_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound26_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound27_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound28_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound29_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound30_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound31_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound32_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound33_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound34_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound35_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound36_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound37_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound38_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound39_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound3_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound40_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound41_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound42_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound43_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound44_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound45_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound46_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound47_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound48_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound49_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound4_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound50_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound51_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound52_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound53_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound54_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound55_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound56_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound57_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound58_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound59_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound5_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound60_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound61_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound63_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound64_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound65_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound66_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound67_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound68_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound69_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound6_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound70_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound71_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound72_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound73_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound74_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound75_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound76_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound77_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound78_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound79_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound7_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound80_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound81_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound82_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound83_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound84_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound85_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound86_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound87_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound88_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound89_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_keyMomentChunkSound9_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical308
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39514 raw39514Labels = mixedMoment B node159 node159Labels := by
  calc
    mixedMoment B raw39514 raw39514Labels = mixedMoment B raw39514step0 raw39514step0Labels := by
      have hz : ∀ j, raw39514 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39514step0 = (fun i j => raw39514 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39514step0 raw39514; decide +kernel
      have hl : raw39514step0Labels = raw39514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39514 raw39514Labels permutation434 hz
    mixedMoment B raw39514step0 raw39514step0Labels = mixedMoment B raw39514step1 raw39514step1Labels := by
      have hz : ∀ j, raw39514step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39514step1 = (fun i j => raw39514step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39514step1 raw39514step0; decide +kernel
      have hl : raw39514step1Labels = raw39514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39514step0 raw39514step0Labels permutation80 hz
    mixedMoment B raw39514step1 raw39514step1Labels = mixedMoment B raw39514step2 raw39514step2Labels := by
      have hz : ∀ j, raw39514step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39514step2 = (fun i j => raw39514step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39514step2 raw39514step1; decide +kernel
      have hl : raw39514step2Labels = raw39514step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39514step1 raw39514step1Labels permutation14 hz
    mixedMoment B raw39514step2 raw39514step2Labels = mixedMoment B raw39514step3 raw39514step3Labels := by
      have ha : raw39514step3 = (fun i j => raw39514step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39514step3 raw39514step2; decide +kernel
      have hl : raw39514step3Labels = raw39514step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39514step2 raw39514step2Labels permutation6 permutation6
    _ = mixedMoment B node159 node159Labels := by rfl

theorem canonical39515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39515 raw39515Labels = mixedMoment B node388 node388Labels := by
  calc
    mixedMoment B raw39515 raw39515Labels = mixedMoment B raw39515step0 raw39515step0Labels := by
      have hz : ∀ j, raw39515 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39515step0 = (fun i j => raw39515 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39515step0 raw39515; decide +kernel
      have hl : raw39515step0Labels = raw39515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39515 raw39515Labels permutation346 hz
    mixedMoment B raw39515step0 raw39515step0Labels = mixedMoment B raw39515step1 raw39515step1Labels := by
      have hz : ∀ j, raw39515step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39515step1 = (fun i j => raw39515step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39515step1 raw39515step0; decide +kernel
      have hl : raw39515step1Labels = raw39515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39515step0 raw39515step0Labels permutation56 hz
    _ = mixedMoment B node388 node388Labels := by rfl

theorem canonical39516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39516 raw39516Labels = mixedMoment B node148 node148Labels := by
  calc
    mixedMoment B raw39516 raw39516Labels = mixedMoment B raw39516step0 raw39516step0Labels := by
      have hz : ∀ j, raw39516 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39516step0 = (fun i j => raw39516 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39516step0 raw39516; decide +kernel
      have hl : raw39516step0Labels = raw39516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39516 raw39516Labels permutation346 hz
    mixedMoment B raw39516step0 raw39516step0Labels = mixedMoment B raw39516step1 raw39516step1Labels := by
      have hz : ∀ j, raw39516step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39516step1 = (fun i j => raw39516step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39516step1 raw39516step0; decide +kernel
      have hl : raw39516step1Labels = raw39516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39516step0 raw39516step0Labels permutation56 hz
    mixedMoment B raw39516step1 raw39516step1Labels = mixedMoment B raw39516step2 raw39516step2Labels := by
      have ha : raw39516step2 = (fun i j => raw39516step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39516step2 raw39516step1; decide +kernel
      have hl : raw39516step2Labels = raw39516step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39516step1 raw39516step1Labels permutation31 permutation7
    _ = mixedMoment B node148 node148Labels := by rfl

theorem canonical39517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39517 raw39517Labels = mixedMoment B node342 node342Labels := by
  calc
    mixedMoment B raw39517 raw39517Labels = mixedMoment B raw39517step0 raw39517step0Labels := by
      have hz : ∀ j, raw39517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39517step0 = (fun i j => raw39517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39517step0 raw39517; decide +kernel
      have hl : raw39517step0Labels = raw39517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39517 raw39517Labels permutation346 hz
    mixedMoment B raw39517step0 raw39517step0Labels = mixedMoment B raw39517step1 raw39517step1Labels := by
      have hz : ∀ j, raw39517step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39517step1 = (fun i j => raw39517step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39517step1 raw39517step0; decide +kernel
      have hl : raw39517step1Labels = raw39517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39517step0 raw39517step0Labels permutation56 hz
    mixedMoment B raw39517step1 raw39517step1Labels = mixedMoment B raw39517step2 raw39517step2Labels := by
      have ha : raw39517step2 = (fun i j => raw39517step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39517step2 raw39517step1; decide +kernel
      have hl : raw39517step2Labels = raw39517step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39517step1 raw39517step1Labels permutation16 permutation6
    _ = mixedMoment B node342 node342Labels := by rfl

theorem canonical39518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39518 raw39518Labels = mixedMoment B node406 node406Labels := by
  calc
    mixedMoment B raw39518 raw39518Labels = mixedMoment B raw39518step0 raw39518step0Labels := by
      have hz : ∀ j, raw39518 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39518step0 = (fun i j => raw39518 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39518step0 raw39518; decide +kernel
      have hl : raw39518step0Labels = raw39518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39518 raw39518Labels permutation346 hz
    mixedMoment B raw39518step0 raw39518step0Labels = mixedMoment B raw39518step1 raw39518step1Labels := by
      have hz : ∀ j, raw39518step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39518step1 = (fun i j => raw39518step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39518step1 raw39518step0; decide +kernel
      have hl : raw39518step1Labels = raw39518step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39518step0 raw39518step0Labels permutation56 hz
    mixedMoment B raw39518step1 raw39518step1Labels = mixedMoment B raw39518step2 raw39518step2Labels := by
      have ha : raw39518step2 = (fun i j => raw39518step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39518step2 raw39518step1; decide +kernel
      have hl : raw39518step2Labels = raw39518step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39518step1 raw39518step1Labels permutation17 permutation6
    _ = mixedMoment B node406 node406Labels := by rfl

theorem canonical39519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39519 raw39519Labels = mixedMoment B node413 node413Labels := by
  calc
    mixedMoment B raw39519 raw39519Labels = mixedMoment B raw39519step0 raw39519step0Labels := by
      have hz : ∀ j, raw39519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39519step0 = (fun i j => raw39519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39519step0 raw39519; decide +kernel
      have hl : raw39519step0Labels = raw39519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39519 raw39519Labels permutation346 hz
    mixedMoment B raw39519step0 raw39519step0Labels = mixedMoment B raw39519step1 raw39519step1Labels := by
      have hz : ∀ j, raw39519step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39519step1 = (fun i j => raw39519step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39519step1 raw39519step0; decide +kernel
      have hl : raw39519step1Labels = raw39519step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39519step0 raw39519step0Labels permutation56 hz
    mixedMoment B raw39519step1 raw39519step1Labels = mixedMoment B raw39519step2 raw39519step2Labels := by
      have ha : raw39519step2 = (fun i j => raw39519step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39519step2 raw39519step1; decide +kernel
      have hl : raw39519step2Labels = raw39519step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39519step1 raw39519step1Labels permutation12 permutation2
    _ = mixedMoment B node413 node413Labels := by rfl

theorem canonical39520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39520 raw39520Labels = mixedMoment B node416 node416Labels := by
  calc
    mixedMoment B raw39520 raw39520Labels = mixedMoment B raw39520step0 raw39520step0Labels := by
      have hz : ∀ j, raw39520 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39520step0 = (fun i j => raw39520 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39520step0 raw39520; decide +kernel
      have hl : raw39520step0Labels = raw39520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39520 raw39520Labels permutation346 hz
    mixedMoment B raw39520step0 raw39520step0Labels = mixedMoment B raw39520step1 raw39520step1Labels := by
      have hz : ∀ j, raw39520step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39520step1 = (fun i j => raw39520step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39520step1 raw39520step0; decide +kernel
      have hl : raw39520step1Labels = raw39520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39520step0 raw39520step0Labels permutation56 hz
    mixedMoment B raw39520step1 raw39520step1Labels = mixedMoment B raw39520step2 raw39520step2Labels := by
      have ha : raw39520step2 = (fun i j => raw39520step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39520step2 raw39520step1; decide +kernel
      have hl : raw39520step2Labels = raw39520step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39520step1 raw39520step1Labels permutation11 permutation2
    _ = mixedMoment B node416 node416Labels := by rfl

theorem canonical39521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39521 raw39521Labels = mixedMoment B node340 node340Labels := by
  calc
    mixedMoment B raw39521 raw39521Labels = mixedMoment B raw39521step0 raw39521step0Labels := by
      have hz : ∀ j, raw39521 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39521step0 = (fun i j => raw39521 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39521step0 raw39521; decide +kernel
      have hl : raw39521step0Labels = raw39521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39521 raw39521Labels permutation265 hz
    mixedMoment B raw39521step0 raw39521step0Labels = mixedMoment B raw39521step1 raw39521step1Labels := by
      have ha : raw39521step1 = (fun i j => raw39521step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39521step1 raw39521step0; decide +kernel
      have hl : raw39521step1Labels = raw39521step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39521step0 raw39521step0Labels permutation95 permutation6
    _ = mixedMoment B node340 node340Labels := by rfl

theorem canonical39522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39522 raw39522Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw39522 raw39522Labels = mixedMoment B raw39522step0 raw39522step0Labels := by
      have hz : ∀ j, raw39522 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39522step0 = (fun i j => raw39522 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39522step0 raw39522; decide +kernel
      have hl : raw39522step0Labels = raw39522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39522 raw39522Labels permutation265 hz
    mixedMoment B raw39522step0 raw39522step0Labels = mixedMoment B raw39522step1 raw39522step1Labels := by
      have ha : raw39522step1 = (fun i j => raw39522step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39522step1 raw39522step0; decide +kernel
      have hl : raw39522step1Labels = raw39522step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39522step0 raw39522step0Labels permutation37 permutation2
    _ = mixedMoment B node387 node387Labels := by rfl

theorem canonical39523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39523 raw39523Labels = mixedMoment B node328 node328Labels := by
  calc
    mixedMoment B raw39523 raw39523Labels = mixedMoment B raw39523step0 raw39523step0Labels := by
      have hz : ∀ j, raw39523 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39523step0 = (fun i j => raw39523 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39523step0 raw39523; decide +kernel
      have hl : raw39523step0Labels = raw39523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39523 raw39523Labels permutation265 hz
    mixedMoment B raw39523step0 raw39523step0Labels = mixedMoment B raw39523step1 raw39523step1Labels := by
      have ha : raw39523step1 = (fun i j => raw39523step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39523step1 raw39523step0; decide +kernel
      have hl : raw39523step1Labels = raw39523step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39523step0 raw39523step0Labels permutation96 permutation6
    _ = mixedMoment B node328 node328Labels := by rfl

theorem canonical39524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39524 raw39524Labels = mixedMoment B node367 node367Labels := by
  calc
    mixedMoment B raw39524 raw39524Labels = mixedMoment B raw39524step0 raw39524step0Labels := by
      have hz : ∀ j, raw39524 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39524step0 = (fun i j => raw39524 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39524step0 raw39524; decide +kernel
      have hl : raw39524step0Labels = raw39524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39524 raw39524Labels permutation265 hz
    mixedMoment B raw39524step0 raw39524step0Labels = mixedMoment B raw39524step1 raw39524step1Labels := by
      have ha : raw39524step1 = (fun i j => raw39524step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39524step1 raw39524step0; decide +kernel
      have hl : raw39524step1Labels = raw39524step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39524step0 raw39524step0Labels permutation36 permutation2
    _ = mixedMoment B node367 node367Labels := by rfl

theorem canonical39525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39525 raw39525Labels = mixedMoment B node271 node271Labels := by
  calc
    mixedMoment B raw39525 raw39525Labels = mixedMoment B raw39525step0 raw39525step0Labels := by
      have hz : ∀ j, raw39525 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39525step0 = (fun i j => raw39525 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39525step0 raw39525; decide +kernel
      have hl : raw39525step0Labels = raw39525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39525 raw39525Labels permutation520 hz
    mixedMoment B raw39525step0 raw39525step0Labels = mixedMoment B raw39525step1 raw39525step1Labels := by
      have hz : ∀ j, raw39525step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39525step1 = (fun i j => raw39525step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39525step1 raw39525step0; decide +kernel
      have hl : raw39525step1Labels = raw39525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39525step0 raw39525step0Labels permutation104 hz
    mixedMoment B raw39525step1 raw39525step1Labels = mixedMoment B raw39525step2 raw39525step2Labels := by
      have hz : ∀ j, raw39525step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39525step2 = (fun i j => raw39525step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39525step2 raw39525step1; decide +kernel
      have hl : raw39525step2Labels = raw39525step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39525step1 raw39525step1Labels permutation20 hz
    _ = mixedMoment B node271 node271Labels := by rfl

theorem canonical39526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39526 raw39526Labels = mixedMoment B node264 node264Labels := by
  calc
    mixedMoment B raw39526 raw39526Labels = mixedMoment B raw39526step0 raw39526step0Labels := by
      have hz : ∀ j, raw39526 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39526step0 = (fun i j => raw39526 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39526step0 raw39526; decide +kernel
      have hl : raw39526step0Labels = raw39526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39526 raw39526Labels permutation434 hz
    mixedMoment B raw39526step0 raw39526step0Labels = mixedMoment B raw39526step1 raw39526step1Labels := by
      have hz : ∀ j, raw39526step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39526step1 = (fun i j => raw39526step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39526step1 raw39526step0; decide +kernel
      have hl : raw39526step1Labels = raw39526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39526step0 raw39526step0Labels permutation80 hz
    mixedMoment B raw39526step1 raw39526step1Labels = mixedMoment B raw39526step2 raw39526step2Labels := by
      have ha : raw39526step2 = (fun i j => raw39526step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39526step2 raw39526step1; decide +kernel
      have hl : raw39526step2Labels = raw39526step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39526step1 raw39526step1Labels permutation17 permutation6
    _ = mixedMoment B node264 node264Labels := by rfl

theorem canonical39527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39527 raw39527Labels = mixedMoment B node250 node250Labels := by
  calc
    mixedMoment B raw39527 raw39527Labels = mixedMoment B raw39527step0 raw39527step0Labels := by
      have hz : ∀ j, raw39527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39527step0 = (fun i j => raw39527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39527step0 raw39527; decide +kernel
      have hl : raw39527step0Labels = raw39527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39527 raw39527Labels permutation434 hz
    mixedMoment B raw39527step0 raw39527step0Labels = mixedMoment B raw39527step1 raw39527step1Labels := by
      have hz : ∀ j, raw39527step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39527step1 = (fun i j => raw39527step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39527step1 raw39527step0; decide +kernel
      have hl : raw39527step1Labels = raw39527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39527step0 raw39527step0Labels permutation80 hz
    mixedMoment B raw39527step1 raw39527step1Labels = mixedMoment B raw39527step2 raw39527step2Labels := by
      have ha : raw39527step2 = (fun i j => raw39527step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39527step2 raw39527step1; decide +kernel
      have hl : raw39527step2Labels = raw39527step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39527step1 raw39527step1Labels permutation19 permutation6
    _ = mixedMoment B node250 node250Labels := by rfl

theorem canonical39528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39528 raw39528Labels = mixedMoment B node188 node188Labels := by
  calc
    mixedMoment B raw39528 raw39528Labels = mixedMoment B raw39528step0 raw39528step0Labels := by
      have hz : ∀ j, raw39528 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39528step0 = (fun i j => raw39528 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39528step0 raw39528; decide +kernel
      have hl : raw39528step0Labels = raw39528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39528 raw39528Labels permutation434 hz
    mixedMoment B raw39528step0 raw39528step0Labels = mixedMoment B raw39528step1 raw39528step1Labels := by
      have hz : ∀ j, raw39528step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39528step1 = (fun i j => raw39528step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39528step1 raw39528step0; decide +kernel
      have hl : raw39528step1Labels = raw39528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39528step0 raw39528step0Labels permutation80 hz
    mixedMoment B raw39528step1 raw39528step1Labels = mixedMoment B raw39528step2 raw39528step2Labels := by
      have ha : raw39528step2 = (fun i j => raw39528step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39528step2 raw39528step1; decide +kernel
      have hl : raw39528step2Labels = raw39528step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39528step1 raw39528step1Labels permutation19 permutation6
    _ = mixedMoment B node188 node188Labels := by rfl

theorem canonical39529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39529 raw39529Labels = mixedMoment B node228 node228Labels := by
  calc
    mixedMoment B raw39529 raw39529Labels = mixedMoment B raw39529step0 raw39529step0Labels := by
      have hz : ∀ j, raw39529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39529step0 = (fun i j => raw39529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39529step0 raw39529; decide +kernel
      have hl : raw39529step0Labels = raw39529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39529 raw39529Labels permutation346 hz
    mixedMoment B raw39529step0 raw39529step0Labels = mixedMoment B raw39529step1 raw39529step1Labels := by
      have ha : raw39529step1 = (fun i j => raw39529step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39529step1 raw39529step0; decide +kernel
      have hl : raw39529step1Labels = raw39529step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39529step0 raw39529step0Labels permutation73 permutation6
    _ = mixedMoment B node228 node228Labels := by rfl

theorem canonical39530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39530 raw39530Labels = mixedMoment B node225 node225Labels := by
  calc
    mixedMoment B raw39530 raw39530Labels = mixedMoment B raw39530step0 raw39530step0Labels := by
      have hz : ∀ j, raw39530 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39530step0 = (fun i j => raw39530 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39530step0 raw39530; decide +kernel
      have hl : raw39530step0Labels = raw39530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39530 raw39530Labels permutation346 hz
    mixedMoment B raw39530step0 raw39530step0Labels = mixedMoment B raw39530step1 raw39530step1Labels := by
      have ha : raw39530step1 = (fun i j => raw39530step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39530step1 raw39530step0; decide +kernel
      have hl : raw39530step1Labels = raw39530step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39530step0 raw39530step0Labels permutation41 permutation7
    mixedMoment B raw39530step1 raw39530step1Labels = mixedMoment B raw39530step2 raw39530step2Labels := by
      have ha : raw39530step2 = -raw39530step1 := by apply Matrix.ext; change ∀ i j, raw39530step2 i j = -(raw39530step1 i j); unfold raw39530step2 raw39530step1; decide +kernel
      have hl : raw39530step2Labels = raw39530step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node225 node225Labels := by rfl

theorem canonical39531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39531 raw39531Labels = mixedMoment B node181 node181Labels := by
  calc
    mixedMoment B raw39531 raw39531Labels = mixedMoment B raw39531step0 raw39531step0Labels := by
      have hz : ∀ j, raw39531 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39531step0 = (fun i j => raw39531 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39531step0 raw39531; decide +kernel
      have hl : raw39531step0Labels = raw39531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39531 raw39531Labels permutation346 hz
    mixedMoment B raw39531step0 raw39531step0Labels = mixedMoment B raw39531step1 raw39531step1Labels := by
      have ha : raw39531step1 = (fun i j => raw39531step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39531step1 raw39531step0; decide +kernel
      have hl : raw39531step1Labels = raw39531step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39531step0 raw39531step0Labels permutation77 permutation6
    _ = mixedMoment B node181 node181Labels := by rfl

theorem canonical39532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39532 raw39532Labels = mixedMoment B node170 node170Labels := by
  calc
    mixedMoment B raw39532 raw39532Labels = mixedMoment B raw39532step0 raw39532step0Labels := by
      have hz : ∀ j, raw39532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39532step0 = (fun i j => raw39532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39532step0 raw39532; decide +kernel
      have hl : raw39532step0Labels = raw39532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39532 raw39532Labels permutation346 hz
    mixedMoment B raw39532step0 raw39532step0Labels = mixedMoment B raw39532step1 raw39532step1Labels := by
      have ha : raw39532step1 = (fun i j => raw39532step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39532step1 raw39532step0; decide +kernel
      have hl : raw39532step1Labels = raw39532step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39532step0 raw39532step0Labels permutation79 permutation6
    _ = mixedMoment B node170 node170Labels := by rfl

theorem canonical39533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39533 raw39533Labels = mixedMoment B node194 node194Labels := by
  calc
    mixedMoment B raw39533 raw39533Labels = mixedMoment B raw39533step0 raw39533step0Labels := by
      have hz : ∀ j, raw39533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39533step0 = (fun i j => raw39533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39533step0 raw39533; decide +kernel
      have hl : raw39533step0Labels = raw39533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39533 raw39533Labels permutation346 hz
    mixedMoment B raw39533step0 raw39533step0Labels = mixedMoment B raw39533step1 raw39533step1Labels := by
      have ha : raw39533step1 = (fun i j => raw39533step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39533step1 raw39533step0; decide +kernel
      have hl : raw39533step1Labels = raw39533step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39533step0 raw39533step0Labels permutation53 permutation7
    mixedMoment B raw39533step1 raw39533step1Labels = mixedMoment B raw39533step2 raw39533step2Labels := by
      have ha : raw39533step2 = -raw39533step1 := by apply Matrix.ext; change ∀ i j, raw39533step2 i j = -(raw39533step1 i j); unfold raw39533step2 raw39533step1; decide +kernel
      have hl : raw39533step2Labels = raw39533step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node194 node194Labels := by rfl

theorem canonical39534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39534 raw39534Labels = mixedMoment B node225 node225Labels := by
  calc
    mixedMoment B raw39534 raw39534Labels = mixedMoment B raw39534step0 raw39534step0Labels := by
      have hz : ∀ j, raw39534 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39534step0 = (fun i j => raw39534 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39534step0 raw39534; decide +kernel
      have hl : raw39534step0Labels = raw39534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39534 raw39534Labels permutation346 hz
    mixedMoment B raw39534step0 raw39534step0Labels = mixedMoment B raw39534step1 raw39534step1Labels := by
      have ha : raw39534step1 = (fun i j => raw39534step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39534step1 raw39534step0; decide +kernel
      have hl : raw39534step1Labels = raw39534step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39534step0 raw39534step0Labels permutation65 permutation6
    _ = mixedMoment B node225 node225Labels := by rfl

theorem canonical39535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39535 raw39535Labels = mixedMoment B node258 node258Labels := by
  calc
    mixedMoment B raw39535 raw39535Labels = mixedMoment B raw39535step0 raw39535step0Labels := by
      have hz : ∀ j, raw39535 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39535step0 = (fun i j => raw39535 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39535step0 raw39535; decide +kernel
      have hl : raw39535step0Labels = raw39535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39535 raw39535Labels permutation346 hz
    mixedMoment B raw39535step0 raw39535step0Labels = mixedMoment B raw39535step1 raw39535step1Labels := by
      have ha : raw39535step1 = (fun i j => raw39535step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39535step1 raw39535step0; decide +kernel
      have hl : raw39535step1Labels = raw39535step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39535step0 raw39535step0Labels permutation65 permutation6
    _ = mixedMoment B node258 node258Labels := by rfl

theorem canonical39536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39536 raw39536Labels = mixedMoment B node166 node166Labels := by
  calc
    mixedMoment B raw39536 raw39536Labels = mixedMoment B raw39536step0 raw39536step0Labels := by
      have ha : raw39536step0 = (fun i j => raw39536 (permutation345 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39536step0 raw39536; decide +kernel
      have hl : raw39536step0Labels = raw39536Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39536 raw39536Labels permutation345 permutation6
    _ = mixedMoment B node166 node166Labels := by rfl

theorem canonical39537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39537 raw39537Labels = mixedMoment B node208 node208Labels := by
  calc
    mixedMoment B raw39537 raw39537Labels = mixedMoment B raw39537step0 raw39537step0Labels := by
      have ha : raw39537step0 = (fun i j => raw39537 (permutation316 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39537step0 raw39537; decide +kernel
      have hl : raw39537step0Labels = raw39537Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39537 raw39537Labels permutation316 permutation6
    _ = mixedMoment B node208 node208Labels := by rfl

theorem canonical39538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39538 raw39538Labels = mixedMoment B node218 node218Labels := by
  calc
    mixedMoment B raw39538 raw39538Labels = mixedMoment B raw39538step0 raw39538step0Labels := by
      have ha : raw39538step0 = (fun i j => raw39538 (permutation317 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39538step0 raw39538; decide +kernel
      have hl : raw39538step0Labels = raw39538Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39538 raw39538Labels permutation317 permutation6
    _ = mixedMoment B node218 node218Labels := by rfl

theorem canonical39539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39539 raw39539Labels = mixedMoment B node166 node166Labels := by
  calc
    mixedMoment B raw39539 raw39539Labels = mixedMoment B raw39539step0 raw39539step0Labels := by
      have ha : raw39539step0 = (fun i j => raw39539 (permutation197 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39539step0 raw39539; decide +kernel
      have hl : raw39539step0Labels = raw39539Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39539 raw39539Labels permutation197 permutation7
    mixedMoment B raw39539step0 raw39539step0Labels = mixedMoment B raw39539step1 raw39539step1Labels := by
      have ha : raw39539step1 = -raw39539step0 := by apply Matrix.ext; change ∀ i j, raw39539step1 i j = -(raw39539step0 i j); unfold raw39539step1 raw39539step0; decide +kernel
      have hl : raw39539step1Labels = raw39539step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node166 node166Labels := by rfl

theorem canonical39540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39540 raw39540Labels = mixedMoment B node264 node264Labels := by
  calc
    mixedMoment B raw39540 raw39540Labels = mixedMoment B raw39540step0 raw39540step0Labels := by
      have hz : ∀ j, raw39540 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39540step0 = (fun i j => raw39540 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39540step0 raw39540; decide +kernel
      have hl : raw39540step0Labels = raw39540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39540 raw39540Labels permutation520 hz
    mixedMoment B raw39540step0 raw39540step0Labels = mixedMoment B raw39540step1 raw39540step1Labels := by
      have hz : ∀ j, raw39540step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39540step1 = (fun i j => raw39540step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39540step1 raw39540step0; decide +kernel
      have hl : raw39540step1Labels = raw39540step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39540step0 raw39540step0Labels permutation104 hz
    mixedMoment B raw39540step1 raw39540step1Labels = mixedMoment B raw39540step2 raw39540step2Labels := by
      have ha : raw39540step2 = (fun i j => raw39540step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39540step2 raw39540step1; decide +kernel
      have hl : raw39540step2Labels = raw39540step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39540step1 raw39540step1Labels permutation10 permutation2
    _ = mixedMoment B node264 node264Labels := by rfl

theorem canonical39541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39541 raw39541Labels = mixedMoment B node263 node263Labels := by
  calc
    mixedMoment B raw39541 raw39541Labels = mixedMoment B raw39541step0 raw39541step0Labels := by
      have hz : ∀ j, raw39541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39541step0 = (fun i j => raw39541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39541step0 raw39541; decide +kernel
      have hl : raw39541step0Labels = raw39541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39541 raw39541Labels permutation434 hz
    mixedMoment B raw39541step0 raw39541step0Labels = mixedMoment B raw39541step1 raw39541step1Labels := by
      have ha : raw39541step1 = (fun i j => raw39541step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39541step1 raw39541step0; decide +kernel
      have hl : raw39541step1Labels = raw39541step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39541step0 raw39541step0Labels permutation38 permutation2
    _ = mixedMoment B node263 node263Labels := by rfl

theorem canonical39542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39542 raw39542Labels = mixedMoment B node246 node246Labels := by
  calc
    mixedMoment B raw39542 raw39542Labels = mixedMoment B raw39542step0 raw39542step0Labels := by
      have hz : ∀ j, raw39542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39542step0 = (fun i j => raw39542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39542step0 raw39542; decide +kernel
      have hl : raw39542step0Labels = raw39542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39542 raw39542Labels permutation434 hz
    mixedMoment B raw39542step0 raw39542step0Labels = mixedMoment B raw39542step1 raw39542step1Labels := by
      have ha : raw39542step1 = (fun i j => raw39542step0 (permutation47 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39542step1 raw39542step0; decide +kernel
      have hl : raw39542step1Labels = raw39542step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39542step0 raw39542step0Labels permutation47 permutation7
    mixedMoment B raw39542step1 raw39542step1Labels = mixedMoment B raw39542step2 raw39542step2Labels := by
      have ha : raw39542step2 = -raw39542step1 := by apply Matrix.ext; change ∀ i j, raw39542step2 i j = -(raw39542step1 i j); unfold raw39542step2 raw39542step1; decide +kernel
      have hl : raw39542step2Labels = raw39542step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node246 node246Labels := by rfl

theorem canonical39543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39543 raw39543Labels = mixedMoment B node193 node193Labels := by
  calc
    mixedMoment B raw39543 raw39543Labels = mixedMoment B raw39543step0 raw39543step0Labels := by
      have hz : ∀ j, raw39543 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39543step0 = (fun i j => raw39543 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39543step0 raw39543; decide +kernel
      have hl : raw39543step0Labels = raw39543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39543 raw39543Labels permutation434 hz
    mixedMoment B raw39543step0 raw39543step0Labels = mixedMoment B raw39543step1 raw39543step1Labels := by
      have ha : raw39543step1 = (fun i j => raw39543step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39543step1 raw39543step0; decide +kernel
      have hl : raw39543step1Labels = raw39543step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39543step0 raw39543step0Labels permutation46 permutation7
    mixedMoment B raw39543step1 raw39543step1Labels = mixedMoment B raw39543step2 raw39543step2Labels := by
      have ha : raw39543step2 = -raw39543step1 := by apply Matrix.ext; change ∀ i j, raw39543step2 i j = -(raw39543step1 i j); unfold raw39543step2 raw39543step1; decide +kernel
      have hl : raw39543step2Labels = raw39543step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node193 node193Labels := by rfl

theorem canonical39544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39544 raw39544Labels = mixedMoment B node165 node165Labels := by
  calc
    mixedMoment B raw39544 raw39544Labels = mixedMoment B raw39544step0 raw39544step0Labels := by
      have ha : raw39544step0 = (fun i j => raw39544 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39544step0 raw39544; decide +kernel
      have hl : raw39544step0Labels = raw39544Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39544 raw39544Labels permutation214 permutation7
    mixedMoment B raw39544step0 raw39544step0Labels = mixedMoment B raw39544step1 raw39544step1Labels := by
      have ha : raw39544step1 = -raw39544step0 := by apply Matrix.ext; change ∀ i j, raw39544step1 i j = -(raw39544step0 i j); unfold raw39544step1 raw39544step0; decide +kernel
      have hl : raw39544step1Labels = raw39544step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node165 node165Labels := by rfl

theorem canonical39545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39545 raw39545Labels = mixedMoment B node191 node191Labels := by
  calc
    mixedMoment B raw39545 raw39545Labels = mixedMoment B raw39545step0 raw39545step0Labels := by
      have ha : raw39545step0 = (fun i j => raw39545 (permutation255 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39545step0 raw39545; decide +kernel
      have hl : raw39545step0Labels = raw39545Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39545 raw39545Labels permutation255 permutation7
    mixedMoment B raw39545step0 raw39545step0Labels = mixedMoment B raw39545step1 raw39545step1Labels := by
      have ha : raw39545step1 = -raw39545step0 := by apply Matrix.ext; change ∀ i j, raw39545step1 i j = -(raw39545step0 i j); unfold raw39545step1 raw39545step0; decide +kernel
      have hl : raw39545step1Labels = raw39545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node191 node191Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical310
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39706 raw39706Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw39706 raw39706Labels = mixedMoment B raw39706step0 raw39706step0Labels := by
      have hz : ∀ j, raw39706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39706step0 = (fun i j => raw39706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39706step0 raw39706; decide +kernel
      have hl : raw39706step0Labels = raw39706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39706 raw39706Labels permutation346 hz
    mixedMoment B raw39706step0 raw39706step0Labels = mixedMoment B raw39706step1 raw39706step1Labels := by
      have hz : ∀ j, raw39706step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39706step1 = (fun i j => raw39706step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39706step1 raw39706step0; decide +kernel
      have hl : raw39706step1Labels = raw39706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39706step0 raw39706step0Labels permutation56 hz
    mixedMoment B raw39706step1 raw39706step1Labels = mixedMoment B raw39706step2 raw39706step2Labels := by
      have ha : raw39706step2 = (fun i j => raw39706step1 (permutation19 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39706step2 raw39706step1; decide +kernel
      have hl : raw39706step2Labels = raw39706step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39706step1 raw39706step1Labels permutation19 permutation4
    _ = mixedMoment B node496 node496Labels := by rfl

theorem canonical39707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39707 raw39707Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw39707 raw39707Labels = mixedMoment B raw39707step0 raw39707step0Labels := by
      have hz : ∀ j, raw39707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39707step0 = (fun i j => raw39707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39707step0 raw39707; decide +kernel
      have hl : raw39707step0Labels = raw39707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39707 raw39707Labels permutation346 hz
    mixedMoment B raw39707step0 raw39707step0Labels = mixedMoment B raw39707step1 raw39707step1Labels := by
      have hz : ∀ j, raw39707step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39707step1 = (fun i j => raw39707step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39707step1 raw39707step0; decide +kernel
      have hl : raw39707step1Labels = raw39707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39707step0 raw39707step0Labels permutation56 hz
    mixedMoment B raw39707step1 raw39707step1Labels = mixedMoment B raw39707step2 raw39707step2Labels := by
      have ha : raw39707step2 = (fun i j => raw39707step1 (permutation19 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39707step2 raw39707step1; decide +kernel
      have hl : raw39707step2Labels = raw39707step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39707step1 raw39707step1Labels permutation19 permutation4
    _ = mixedMoment B node268 node268Labels := by rfl

theorem canonical39708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39708 raw39708Labels = mixedMoment B node504 node504Labels := by
  calc
    mixedMoment B raw39708 raw39708Labels = mixedMoment B raw39708step0 raw39708step0Labels := by
      have hz : ∀ j, raw39708 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39708step0 = (fun i j => raw39708 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39708step0 raw39708; decide +kernel
      have hl : raw39708step0Labels = raw39708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39708 raw39708Labels permutation265 hz
    mixedMoment B raw39708step0 raw39708step0Labels = mixedMoment B raw39708step1 raw39708step1Labels := by
      have ha : raw39708step1 = (fun i j => raw39708step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39708step1 raw39708step0; decide +kernel
      have hl : raw39708step1Labels = raw39708step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39708step0 raw39708step0Labels permutation32 permutation3
    _ = mixedMoment B node504 node504Labels := by rfl

theorem canonical39709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39709 raw39709Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw39709 raw39709Labels = mixedMoment B raw39709step0 raw39709step0Labels := by
      have hz : ∀ j, raw39709 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39709step0 = (fun i j => raw39709 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39709step0 raw39709; decide +kernel
      have hl : raw39709step0Labels = raw39709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39709 raw39709Labels permutation265 hz
    mixedMoment B raw39709step0 raw39709step0Labels = mixedMoment B raw39709step1 raw39709step1Labels := by
      have ha : raw39709step1 = (fun i j => raw39709step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39709step1 raw39709step0; decide +kernel
      have hl : raw39709step1Labels = raw39709step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39709step0 raw39709step0Labels permutation91 permutation4
    _ = mixedMoment B node467 node467Labels := by rfl

theorem canonical39710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39710 raw39710Labels = mixedMoment B node272 node272Labels := by
  calc
    mixedMoment B raw39710 raw39710Labels = mixedMoment B raw39710step0 raw39710step0Labels := by
      have hz : ∀ j, raw39710 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39710step0 = (fun i j => raw39710 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39710step0 raw39710; decide +kernel
      have hl : raw39710step0Labels = raw39710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39710 raw39710Labels permutation520 hz
    mixedMoment B raw39710step0 raw39710step0Labels = mixedMoment B raw39710step1 raw39710step1Labels := by
      have hz : ∀ j, raw39710step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39710step1 = (fun i j => raw39710step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39710step1 raw39710step0; decide +kernel
      have hl : raw39710step1Labels = raw39710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39710step0 raw39710step0Labels permutation104 hz
    mixedMoment B raw39710step1 raw39710step1Labels = mixedMoment B raw39710step2 raw39710step2Labels := by
      have hz : ∀ j, raw39710step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39710step2 = (fun i j => raw39710step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39710step2 raw39710step1; decide +kernel
      have hl : raw39710step2Labels = raw39710step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39710step1 raw39710step1Labels permutation20 hz
    mixedMoment B raw39710step2 raw39710step2Labels = mixedMoment B raw39710step3 raw39710step3Labels := by
      have ha : raw39710step3 = (fun i j => raw39710step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39710step3 raw39710step2; decide +kernel
      have hl : raw39710step3Labels = raw39710step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39710step2 raw39710step2Labels permutation7 permutation3
    mixedMoment B raw39710step3 raw39710step3Labels = mixedMoment B raw39710step4 raw39710step4Labels := by
      have ha : raw39710step4 = -raw39710step3 := by apply Matrix.ext; change ∀ i j, raw39710step4 i j = -(raw39710step3 i j); unfold raw39710step4 raw39710step3; decide +kernel
      have hl : raw39710step4Labels = raw39710step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node272 node272Labels := by rfl

theorem canonical39711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39711 raw39711Labels = mixedMoment B node469 node469Labels := by
  calc
    mixedMoment B raw39711 raw39711Labels = mixedMoment B raw39711step0 raw39711step0Labels := by
      have hz : ∀ j, raw39711 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39711step0 = (fun i j => raw39711 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39711step0 raw39711; decide +kernel
      have hl : raw39711step0Labels = raw39711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39711 raw39711Labels permutation434 hz
    mixedMoment B raw39711step0 raw39711step0Labels = mixedMoment B raw39711step1 raw39711step1Labels := by
      have hz : ∀ j, raw39711step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39711step1 = (fun i j => raw39711step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39711step1 raw39711step0; decide +kernel
      have hl : raw39711step1Labels = raw39711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39711step0 raw39711step0Labels permutation80 hz
    mixedMoment B raw39711step1 raw39711step1Labels = mixedMoment B raw39711step2 raw39711step2Labels := by
      have ha : raw39711step2 = (fun i j => raw39711step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39711step2 raw39711step1; decide +kernel
      have hl : raw39711step2Labels = raw39711step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39711step1 raw39711step1Labels permutation31 permutation3
    mixedMoment B raw39711step2 raw39711step2Labels = mixedMoment B raw39711step3 raw39711step3Labels := by
      have ha : raw39711step3 = -raw39711step2 := by apply Matrix.ext; change ∀ i j, raw39711step3 i j = -(raw39711step2 i j); unfold raw39711step3 raw39711step2; decide +kernel
      have hl : raw39711step3Labels = raw39711step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node469 node469Labels := by rfl

theorem canonical39712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39712 raw39712Labels = mixedMoment B node516 node516Labels := by
  calc
    mixedMoment B raw39712 raw39712Labels = mixedMoment B raw39712step0 raw39712step0Labels := by
      have hz : ∀ j, raw39712 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39712step0 = (fun i j => raw39712 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39712step0 raw39712; decide +kernel
      have hl : raw39712step0Labels = raw39712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39712 raw39712Labels permutation434 hz
    mixedMoment B raw39712step0 raw39712step0Labels = mixedMoment B raw39712step1 raw39712step1Labels := by
      have hz : ∀ j, raw39712step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39712step1 = (fun i j => raw39712step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39712step1 raw39712step0; decide +kernel
      have hl : raw39712step1Labels = raw39712step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39712step0 raw39712step0Labels permutation80 hz
    mixedMoment B raw39712step1 raw39712step1Labels = mixedMoment B raw39712step2 raw39712step2Labels := by
      have ha : raw39712step2 = (fun i j => raw39712step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39712step2 raw39712step1; decide +kernel
      have hl : raw39712step2Labels = raw39712step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39712step1 raw39712step1Labels permutation8 permutation3
    _ = mixedMoment B node516 node516Labels := by rfl

theorem canonical39713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39713 raw39713Labels = mixedMoment B node410 node410Labels := by
  calc
    mixedMoment B raw39713 raw39713Labels = mixedMoment B raw39713step0 raw39713step0Labels := by
      have hz : ∀ j, raw39713 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39713step0 = (fun i j => raw39713 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39713step0 raw39713; decide +kernel
      have hl : raw39713step0Labels = raw39713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39713 raw39713Labels permutation434 hz
    mixedMoment B raw39713step0 raw39713step0Labels = mixedMoment B raw39713step1 raw39713step1Labels := by
      have hz : ∀ j, raw39713step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39713step1 = (fun i j => raw39713step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39713step1 raw39713step0; decide +kernel
      have hl : raw39713step1Labels = raw39713step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39713step0 raw39713step0Labels permutation80 hz
    mixedMoment B raw39713step1 raw39713step1Labels = mixedMoment B raw39713step2 raw39713step2Labels := by
      have ha : raw39713step2 = (fun i j => raw39713step1 (permutation24 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39713step2 raw39713step1; decide +kernel
      have hl : raw39713step2Labels = raw39713step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39713step1 raw39713step1Labels permutation24 permutation4
    _ = mixedMoment B node410 node410Labels := by rfl

theorem canonical39714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39714 raw39714Labels = mixedMoment B node483 node483Labels := by
  calc
    mixedMoment B raw39714 raw39714Labels = mixedMoment B raw39714step0 raw39714step0Labels := by
      have hz : ∀ j, raw39714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39714step0 = (fun i j => raw39714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39714step0 raw39714; decide +kernel
      have hl : raw39714step0Labels = raw39714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39714 raw39714Labels permutation346 hz
    mixedMoment B raw39714step0 raw39714step0Labels = mixedMoment B raw39714step1 raw39714step1Labels := by
      have ha : raw39714step1 = (fun i j => raw39714step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39714step1 raw39714step0; decide +kernel
      have hl : raw39714step1Labels = raw39714step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39714step0 raw39714step0Labels permutation151 permutation3
    mixedMoment B raw39714step1 raw39714step1Labels = mixedMoment B raw39714step2 raw39714step2Labels := by
      have ha : raw39714step2 = -raw39714step1 := by apply Matrix.ext; change ∀ i j, raw39714step2 i j = -(raw39714step1 i j); unfold raw39714step2 raw39714step1; decide +kernel
      have hl : raw39714step2Labels = raw39714step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node483 node483Labels := by rfl

theorem canonical39715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39715 raw39715Labels = mixedMoment B node498 node498Labels := by
  calc
    mixedMoment B raw39715 raw39715Labels = mixedMoment B raw39715step0 raw39715step0Labels := by
      have hz : ∀ j, raw39715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39715step0 = (fun i j => raw39715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39715step0 raw39715; decide +kernel
      have hl : raw39715step0Labels = raw39715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39715 raw39715Labels permutation346 hz
    mixedMoment B raw39715step0 raw39715step0Labels = mixedMoment B raw39715step1 raw39715step1Labels := by
      have ha : raw39715step1 = (fun i j => raw39715step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39715step1 raw39715step0; decide +kernel
      have hl : raw39715step1Labels = raw39715step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39715step0 raw39715step0Labels permutation151 permutation2
    mixedMoment B raw39715step1 raw39715step1Labels = mixedMoment B raw39715step2 raw39715step2Labels := by
      have ha : raw39715step2 = -raw39715step1 := by apply Matrix.ext; change ∀ i j, raw39715step2 i j = -(raw39715step1 i j); unfold raw39715step2 raw39715step1; decide +kernel
      have hl : raw39715step2Labels = raw39715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node498 node498Labels := by rfl

theorem canonical39716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39716 raw39716Labels = mixedMoment B node491 node491Labels := by
  calc
    mixedMoment B raw39716 raw39716Labels = mixedMoment B raw39716step0 raw39716step0Labels := by
      have hz : ∀ j, raw39716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39716step0 = (fun i j => raw39716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39716step0 raw39716; decide +kernel
      have hl : raw39716step0Labels = raw39716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39716 raw39716Labels permutation346 hz
    mixedMoment B raw39716step0 raw39716step0Labels = mixedMoment B raw39716step1 raw39716step1Labels := by
      have ha : raw39716step1 = (fun i j => raw39716step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39716step1 raw39716step0; decide +kernel
      have hl : raw39716step1Labels = raw39716step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39716step0 raw39716step0Labels permutation151 permutation2
    mixedMoment B raw39716step1 raw39716step1Labels = mixedMoment B raw39716step2 raw39716step2Labels := by
      have ha : raw39716step2 = -raw39716step1 := by apply Matrix.ext; change ∀ i j, raw39716step2 i j = -(raw39716step1 i j); unfold raw39716step2 raw39716step1; decide +kernel
      have hl : raw39716step2Labels = raw39716step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node491 node491Labels := by rfl

theorem canonical39717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39717 raw39717Labels = mixedMoment B node514 node514Labels := by
  calc
    mixedMoment B raw39717 raw39717Labels = mixedMoment B raw39717step0 raw39717step0Labels := by
      have hz : ∀ j, raw39717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39717step0 = (fun i j => raw39717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39717step0 raw39717; decide +kernel
      have hl : raw39717step0Labels = raw39717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39717 raw39717Labels permutation346 hz
    mixedMoment B raw39717step0 raw39717step0Labels = mixedMoment B raw39717step1 raw39717step1Labels := by
      have ha : raw39717step1 = (fun i j => raw39717step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39717step1 raw39717step0; decide +kernel
      have hl : raw39717step1Labels = raw39717step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39717step0 raw39717step0Labels permutation56 permutation5
    mixedMoment B raw39717step1 raw39717step1Labels = mixedMoment B raw39717step2 raw39717step2Labels := by
      have ha : raw39717step2 = -raw39717step1 := by apply Matrix.ext; change ∀ i j, raw39717step2 i j = -(raw39717step1 i j); unfold raw39717step2 raw39717step1; decide +kernel
      have hl : raw39717step2Labels = raw39717step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node514 node514Labels := by rfl

theorem canonical39718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39718 raw39718Labels = mixedMoment B node515 node515Labels := by
  calc
    mixedMoment B raw39718 raw39718Labels = mixedMoment B raw39718step0 raw39718step0Labels := by
      have hz : ∀ j, raw39718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39718step0 = (fun i j => raw39718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39718step0 raw39718; decide +kernel
      have hl : raw39718step0Labels = raw39718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39718 raw39718Labels permutation346 hz
    mixedMoment B raw39718step0 raw39718step0Labels = mixedMoment B raw39718step1 raw39718step1Labels := by
      have ha : raw39718step1 = (fun i j => raw39718step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39718step1 raw39718step0; decide +kernel
      have hl : raw39718step1Labels = raw39718step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39718step0 raw39718step0Labels permutation32 permutation3
    _ = mixedMoment B node515 node515Labels := by rfl

theorem canonical39719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39719 raw39719Labels = mixedMoment B node512 node512Labels := by
  calc
    mixedMoment B raw39719 raw39719Labels = mixedMoment B raw39719step0 raw39719step0Labels := by
      have ha : raw39719step0 = (fun i j => raw39719 (permutation273 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39719step0 raw39719; decide +kernel
      have hl : raw39719step0Labels = raw39719Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39719 raw39719Labels permutation273 permutation5
    mixedMoment B raw39719step0 raw39719step0Labels = mixedMoment B raw39719step1 raw39719step1Labels := by
      have ha : raw39719step1 = -raw39719step0 := by apply Matrix.ext; change ∀ i j, raw39719step1 i j = -(raw39719step0 i j); unfold raw39719step1 raw39719step0; decide +kernel
      have hl : raw39719step1Labels = raw39719step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node512 node512Labels := by rfl

theorem canonical39720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39720 raw39720Labels = mixedMoment B node513 node513Labels := by
  calc
    mixedMoment B raw39720 raw39720Labels = mixedMoment B raw39720step0 raw39720step0Labels := by
      have ha : raw39720step0 = (fun i j => raw39720 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39720step0 raw39720; decide +kernel
      have hl : raw39720step0Labels = raw39720Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39720 raw39720Labels permutation152 permutation3
    _ = mixedMoment B node513 node513Labels := by rfl

theorem canonical39721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39721 raw39721Labels = mixedMoment B node5506 node5506Labels := by
  calc
    mixedMoment B raw39721 raw39721Labels = mixedMoment B raw39721step0 raw39721step0Labels := by
      have hz : ∀ j, raw39721 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39721step0 = (fun i j => raw39721 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39721step0 raw39721; decide +kernel
      have hl : raw39721step0Labels = raw39721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39721 raw39721Labels permutation434 hz
    mixedMoment B raw39721step0 raw39721step0Labels = mixedMoment B raw39721step1 raw39721step1Labels := by
      have hz : ∀ j, raw39721step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39721step1 = (fun i j => raw39721step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39721step1 raw39721step0; decide +kernel
      have hl : raw39721step1Labels = raw39721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39721step0 raw39721step0Labels permutation80 hz
    mixedMoment B raw39721step1 raw39721step1Labels = mixedMoment B raw39721step2 raw39721step2Labels := by
      have ha : raw39721step2 = (fun i j => raw39721step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39721step2 raw39721step1; decide +kernel
      have hl : raw39721step2Labels = raw39721step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39721step1 raw39721step1Labels permutation8 permutation3
    _ = mixedMoment B node5506 node5506Labels := by rfl

theorem canonical39722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39722 raw39722Labels = mixedMoment B node489 node489Labels := by
  calc
    mixedMoment B raw39722 raw39722Labels = mixedMoment B raw39722step0 raw39722step0Labels := by
      have hz : ∀ j, raw39722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39722step0 = (fun i j => raw39722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39722step0 raw39722; decide +kernel
      have hl : raw39722step0Labels = raw39722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39722 raw39722Labels permutation346 hz
    mixedMoment B raw39722step0 raw39722step0Labels = mixedMoment B raw39722step1 raw39722step1Labels := by
      have ha : raw39722step1 = (fun i j => raw39722step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39722step1 raw39722step0; decide +kernel
      have hl : raw39722step1Labels = raw39722step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39722step0 raw39722step0Labels permutation151 permutation2
    mixedMoment B raw39722step1 raw39722step1Labels = mixedMoment B raw39722step2 raw39722step2Labels := by
      have ha : raw39722step2 = -raw39722step1 := by apply Matrix.ext; change ∀ i j, raw39722step2 i j = -(raw39722step1 i j); unfold raw39722step2 raw39722step1; decide +kernel
      have hl : raw39722step2Labels = raw39722step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node489 node489Labels := by rfl

theorem canonical39723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39723 raw39723Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw39723 raw39723Labels = mixedMoment B raw39723step0 raw39723step0Labels := by
      have hz : ∀ j, raw39723 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39723step0 = (fun i j => raw39723 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39723step0 raw39723; decide +kernel
      have hl : raw39723step0Labels = raw39723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39723 raw39723Labels permutation520 hz
    mixedMoment B raw39723step0 raw39723step0Labels = mixedMoment B raw39723step1 raw39723step1Labels := by
      have hz : ∀ j, raw39723step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39723step1 = (fun i j => raw39723step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39723step1 raw39723step0; decide +kernel
      have hl : raw39723step1Labels = raw39723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39723step0 raw39723step0Labels permutation104 hz
    mixedMoment B raw39723step1 raw39723step1Labels = mixedMoment B raw39723step2 raw39723step2Labels := by
      have ha : raw39723step2 = (fun i j => raw39723step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39723step2 raw39723step1; decide +kernel
      have hl : raw39723step2Labels = raw39723step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39723step1 raw39723step1Labels permutation28 permutation5
    _ = mixedMoment B node268 node268Labels := by rfl

theorem canonical39724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39724 raw39724Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw39724 raw39724Labels = mixedMoment B raw39724step0 raw39724step0Labels := by
      have hz : ∀ j, raw39724 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39724step0 = (fun i j => raw39724 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39724step0 raw39724; decide +kernel
      have hl : raw39724step0Labels = raw39724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39724 raw39724Labels permutation434 hz
    mixedMoment B raw39724step0 raw39724step0Labels = mixedMoment B raw39724step1 raw39724step1Labels := by
      have ha : raw39724step1 = (fun i j => raw39724step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39724step1 raw39724step0; decide +kernel
      have hl : raw39724step1Labels = raw39724step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39724step0 raw39724step0Labels permutation148 permutation5
    _ = mixedMoment B node467 node467Labels := by rfl

theorem canonical39725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39725 raw39725Labels = mixedMoment B node498 node498Labels := by
  calc
    mixedMoment B raw39725 raw39725Labels = mixedMoment B raw39725step0 raw39725step0Labels := by
      have hz : ∀ j, raw39725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39725step0 = (fun i j => raw39725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39725step0 raw39725; decide +kernel
      have hl : raw39725step0Labels = raw39725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39725 raw39725Labels permutation434 hz
    mixedMoment B raw39725step0 raw39725step0Labels = mixedMoment B raw39725step1 raw39725step1Labels := by
      have ha : raw39725step1 = (fun i j => raw39725step0 (permutation81 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39725step1 raw39725step0; decide +kernel
      have hl : raw39725step1Labels = raw39725step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39725step0 raw39725step0Labels permutation81 permutation4
    mixedMoment B raw39725step1 raw39725step1Labels = mixedMoment B raw39725step2 raw39725step2Labels := by
      have ha : raw39725step2 = -raw39725step1 := by apply Matrix.ext; change ∀ i j, raw39725step2 i j = -(raw39725step1 i j); unfold raw39725step2 raw39725step1; decide +kernel
      have hl : raw39725step2Labels = raw39725step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node498 node498Labels := by rfl

theorem canonical39726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39726 raw39726Labels = mixedMoment B node381 node381Labels := by
  calc
    mixedMoment B raw39726 raw39726Labels = mixedMoment B raw39726step0 raw39726step0Labels := by
      have hz : ∀ j, raw39726 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39726step0 = (fun i j => raw39726 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39726step0 raw39726; decide +kernel
      have hl : raw39726step0Labels = raw39726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39726 raw39726Labels permutation434 hz
    mixedMoment B raw39726step0 raw39726step0Labels = mixedMoment B raw39726step1 raw39726step1Labels := by
      have ha : raw39726step1 = (fun i j => raw39726step0 (permutation114 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39726step1 raw39726step0; decide +kernel
      have hl : raw39726step1Labels = raw39726step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39726step0 raw39726step0Labels permutation114 permutation4
    _ = mixedMoment B node381 node381Labels := by rfl

theorem canonical39727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39727 raw39727Labels = mixedMoment B node480 node480Labels := by
  calc
    mixedMoment B raw39727 raw39727Labels = mixedMoment B raw39727step0 raw39727step0Labels := by
      have ha : raw39727step0 = (fun i j => raw39727 (permutation661 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39727step0 raw39727; decide +kernel
      have hl : raw39727step0Labels = raw39727Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39727 raw39727Labels permutation661 permutation5
    _ = mixedMoment B node480 node480Labels := by rfl

theorem canonical39728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39728 raw39728Labels = mixedMoment B node444 node444Labels := by
  calc
    mixedMoment B raw39728 raw39728Labels = mixedMoment B raw39728step0 raw39728step0Labels := by
      have ha : raw39728step0 = (fun i j => raw39728 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39728step0 raw39728; decide +kernel
      have hl : raw39728step0Labels = raw39728Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39728 raw39728Labels permutation414 permutation6
    _ = mixedMoment B node444 node444Labels := by rfl

theorem canonical39729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39729 raw39729Labels = mixedMoment B node443 node443Labels := by
  calc
    mixedMoment B raw39729 raw39729Labels = mixedMoment B raw39729step0 raw39729step0Labels := by
      have ha : raw39729step0 = (fun i j => raw39729 (permutation643 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39729step0 raw39729; decide +kernel
      have hl : raw39729step0Labels = raw39729Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39729 raw39729Labels permutation643 permutation7
    _ = mixedMoment B node443 node443Labels := by rfl

theorem canonical39730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39730 raw39730Labels = mixedMoment B node485 node485Labels := by
  calc
    mixedMoment B raw39730 raw39730Labels = mixedMoment B raw39730step0 raw39730step0Labels := by
      have ha : raw39730step0 = (fun i j => raw39730 (permutation389 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39730step0 raw39730; decide +kernel
      have hl : raw39730step0Labels = raw39730Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39730 raw39730Labels permutation389 permutation6
    _ = mixedMoment B node485 node485Labels := by rfl

theorem canonical39731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39731 raw39731Labels = mixedMoment B node499 node499Labels := by
  calc
    mixedMoment B raw39731 raw39731Labels = mixedMoment B raw39731step0 raw39731step0Labels := by
      have ha : raw39731step0 = (fun i j => raw39731 (permutation346 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39731step0 raw39731; decide +kernel
      have hl : raw39731step0Labels = raw39731Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39731 raw39731Labels permutation346 permutation4
    mixedMoment B raw39731step0 raw39731step0Labels = mixedMoment B raw39731step1 raw39731step1Labels := by
      have ha : raw39731step1 = -raw39731step0 := by apply Matrix.ext; change ∀ i j, raw39731step1 i j = -(raw39731step0 i j); unfold raw39731step1 raw39731step0; decide +kernel
      have hl : raw39731step1Labels = raw39731step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node499 node499Labels := by rfl

theorem canonical39732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39732 raw39732Labels = mixedMoment B node521 node521Labels := by
  calc
    mixedMoment B raw39732 raw39732Labels = mixedMoment B raw39732step0 raw39732step0Labels := by
      have hz : ∀ j, raw39732 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39732step0 = (fun i j => raw39732 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39732step0 raw39732; decide +kernel
      have hl : raw39732step0Labels = raw39732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39732 raw39732Labels permutation434 hz
    _ = mixedMoment B node521 node521Labels := by rfl

theorem canonical39733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39733 raw39733Labels = mixedMoment B node479 node479Labels := by
  calc
    mixedMoment B raw39733 raw39733Labels = mixedMoment B raw39733step0 raw39733step0Labels := by
      have ha : raw39733step0 = (fun i j => raw39733 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39733step0 raw39733; decide +kernel
      have hl : raw39733step0Labels = raw39733Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39733 raw39733Labels permutation682 permutation2
    mixedMoment B raw39733step0 raw39733step0Labels = mixedMoment B raw39733step1 raw39733step1Labels := by
      have ha : raw39733step1 = -raw39733step0 := by apply Matrix.ext; change ∀ i j, raw39733step1 i j = -(raw39733step0 i j); unfold raw39733step1 raw39733step0; decide +kernel
      have hl : raw39733step1Labels = raw39733step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node479 node479Labels := by rfl

theorem canonical39734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39734 raw39734Labels = mixedMoment B node409 node409Labels := by
  calc
    mixedMoment B raw39734 raw39734Labels = mixedMoment B raw39734step0 raw39734step0Labels := by
      have hz : ∀ j, raw39734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39734step0 = (fun i j => raw39734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39734step0 raw39734; decide +kernel
      have hl : raw39734step0Labels = raw39734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39734 raw39734Labels permutation346 hz
    mixedMoment B raw39734step0 raw39734step0Labels = mixedMoment B raw39734step1 raw39734step1Labels := by
      have ha : raw39734step1 = (fun i j => raw39734step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39734step1 raw39734step0; decide +kernel
      have hl : raw39734step1Labels = raw39734step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39734step0 raw39734step0Labels permutation122 permutation6
    _ = mixedMoment B node409 node409Labels := by rfl

theorem canonical39735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39735 raw39735Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw39735 raw39735Labels = mixedMoment B raw39735step0 raw39735step0Labels := by
      have hz : ∀ j, raw39735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39735step0 = (fun i j => raw39735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39735step0 raw39735; decide +kernel
      have hl : raw39735step0Labels = raw39735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39735 raw39735Labels permutation346 hz
    mixedMoment B raw39735step0 raw39735step0Labels = mixedMoment B raw39735step1 raw39735step1Labels := by
      have ha : raw39735step1 = (fun i j => raw39735step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39735step1 raw39735step0; decide +kernel
      have hl : raw39735step1Labels = raw39735step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39735step0 raw39735step0Labels permutation151 permutation7
    _ = mixedMoment B node387 node387Labels := by rfl

theorem canonical39736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39736 raw39736Labels = mixedMoment B node150 node150Labels := by
  calc
    mixedMoment B raw39736 raw39736Labels = mixedMoment B raw39736step0 raw39736step0Labels := by
      have hz : ∀ j, raw39736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39736step0 = (fun i j => raw39736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39736step0 raw39736; decide +kernel
      have hl : raw39736step0Labels = raw39736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39736 raw39736Labels permutation346 hz
    mixedMoment B raw39736step0 raw39736step0Labels = mixedMoment B raw39736step1 raw39736step1Labels := by
      have ha : raw39736step1 = (fun i j => raw39736step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39736step1 raw39736step0; decide +kernel
      have hl : raw39736step1Labels = raw39736step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39736step0 raw39736step0Labels permutation128 permutation6
    _ = mixedMoment B node150 node150Labels := by rfl

theorem canonical39737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39737 raw39737Labels = mixedMoment B node145 node145Labels := by
  calc
    mixedMoment B raw39737 raw39737Labels = mixedMoment B raw39737step0 raw39737step0Labels := by
      have hz : ∀ j, raw39737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39737step0 = (fun i j => raw39737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39737step0 raw39737; decide +kernel
      have hl : raw39737step0Labels = raw39737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39737 raw39737Labels permutation346 hz
    mixedMoment B raw39737step0 raw39737step0Labels = mixedMoment B raw39737step1 raw39737step1Labels := by
      have ha : raw39737step1 = (fun i j => raw39737step0 (permutation148 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39737step1 raw39737step0; decide +kernel
      have hl : raw39737step1Labels = raw39737step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39737step0 raw39737step0Labels permutation148 permutation7
    _ = mixedMoment B node145 node145Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical311
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39832 raw39832Labels = mixedMoment B node356 node356Labels := by
  calc
    mixedMoment B raw39832 raw39832Labels = mixedMoment B raw39832step0 raw39832step0Labels := by
      have ha : raw39832step0 = (fun i j => raw39832 (permutation525 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39832step0 raw39832; decide +kernel
      have hl : raw39832step0Labels = raw39832Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39832 raw39832Labels permutation525 permutation4
    _ = mixedMoment B node356 node356Labels := by rfl

theorem canonical39833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39833 raw39833Labels = mixedMoment B node398 node398Labels := by
  calc
    mixedMoment B raw39833 raw39833Labels = mixedMoment B raw39833step0 raw39833step0Labels := by
      have hz : ∀ j, raw39833 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39833step0 = (fun i j => raw39833 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39833step0 raw39833; decide +kernel
      have hl : raw39833step0Labels = raw39833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39833 raw39833Labels permutation434 hz
    mixedMoment B raw39833step0 raw39833step0Labels = mixedMoment B raw39833step1 raw39833step1Labels := by
      have ha : raw39833step1 = (fun i j => raw39833step0 (permutation135 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39833step1 raw39833step0; decide +kernel
      have hl : raw39833step1Labels = raw39833step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39833step0 raw39833step0Labels permutation135 permutation5
    _ = mixedMoment B node398 node398Labels := by rfl

theorem canonical39834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39834 raw39834Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw39834 raw39834Labels = mixedMoment B raw39834step0 raw39834step0Labels := by
      have hz : ∀ j, raw39834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39834step0 = (fun i j => raw39834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39834step0 raw39834; decide +kernel
      have hl : raw39834step0Labels = raw39834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39834 raw39834Labels permutation434 hz
    mixedMoment B raw39834step0 raw39834step0Labels = mixedMoment B raw39834step1 raw39834step1Labels := by
      have ha : raw39834step1 = (fun i j => raw39834step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39834step1 raw39834step0; decide +kernel
      have hl : raw39834step1Labels = raw39834step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39834step0 raw39834step0Labels permutation35 permutation7
    mixedMoment B raw39834step1 raw39834step1Labels = mixedMoment B raw39834step2 raw39834step2Labels := by
      have ha : raw39834step2 = -raw39834step1 := by apply Matrix.ext; change ∀ i j, raw39834step2 i j = -(raw39834step1 i j); unfold raw39834step2 raw39834step1; decide +kernel
      have hl : raw39834step2Labels = raw39834step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node467 node467Labels := by rfl

theorem canonical39835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39835 raw39835Labels = mixedMoment B node446 node446Labels := by
  calc
    mixedMoment B raw39835 raw39835Labels = mixedMoment B raw39835step0 raw39835step0Labels := by
      have hz : ∀ j, raw39835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39835step0 = (fun i j => raw39835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39835step0 raw39835; decide +kernel
      have hl : raw39835step0Labels = raw39835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39835 raw39835Labels permutation434 hz
    mixedMoment B raw39835step0 raw39835step0Labels = mixedMoment B raw39835step1 raw39835step1Labels := by
      have ha : raw39835step1 = (fun i j => raw39835step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39835step1 raw39835step0; decide +kernel
      have hl : raw39835step1Labels = raw39835step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39835step0 raw39835step0Labels permutation145 permutation7
    _ = mixedMoment B node446 node446Labels := by rfl

theorem canonical39836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39836 raw39836Labels = mixedMoment B node288 node288Labels := by
  calc
    mixedMoment B raw39836 raw39836Labels = mixedMoment B raw39836step0 raw39836step0Labels := by
      have hz : ∀ j, raw39836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39836step0 = (fun i j => raw39836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39836step0 raw39836; decide +kernel
      have hl : raw39836step0Labels = raw39836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39836 raw39836Labels permutation434 hz
    mixedMoment B raw39836step0 raw39836step0Labels = mixedMoment B raw39836step1 raw39836step1Labels := by
      have ha : raw39836step1 = (fun i j => raw39836step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39836step1 raw39836step0; decide +kernel
      have hl : raw39836step1Labels = raw39836step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39836step0 raw39836step0Labels permutation143 permutation7
    _ = mixedMoment B node288 node288Labels := by rfl

theorem canonical39837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39837 raw39837Labels = mixedMoment B node434 node434Labels := by
  calc
    mixedMoment B raw39837 raw39837Labels = mixedMoment B raw39837step0 raw39837step0Labels := by
      have ha : raw39837step0 = (fun i j => raw39837 (permutation412 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39837step0 raw39837; decide +kernel
      have hl : raw39837step0Labels = raw39837Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39837 raw39837Labels permutation412 permutation6
    _ = mixedMoment B node434 node434Labels := by rfl

theorem canonical39838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39838 raw39838Labels = mixedMoment B node280 node280Labels := by
  calc
    mixedMoment B raw39838 raw39838Labels = mixedMoment B raw39838step0 raw39838step0Labels := by
      have ha : raw39838step0 = (fun i j => raw39838 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39838step0 raw39838; decide +kernel
      have hl : raw39838step0Labels = raw39838Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39838 raw39838Labels permutation646 permutation7
    _ = mixedMoment B node280 node280Labels := by rfl

theorem canonical39839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39839 raw39839Labels = mixedMoment B node278 node278Labels := by
  calc
    mixedMoment B raw39839 raw39839Labels = mixedMoment B raw39839step0 raw39839step0Labels := by
      have ha : raw39839step0 = (fun i j => raw39839 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39839step0 raw39839; decide +kernel
      have hl : raw39839step0Labels = raw39839Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39839 raw39839Labels permutation644 permutation7
    _ = mixedMoment B node278 node278Labels := by rfl

theorem canonical39840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39840 raw39840Labels = mixedMoment B node313 node313Labels := by
  calc
    mixedMoment B raw39840 raw39840Labels = mixedMoment B raw39840step0 raw39840step0Labels := by
      have hz : ∀ j, raw39840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39840step0 = (fun i j => raw39840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39840step0 raw39840; decide +kernel
      have hl : raw39840step0Labels = raw39840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39840 raw39840Labels permutation434 hz
    mixedMoment B raw39840step0 raw39840step0Labels = mixedMoment B raw39840step1 raw39840step1Labels := by
      have ha : raw39840step1 = (fun i j => raw39840step0 (permutation119 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39840step1 raw39840step0; decide +kernel
      have hl : raw39840step1Labels = raw39840step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39840step0 raw39840step0Labels permutation119 permutation6
    _ = mixedMoment B node313 node313Labels := by rfl

theorem canonical39841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39841 raw39841Labels = mixedMoment B node123 node123Labels := by
  calc
    mixedMoment B raw39841 raw39841Labels = mixedMoment B raw39841step0 raw39841step0Labels := by
      have hz : ∀ j, raw39841 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39841step0 = (fun i j => raw39841 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39841step0 raw39841; decide +kernel
      have hl : raw39841step0Labels = raw39841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39841 raw39841Labels permutation434 hz
    mixedMoment B raw39841step0 raw39841step0Labels = mixedMoment B raw39841step1 raw39841step1Labels := by
      have ha : raw39841step1 = (fun i j => raw39841step0 (permutation142 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39841step1 raw39841step0; decide +kernel
      have hl : raw39841step1Labels = raw39841step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39841step0 raw39841step0Labels permutation142 permutation6
    _ = mixedMoment B node123 node123Labels := by rfl

theorem canonical39842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39842 raw39842Labels = mixedMoment B node5508 node5508Labels := by
  calc
    mixedMoment B raw39842 raw39842Labels = mixedMoment B raw39842step0 raw39842step0Labels := by
      have ha : raw39842step0 = (fun i j => raw39842 (permutation550 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39842step0 raw39842; decide +kernel
      have hl : raw39842step0Labels = raw39842Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39842 raw39842Labels permutation550 permutation6
    _ = mixedMoment B node5508 node5508Labels := by rfl

theorem canonical39843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39843 raw39843Labels = mixedMoment B node114 node114Labels := by
  calc
    mixedMoment B raw39843 raw39843Labels = mixedMoment B raw39843step0 raw39843step0Labels := by
      have ha : raw39843step0 = (fun i j => raw39843 (permutation643 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39843step0 raw39843; decide +kernel
      have hl : raw39843step0Labels = raw39843Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39843 raw39843Labels permutation643 permutation6
    _ = mixedMoment B node114 node114Labels := by rfl

theorem canonical39844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39844 raw39844Labels = mixedMoment B node29 node29Labels := by
  calc
    mixedMoment B raw39844 raw39844Labels = mixedMoment B raw39844step0 raw39844step0Labels := by
      have hz : ∀ j, raw39844 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39844step0 = (fun i j => raw39844 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39844step0 raw39844; decide +kernel
      have hl : raw39844step0Labels = raw39844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39844 raw39844Labels permutation434 hz
    mixedMoment B raw39844step0 raw39844step0Labels = mixedMoment B raw39844step1 raw39844step1Labels := by
      have hz : ∀ j, raw39844step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39844step1 = (fun i j => raw39844step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39844step1 raw39844step0; decide +kernel
      have hl : raw39844step1Labels = raw39844step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39844step0 raw39844step0Labels permutation80 hz
    mixedMoment B raw39844step1 raw39844step1Labels = mixedMoment B raw39844step2 raw39844step2Labels := by
      have ha : raw39844step2 = (fun i j => raw39844step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39844step2 raw39844step1; decide +kernel
      have hl : raw39844step2Labels = raw39844step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39844step1 raw39844step1Labels permutation28 permutation6
    _ = mixedMoment B node29 node29Labels := by rfl

theorem canonical39845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39845 raw39845Labels = mixedMoment B node101 node101Labels := by
  calc
    mixedMoment B raw39845 raw39845Labels = mixedMoment B raw39845step0 raw39845step0Labels := by
      have hz : ∀ j, raw39845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39845step0 = (fun i j => raw39845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39845step0 raw39845; decide +kernel
      have hl : raw39845step0Labels = raw39845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39845 raw39845Labels permutation346 hz
    mixedMoment B raw39845step0 raw39845step0Labels = mixedMoment B raw39845step1 raw39845step1Labels := by
      have ha : raw39845step1 = (fun i j => raw39845step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39845step1 raw39845step0; decide +kernel
      have hl : raw39845step1Labels = raw39845step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39845step0 raw39845step0Labels permutation125 permutation6
    _ = mixedMoment B node101 node101Labels := by rfl

theorem canonical39846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39846 raw39846Labels = mixedMoment B node142 node142Labels := by
  calc
    mixedMoment B raw39846 raw39846Labels = mixedMoment B raw39846step0 raw39846step0Labels := by
      have hz : ∀ j, raw39846 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39846step0 = (fun i j => raw39846 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39846step0 raw39846; decide +kernel
      have hl : raw39846step0Labels = raw39846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39846 raw39846Labels permutation346 hz
    mixedMoment B raw39846step0 raw39846step0Labels = mixedMoment B raw39846step1 raw39846step1Labels := by
      have ha : raw39846step1 = (fun i j => raw39846step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39846step1 raw39846step0; decide +kernel
      have hl : raw39846step1Labels = raw39846step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39846step0 raw39846step0Labels permutation151 permutation7
    _ = mixedMoment B node142 node142Labels := by rfl

theorem canonical39847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39847 raw39847Labels = mixedMoment B node27 node27Labels := by
  calc
    mixedMoment B raw39847 raw39847Labels = mixedMoment B raw39847step0 raw39847step0Labels := by
      have hz : ∀ j, raw39847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39847step0 = (fun i j => raw39847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39847step0 raw39847; decide +kernel
      have hl : raw39847step0Labels = raw39847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39847 raw39847Labels permutation346 hz
    mixedMoment B raw39847step0 raw39847step0Labels = mixedMoment B raw39847step1 raw39847step1Labels := by
      have ha : raw39847step1 = (fun i j => raw39847step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39847step1 raw39847step0; decide +kernel
      have hl : raw39847step1Labels = raw39847step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39847step0 raw39847step0Labels permutation137 permutation6
    _ = mixedMoment B node27 node27Labels := by rfl

theorem canonical39848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39848 raw39848Labels = mixedMoment B node12 node12Labels := by
  calc
    mixedMoment B raw39848 raw39848Labels = mixedMoment B raw39848step0 raw39848step0Labels := by
      have hz : ∀ j, raw39848 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39848step0 = (fun i j => raw39848 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39848step0 raw39848; decide +kernel
      have hl : raw39848step0Labels = raw39848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39848 raw39848Labels permutation346 hz
    mixedMoment B raw39848step0 raw39848step0Labels = mixedMoment B raw39848step1 raw39848step1Labels := by
      have ha : raw39848step1 = (fun i j => raw39848step0 (permutation148 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39848step1 raw39848step0; decide +kernel
      have hl : raw39848step1Labels = raw39848step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39848step0 raw39848step0Labels permutation148 permutation6
    _ = mixedMoment B node12 node12Labels := by rfl

theorem canonical39849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39849 raw39849Labels = mixedMoment B node10 node10Labels := by
  calc
    mixedMoment B raw39849 raw39849Labels = mixedMoment B raw39849step0 raw39849step0Labels := by
      have ha : raw39849step0 = (fun i j => raw39849 (permutation674 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39849step0 raw39849; decide +kernel
      have hl : raw39849step0Labels = raw39849Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39849 raw39849Labels permutation674 permutation6
    _ = mixedMoment B node10 node10Labels := by rfl

theorem canonical39850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39850 raw39850Labels = mixedMoment B node229 node229Labels := by
  calc
    mixedMoment B raw39850 raw39850Labels = mixedMoment B raw39850step0 raw39850step0Labels := by
      have hz : ∀ j, raw39850 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39850step0 = (fun i j => raw39850 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39850step0 raw39850; decide +kernel
      have hl : raw39850step0Labels = raw39850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39850 raw39850Labels permutation434 hz
    mixedMoment B raw39850step0 raw39850step0Labels = mixedMoment B raw39850step1 raw39850step1Labels := by
      have ha : raw39850step1 = (fun i j => raw39850step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39850step1 raw39850step0; decide +kernel
      have hl : raw39850step1Labels = raw39850step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39850step0 raw39850step0Labels permutation96 permutation6
    _ = mixedMoment B node229 node229Labels := by rfl

theorem canonical39851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39851 raw39851Labels = mixedMoment B node240 node240Labels := by
  calc
    mixedMoment B raw39851 raw39851Labels = mixedMoment B raw39851step0 raw39851step0Labels := by
      have hz : ∀ j, raw39851 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39851step0 = (fun i j => raw39851 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39851step0 raw39851; decide +kernel
      have hl : raw39851step0Labels = raw39851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39851 raw39851Labels permutation434 hz
    mixedMoment B raw39851step0 raw39851step0Labels = mixedMoment B raw39851step1 raw39851step1Labels := by
      have ha : raw39851step1 = (fun i j => raw39851step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39851step1 raw39851step0; decide +kernel
      have hl : raw39851step1Labels = raw39851step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39851step0 raw39851step0Labels permutation102 permutation6
    _ = mixedMoment B node240 node240Labels := by rfl

theorem canonical39852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39852 raw39852Labels = mixedMoment B node184 node184Labels := by
  calc
    mixedMoment B raw39852 raw39852Labels = mixedMoment B raw39852step0 raw39852step0Labels := by
      have hz : ∀ j, raw39852 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39852step0 = (fun i j => raw39852 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39852step0 raw39852; decide +kernel
      have hl : raw39852step0Labels = raw39852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39852 raw39852Labels permutation434 hz
    mixedMoment B raw39852step0 raw39852step0Labels = mixedMoment B raw39852step1 raw39852step1Labels := by
      have ha : raw39852step1 = (fun i j => raw39852step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39852step1 raw39852step0; decide +kernel
      have hl : raw39852step1Labels = raw39852step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39852step0 raw39852step0Labels permutation102 permutation6
    _ = mixedMoment B node184 node184Labels := by rfl

theorem canonical39853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39853 raw39853Labels = mixedMoment B node167 node167Labels := by
  calc
    mixedMoment B raw39853 raw39853Labels = mixedMoment B raw39853step0 raw39853step0Labels := by
      have ha : raw39853step0 = (fun i j => raw39853 (permutation432 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39853step0 raw39853; decide +kernel
      have hl : raw39853step0Labels = raw39853Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39853 raw39853Labels permutation432 permutation6
    _ = mixedMoment B node167 node167Labels := by rfl

theorem canonical39854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39854 raw39854Labels = mixedMoment B node434 node434Labels := by
  calc
    mixedMoment B raw39854 raw39854Labels = mixedMoment B raw39854step0 raw39854step0Labels := by
      have ha : raw39854step0 = (fun i j => raw39854 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39854step0 raw39854; decide +kernel
      have hl : raw39854step0Labels = raw39854Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39854 raw39854Labels permutation173 permutation7
    mixedMoment B raw39854step0 raw39854step0Labels = mixedMoment B raw39854step1 raw39854step1Labels := by
      have ha : raw39854step1 = -raw39854step0 := by apply Matrix.ext; change ∀ i j, raw39854step1 i j = -(raw39854step0 i j); unfold raw39854step1 raw39854step0; decide +kernel
      have hl : raw39854step1Labels = raw39854step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node434 node434Labels := by rfl

theorem canonical39855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39855 raw39855Labels = mixedMoment B node427 node427Labels := by
  calc
    mixedMoment B raw39855 raw39855Labels = mixedMoment B raw39855step0 raw39855step0Labels := by
      have ha : raw39855step0 = (fun i j => raw39855 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39855step0 raw39855; decide +kernel
      have hl : raw39855step0Labels = raw39855Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39855 raw39855Labels permutation166 permutation7
    mixedMoment B raw39855step0 raw39855step0Labels = mixedMoment B raw39855step1 raw39855step1Labels := by
      have ha : raw39855step1 = -raw39855step0 := by apply Matrix.ext; change ∀ i j, raw39855step1 i j = -(raw39855step0 i j); unfold raw39855step1 raw39855step0; decide +kernel
      have hl : raw39855step1Labels = raw39855step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node427 node427Labels := by rfl

theorem canonical39856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39856 raw39856Labels = mixedMoment B node435 node435Labels := by
  calc
    mixedMoment B raw39856 raw39856Labels = mixedMoment B raw39856step0 raw39856step0Labels := by
      have hz : ∀ j, raw39856 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39856step0 = (fun i j => raw39856 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39856step0 raw39856; decide +kernel
      have hl : raw39856step0Labels = raw39856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39856 raw39856Labels permutation434 hz
    mixedMoment B raw39856step0 raw39856step0Labels = mixedMoment B raw39856step1 raw39856step1Labels := by
      have ha : raw39856step1 = (fun i j => raw39856step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39856step1 raw39856step0; decide +kernel
      have hl : raw39856step1Labels = raw39856step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39856step0 raw39856step0Labels permutation96 permutation6
    _ = mixedMoment B node435 node435Labels := by rfl

theorem canonical39857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39857 raw39857Labels = mixedMoment B node432 node432Labels := by
  calc
    mixedMoment B raw39857 raw39857Labels = mixedMoment B raw39857step0 raw39857step0Labels := by
      have hz : ∀ j, raw39857 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39857step0 = (fun i j => raw39857 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39857step0 raw39857; decide +kernel
      have hl : raw39857step0Labels = raw39857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39857 raw39857Labels permutation434 hz
    mixedMoment B raw39857step0 raw39857step0Labels = mixedMoment B raw39857step1 raw39857step1Labels := by
      have ha : raw39857step1 = (fun i j => raw39857step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39857step1 raw39857step0; decide +kernel
      have hl : raw39857step1Labels = raw39857step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39857step0 raw39857step0Labels permutation34 permutation7
    mixedMoment B raw39857step1 raw39857step1Labels = mixedMoment B raw39857step2 raw39857step2Labels := by
      have ha : raw39857step2 = -raw39857step1 := by apply Matrix.ext; change ∀ i j, raw39857step2 i j = -(raw39857step1 i j); unfold raw39857step2 raw39857step1; decide +kernel
      have hl : raw39857step2Labels = raw39857step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node432 node432Labels := by rfl

theorem canonical39858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39858 raw39858Labels = mixedMoment B node282 node282Labels := by
  calc
    mixedMoment B raw39858 raw39858Labels = mixedMoment B raw39858step0 raw39858step0Labels := by
      have hz : ∀ j, raw39858 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39858step0 = (fun i j => raw39858 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39858step0 raw39858; decide +kernel
      have hl : raw39858step0Labels = raw39858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39858 raw39858Labels permutation434 hz
    mixedMoment B raw39858step0 raw39858step0Labels = mixedMoment B raw39858step1 raw39858step1Labels := by
      have ha : raw39858step1 = (fun i j => raw39858step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39858step1 raw39858step0; decide +kernel
      have hl : raw39858step1Labels = raw39858step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39858step0 raw39858step0Labels permutation145 permutation7
    _ = mixedMoment B node282 node282Labels := by rfl

theorem canonical39859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39859 raw39859Labels = mixedMoment B node426 node426Labels := by
  calc
    mixedMoment B raw39859 raw39859Labels = mixedMoment B raw39859step0 raw39859step0Labels := by
      have ha : raw39859step0 = (fun i j => raw39859 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39859step0 raw39859; decide +kernel
      have hl : raw39859step0Labels = raw39859Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39859 raw39859Labels permutation393 permutation6
    _ = mixedMoment B node426 node426Labels := by rfl

theorem canonical39860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39860 raw39860Labels = mixedMoment B node428 node428Labels := by
  calc
    mixedMoment B raw39860 raw39860Labels = mixedMoment B raw39860step0 raw39860step0Labels := by
      have ha : raw39860step0 = (fun i j => raw39860 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39860step0 raw39860; decide +kernel
      have hl : raw39860step0Labels = raw39860Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39860 raw39860Labels permutation393 permutation6
    _ = mixedMoment B node428 node428Labels := by rfl

theorem canonical39861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39861 raw39861Labels = mixedMoment B node429 node429Labels := by
  calc
    mixedMoment B raw39861 raw39861Labels = mixedMoment B raw39861step0 raw39861step0Labels := by
      have ha : raw39861step0 = (fun i j => raw39861 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39861step0 raw39861; decide +kernel
      have hl : raw39861step0Labels = raw39861Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39861 raw39861Labels permutation164 permutation7
    mixedMoment B raw39861step0 raw39861step0Labels = mixedMoment B raw39861step1 raw39861step1Labels := by
      have ha : raw39861step1 = -raw39861step0 := by apply Matrix.ext; change ∀ i j, raw39861step1 i j = -(raw39861step0 i j); unfold raw39861step1 raw39861step0; decide +kernel
      have hl : raw39861step1Labels = raw39861step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node429 node429Labels := by rfl

theorem canonical39862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39862 raw39862Labels = mixedMoment B node309 node309Labels := by
  calc
    mixedMoment B raw39862 raw39862Labels = mixedMoment B raw39862step0 raw39862step0Labels := by
      have hz : ∀ j, raw39862 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39862step0 = (fun i j => raw39862 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39862step0 raw39862; decide +kernel
      have hl : raw39862step0Labels = raw39862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39862 raw39862Labels permutation434 hz
    mixedMoment B raw39862step0 raw39862step0Labels = mixedMoment B raw39862step1 raw39862step1Labels := by
      have ha : raw39862step1 = (fun i j => raw39862step0 (permutation120 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39862step1 raw39862step0; decide +kernel
      have hl : raw39862step1Labels = raw39862step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39862step0 raw39862step0Labels permutation120 permutation6
    _ = mixedMoment B node309 node309Labels := by rfl

theorem canonical39863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39863 raw39863Labels = mixedMoment B node325 node325Labels := by
  calc
    mixedMoment B raw39863 raw39863Labels = mixedMoment B raw39863step0 raw39863step0Labels := by
      have hz : ∀ j, raw39863 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39863step0 = (fun i j => raw39863 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39863step0 raw39863; decide +kernel
      have hl : raw39863step0Labels = raw39863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39863 raw39863Labels permutation434 hz
    mixedMoment B raw39863step0 raw39863step0Labels = mixedMoment B raw39863step1 raw39863step1Labels := by
      have ha : raw39863step1 = (fun i j => raw39863step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39863step1 raw39863step0; decide +kernel
      have hl : raw39863step1Labels = raw39863step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39863step0 raw39863step0Labels permutation145 permutation7
    _ = mixedMoment B node325 node325Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical323
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41397 raw41397Labels = mixedMoment B node1125 node1125Labels := by
  calc
    mixedMoment B raw41397 raw41397Labels = mixedMoment B raw41397step0 raw41397step0Labels := by
      have ha : raw41397step0 = (fun i j => raw41397 (permutation647 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41397step0 raw41397; decide +kernel
      have hl : raw41397step0Labels = raw41397Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41397 raw41397Labels permutation647 permutation6
    _ = mixedMoment B node1125 node1125Labels := by rfl

theorem canonical41398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41398 raw41398Labels = mixedMoment B node597 node597Labels := by
  calc
    mixedMoment B raw41398 raw41398Labels = mixedMoment B raw41398step0 raw41398step0Labels := by
      have ha : raw41398step0 = (fun i j => raw41398 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41398step0 raw41398; decide +kernel
      have hl : raw41398step0Labels = raw41398Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41398 raw41398Labels permutation590 permutation6
    _ = mixedMoment B node597 node597Labels := by rfl

theorem canonical41399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41399 raw41399Labels = mixedMoment B node577 node577Labels := by
  calc
    mixedMoment B raw41399 raw41399Labels = mixedMoment B raw41399step0 raw41399step0Labels := by
      have ha : raw41399step0 = (fun i j => raw41399 (permutation665 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41399step0 raw41399; decide +kernel
      have hl : raw41399step0Labels = raw41399Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41399 raw41399Labels permutation665 permutation6
    _ = mixedMoment B node577 node577Labels := by rfl

theorem canonical41400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41400 raw41400Labels = mixedMoment B node2132 node2132Labels := by
  calc
    mixedMoment B raw41400 raw41400Labels = mixedMoment B raw41400step0 raw41400step0Labels := by
      have hz : ∀ j, raw41400 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41400step0 = (fun i j => raw41400 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41400step0 raw41400; decide +kernel
      have hl : raw41400step0Labels = raw41400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41400 raw41400Labels permutation520 hz
    mixedMoment B raw41400step0 raw41400step0Labels = mixedMoment B raw41400step1 raw41400step1Labels := by
      have ha : raw41400step1 = (fun i j => raw41400step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41400step1 raw41400step0; decide +kernel
      have hl : raw41400step1Labels = raw41400step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41400step0 raw41400step0Labels permutation122 permutation6
    _ = mixedMoment B node2132 node2132Labels := by rfl

theorem canonical41401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41401 raw41401Labels = mixedMoment B node1822 node1822Labels := by
  calc
    mixedMoment B raw41401 raw41401Labels = mixedMoment B raw41401step0 raw41401step0Labels := by
      have ha : raw41401step0 = (fun i j => raw41401 (permutation506 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41401step0 raw41401; decide +kernel
      have hl : raw41401step0Labels = raw41401Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41401 raw41401Labels permutation506 permutation6
    _ = mixedMoment B node1822 node1822Labels := by rfl

theorem canonical41402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41402 raw41402Labels = mixedMoment B node2088 node2088Labels := by
  calc
    mixedMoment B raw41402 raw41402Labels = mixedMoment B raw41402step0 raw41402step0Labels := by
      have ha : raw41402step0 = (fun i j => raw41402 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41402step0 raw41402; decide +kernel
      have hl : raw41402step0Labels = raw41402Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41402 raw41402Labels permutation514 permutation6
    _ = mixedMoment B node2088 node2088Labels := by rfl

theorem canonical41403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41403 raw41403Labels = mixedMoment B node1803 node1803Labels := by
  calc
    mixedMoment B raw41403 raw41403Labels = mixedMoment B raw41403step0 raw41403step0Labels := by
      have ha : raw41403step0 = (fun i j => raw41403 (permutation506 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41403step0 raw41403; decide +kernel
      have hl : raw41403step0Labels = raw41403Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41403 raw41403Labels permutation506 permutation6
    _ = mixedMoment B node1803 node1803Labels := by rfl

theorem canonical41404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41404 raw41404Labels = mixedMoment B node601 node601Labels := by
  calc
    mixedMoment B raw41404 raw41404Labels = mixedMoment B raw41404step0 raw41404step0Labels := by
      have hz : ∀ j, raw41404 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41404step0 = (fun i j => raw41404 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41404step0 raw41404; decide +kernel
      have hl : raw41404step0Labels = raw41404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41404 raw41404Labels permutation434 hz
    mixedMoment B raw41404step0 raw41404step0Labels = mixedMoment B raw41404step1 raw41404step1Labels := by
      have ha : raw41404step1 = (fun i j => raw41404step0 (permutation129 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41404step1 raw41404step0; decide +kernel
      have hl : raw41404step1Labels = raw41404step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41404step0 raw41404step0Labels permutation129 permutation6
    _ = mixedMoment B node601 node601Labels := by rfl

theorem canonical41405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41405 raw41405Labels = mixedMoment B node578 node578Labels := by
  calc
    mixedMoment B raw41405 raw41405Labels = mixedMoment B raw41405step0 raw41405step0Labels := by
      have ha : raw41405step0 = (fun i j => raw41405 (permutation666 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41405step0 raw41405; decide +kernel
      have hl : raw41405step0Labels = raw41405Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41405 raw41405Labels permutation666 permutation6
    _ = mixedMoment B node578 node578Labels := by rfl

theorem canonical41406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41406 raw41406Labels = mixedMoment B node1823 node1823Labels := by
  calc
    mixedMoment B raw41406 raw41406Labels = mixedMoment B raw41406step0 raw41406step0Labels := by
      have hz : ∀ j, raw41406 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41406step0 = (fun i j => raw41406 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41406step0 raw41406; decide +kernel
      have hl : raw41406step0Labels = raw41406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41406 raw41406Labels permutation520 hz
    mixedMoment B raw41406step0 raw41406step0Labels = mixedMoment B raw41406step1 raw41406step1Labels := by
      have ha : raw41406step1 = (fun i j => raw41406step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41406step1 raw41406step0; decide +kernel
      have hl : raw41406step1Labels = raw41406step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41406step0 raw41406step0Labels permutation122 permutation6
    _ = mixedMoment B node1823 node1823Labels := by rfl

theorem canonical41407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41407 raw41407Labels = mixedMoment B node1789 node1789Labels := by
  calc
    mixedMoment B raw41407 raw41407Labels = mixedMoment B raw41407step0 raw41407step0Labels := by
      have ha : raw41407step0 = (fun i j => raw41407 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41407step0 raw41407; decide +kernel
      have hl : raw41407step0Labels = raw41407Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41407 raw41407Labels permutation514 permutation6
    _ = mixedMoment B node1789 node1789Labels := by rfl

theorem canonical41408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41408 raw41408Labels = mixedMoment B node2529 node2529Labels := by
  calc
    mixedMoment B raw41408 raw41408Labels = mixedMoment B raw41408step0 raw41408step0Labels := by
      have ha : raw41408step0 = (fun i j => raw41408 (permutation349 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41408step0 raw41408; decide +kernel
      have hl : raw41408step0Labels = raw41408Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41408 raw41408Labels permutation349 permutation6
    mixedMoment B raw41408step0 raw41408step0Labels = mixedMoment B raw41408step1 raw41408step1Labels := by
      have ha : raw41408step1 = -raw41408step0 := by apply Matrix.ext; change ∀ i j, raw41408step1 i j = -(raw41408step0 i j); unfold raw41408step1 raw41408step0; decide +kernel
      have hl : raw41408step1Labels = raw41408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2529 node2529Labels := by rfl

theorem canonical41409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41409 raw41409Labels = mixedMoment B node2524 node2524Labels := by
  calc
    mixedMoment B raw41409 raw41409Labels = mixedMoment B raw41409step0 raw41409step0Labels := by
      have ha : raw41409step0 = (fun i j => raw41409 (permutation348 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41409step0 raw41409; decide +kernel
      have hl : raw41409step0Labels = raw41409Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41409 raw41409Labels permutation348 permutation6
    mixedMoment B raw41409step0 raw41409step0Labels = mixedMoment B raw41409step1 raw41409step1Labels := by
      have ha : raw41409step1 = -raw41409step0 := by apply Matrix.ext; change ∀ i j, raw41409step1 i j = -(raw41409step0 i j); unfold raw41409step1 raw41409step0; decide +kernel
      have hl : raw41409step1Labels = raw41409step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2524 node2524Labels := by rfl

theorem canonical41410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41410 raw41410Labels = mixedMoment B node1111 node1111Labels := by
  calc
    mixedMoment B raw41410 raw41410Labels = mixedMoment B raw41410step0 raw41410step0Labels := by
      have ha : raw41410step0 = (fun i j => raw41410 (permutation659 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41410step0 raw41410; decide +kernel
      have hl : raw41410step0Labels = raw41410Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41410 raw41410Labels permutation659 permutation6
    _ = mixedMoment B node1111 node1111Labels := by rfl

theorem canonical41411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41411 raw41411Labels = mixedMoment B node579 node579Labels := by
  calc
    mixedMoment B raw41411 raw41411Labels = mixedMoment B raw41411step0 raw41411step0Labels := by
      have hz : ∀ j, raw41411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41411step0 = (fun i j => raw41411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41411step0 raw41411; decide +kernel
      have hl : raw41411step0Labels = raw41411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41411 raw41411Labels permutation434 hz
    mixedMoment B raw41411step0 raw41411step0Labels = mixedMoment B raw41411step1 raw41411step1Labels := by
      have ha : raw41411step1 = (fun i j => raw41411step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41411step1 raw41411step0; decide +kernel
      have hl : raw41411step1Labels = raw41411step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41411step0 raw41411step0Labels permutation146 permutation6
    _ = mixedMoment B node579 node579Labels := by rfl

theorem canonical41412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41412 raw41412Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw41412 raw41412Labels = mixedMoment B raw41412step0 raw41412step0Labels := by
      have ha : raw41412step0 = (fun i j => raw41412 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41412step0 raw41412; decide +kernel
      have hl : raw41412step0Labels = raw41412Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41412 raw41412Labels permutation414 permutation6
    _ = mixedMoment B node2105 node2105Labels := by rfl

theorem canonical41413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41413 raw41413Labels = mixedMoment B node1802 node1802Labels := by
  calc
    mixedMoment B raw41413 raw41413Labels = mixedMoment B raw41413step0 raw41413step0Labels := by
      have ha : raw41413step0 = (fun i j => raw41413 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41413step0 raw41413; decide +kernel
      have hl : raw41413step0Labels = raw41413Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41413 raw41413Labels permutation414 permutation6
    _ = mixedMoment B node1802 node1802Labels := by rfl

theorem canonical41414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41414 raw41414Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw41414 raw41414Labels = mixedMoment B raw41414step0 raw41414step0Labels := by
      have ha : raw41414step0 = (fun i j => raw41414 (permutation399 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41414step0 raw41414; decide +kernel
      have hl : raw41414step0Labels = raw41414Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41414 raw41414Labels permutation399 permutation6
    _ = mixedMoment B node2051 node2051Labels := by rfl

theorem canonical41415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41415 raw41415Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw41415 raw41415Labels = mixedMoment B raw41415step0 raw41415step0Labels := by
      have ha : raw41415step0 = (fun i j => raw41415 (permutation409 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41415step0 raw41415; decide +kernel
      have hl : raw41415step0Labels = raw41415Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41415 raw41415Labels permutation409 permutation6
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical41416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41416 raw41416Labels = mixedMoment B node2019 node2019Labels := by
  calc
    mixedMoment B raw41416 raw41416Labels = mixedMoment B raw41416step0 raw41416step0Labels := by
      have ha : raw41416step0 = (fun i j => raw41416 (permutation409 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41416step0 raw41416; decide +kernel
      have hl : raw41416step0Labels = raw41416Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41416 raw41416Labels permutation409 permutation6
    _ = mixedMoment B node2019 node2019Labels := by rfl

theorem canonical41417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41417 raw41417Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw41417 raw41417Labels = mixedMoment B raw41417step0 raw41417step0Labels := by
      have ha : raw41417step0 = (fun i j => raw41417 (permutation395 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41417step0 raw41417; decide +kernel
      have hl : raw41417step0Labels = raw41417Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41417 raw41417Labels permutation395 permutation6
    _ = mixedMoment B node3812 node3812Labels := by rfl

theorem canonical41418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41418 raw41418Labels = mixedMoment B node3786 node3786Labels := by
  calc
    mixedMoment B raw41418 raw41418Labels = mixedMoment B raw41418step0 raw41418step0Labels := by
      have ha : raw41418step0 = (fun i j => raw41418 (permutation395 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41418step0 raw41418; decide +kernel
      have hl : raw41418step0Labels = raw41418Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41418 raw41418Labels permutation395 permutation6
    _ = mixedMoment B node3786 node3786Labels := by rfl

theorem canonical41419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41419 raw41419Labels = mixedMoment B node1966 node1966Labels := by
  calc
    mixedMoment B raw41419 raw41419Labels = mixedMoment B raw41419step0 raw41419step0Labels := by
      have ha : raw41419step0 = (fun i j => raw41419 (permutation523 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41419step0 raw41419; decide +kernel
      have hl : raw41419step0Labels = raw41419Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41419 raw41419Labels permutation523 permutation6
    mixedMoment B raw41419step0 raw41419step0Labels = mixedMoment B raw41419step1 raw41419step1Labels := by
      have ha : raw41419step1 = -raw41419step0 := by apply Matrix.ext; change ∀ i j, raw41419step1 i j = -(raw41419step0 i j); unfold raw41419step1 raw41419step0; decide +kernel
      have hl : raw41419step1Labels = raw41419step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1966 node1966Labels := by rfl

theorem canonical41420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41420 raw41420Labels = mixedMoment B node3493 node3493Labels := by
  calc
    mixedMoment B raw41420 raw41420Labels = mixedMoment B raw41420step0 raw41420step0Labels := by
      have ha : raw41420step0 = (fun i j => raw41420 (permutation594 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41420step0 raw41420; decide +kernel
      have hl : raw41420step0Labels = raw41420Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41420 raw41420Labels permutation594 permutation6
    mixedMoment B raw41420step0 raw41420step0Labels = mixedMoment B raw41420step1 raw41420step1Labels := by
      have ha : raw41420step1 = -raw41420step0 := by apply Matrix.ext; change ∀ i j, raw41420step1 i j = -(raw41420step0 i j); unfold raw41420step1 raw41420step0; decide +kernel
      have hl : raw41420step1Labels = raw41420step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3493 node3493Labels := by rfl

theorem canonical41421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41421 raw41421Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw41421 raw41421Labels = mixedMoment B raw41421step0 raw41421step0Labels := by
      have ha : raw41421step0 = (fun i j => raw41421 (permutation389 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41421step0 raw41421; decide +kernel
      have hl : raw41421step0Labels = raw41421Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41421 raw41421Labels permutation389 permutation6
    _ = mixedMoment B node3805 node3805Labels := by rfl

theorem canonical41422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41422 raw41422Labels = mixedMoment B node2807 node2807Labels := by
  calc
    mixedMoment B raw41422 raw41422Labels = mixedMoment B raw41422step0 raw41422step0Labels := by
      have ha : raw41422step0 = (fun i j => raw41422 (permutation623 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41422step0 raw41422; decide +kernel
      have hl : raw41422step0Labels = raw41422Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41422 raw41422Labels permutation623 permutation6
    _ = mixedMoment B node2807 node2807Labels := by rfl

theorem canonical41423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41423 raw41423Labels = mixedMoment B node3703 node3703Labels := by
  calc
    mixedMoment B raw41423 raw41423Labels = mixedMoment B raw41423step0 raw41423step0Labels := by
      have ha : raw41423step0 = (fun i j => raw41423 (permutation399 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41423step0 raw41423; decide +kernel
      have hl : raw41423step0Labels = raw41423Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41423 raw41423Labels permutation399 permutation6
    _ = mixedMoment B node3703 node3703Labels := by rfl

theorem canonical41424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41424 raw41424Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw41424 raw41424Labels = mixedMoment B raw41424step0 raw41424step0Labels := by
      have ha : raw41424step0 = (fun i j => raw41424 (permutation409 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41424step0 raw41424; decide +kernel
      have hl : raw41424step0Labels = raw41424Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41424 raw41424Labels permutation409 permutation6
    _ = mixedMoment B node3689 node3689Labels := by rfl

theorem canonical41425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41425 raw41425Labels = mixedMoment B node1964 node1964Labels := by
  calc
    mixedMoment B raw41425 raw41425Labels = mixedMoment B raw41425step0 raw41425step0Labels := by
      have ha : raw41425step0 = (fun i j => raw41425 (permutation520 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41425step0 raw41425; decide +kernel
      have hl : raw41425step0Labels = raw41425Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41425 raw41425Labels permutation520 permutation6
    mixedMoment B raw41425step0 raw41425step0Labels = mixedMoment B raw41425step1 raw41425step1Labels := by
      have ha : raw41425step1 = -raw41425step0 := by apply Matrix.ext; change ∀ i j, raw41425step1 i j = -(raw41425step0 i j); unfold raw41425step1 raw41425step0; decide +kernel
      have hl : raw41425step1Labels = raw41425step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1964 node1964Labels := by rfl

theorem canonical41426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41426 raw41426Labels = mixedMoment B node3496 node3496Labels := by
  calc
    mixedMoment B raw41426 raw41426Labels = mixedMoment B raw41426step0 raw41426step0Labels := by
      have ha : raw41426step0 = (fun i j => raw41426 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41426step0 raw41426; decide +kernel
      have hl : raw41426step0Labels = raw41426Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41426 raw41426Labels permutation590 permutation6
    mixedMoment B raw41426step0 raw41426step0Labels = mixedMoment B raw41426step1 raw41426step1Labels := by
      have ha : raw41426step1 = -raw41426step0 := by apply Matrix.ext; change ∀ i j, raw41426step1 i j = -(raw41426step0 i j); unfold raw41426step1 raw41426step0; decide +kernel
      have hl : raw41426step1Labels = raw41426step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3496 node3496Labels := by rfl

theorem canonical41427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41427 raw41427Labels = mixedMoment B node1126 node1126Labels := by
  calc
    mixedMoment B raw41427 raw41427Labels = mixedMoment B raw41427step0 raw41427step0Labels := by
      have ha : raw41427step0 = (fun i j => raw41427 (permutation623 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41427step0 raw41427; decide +kernel
      have hl : raw41427step0Labels = raw41427Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41427 raw41427Labels permutation623 permutation6
    _ = mixedMoment B node1126 node1126Labels := by rfl

theorem canonical41428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41428 raw41428Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw41428 raw41428Labels = mixedMoment B raw41428step0 raw41428step0Labels := by
      have ha : raw41428step0 = (fun i j => raw41428 (permutation541 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41428step0 raw41428; decide +kernel
      have hl : raw41428step0Labels = raw41428Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41428 raw41428Labels permutation541 permutation6
    _ = mixedMoment B node2508 node2508Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical43072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43072 raw43072Labels = mixedMoment B node3255 node3255Labels := by
  calc
    mixedMoment B raw43072 raw43072Labels = mixedMoment B raw43072step0 raw43072step0Labels := by
      have ha : raw43072step0 = (fun i j => raw43072 (permutation648 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43072step0 raw43072; decide +kernel
      have hl : raw43072step0Labels = raw43072Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43072 raw43072Labels permutation648 permutation4
    mixedMoment B raw43072step0 raw43072step0Labels = mixedMoment B raw43072step1 raw43072step1Labels := by
      have ha : raw43072step1 = -raw43072step0 := by apply Matrix.ext; change ∀ i j, raw43072step1 i j = -(raw43072step0 i j); unfold raw43072step1 raw43072step0; decide +kernel
      have hl : raw43072step1Labels = raw43072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43072step1 raw43072step1Labels = mixedMoment B raw43072step2 raw43072step2Labels := by
      have ha : raw43072step2 = raw43072step1 := by apply Matrix.ext; unfold raw43072step2 raw43072step1; decide +kernel
      have hl : raw43072step1Labels = labelEmbedding1 ∘ raw43072step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43072step1 raw43072step1Labels raw43072step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3255 node3255Labels := by rfl

theorem canonical43073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43073 raw43073Labels = mixedMoment B node4527 node4527Labels := by
  calc
    mixedMoment B raw43073 raw43073Labels = mixedMoment B raw43073step0 raw43073step0Labels := by
      have ha : raw43073step0 = (fun i j => raw43073 (permutation659 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43073step0 raw43073; decide +kernel
      have hl : raw43073step0Labels = raw43073Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43073 raw43073Labels permutation659 permutation6
    _ = mixedMoment B node4527 node4527Labels := by rfl

theorem canonical43074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43074 raw43074Labels = mixedMoment B node1505 node1505Labels := by
  calc
    mixedMoment B raw43074 raw43074Labels = mixedMoment B raw43074step0 raw43074step0Labels := by
      have hz : ∀ j, raw43074 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43074step0 = (fun i j => raw43074 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43074step0 raw43074; decide +kernel
      have hl : raw43074step0Labels = raw43074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43074 raw43074Labels permutation434 hz
    mixedMoment B raw43074step0 raw43074step0Labels = mixedMoment B raw43074step1 raw43074step1Labels := by
      have ha : raw43074step1 = (fun i j => raw43074step0 (permutation129 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43074step1 raw43074step0; decide +kernel
      have hl : raw43074step1Labels = raw43074step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43074step0 raw43074step0Labels permutation129 permutation4
    mixedMoment B raw43074step1 raw43074step1Labels = mixedMoment B raw43074step2 raw43074step2Labels := by
      have ha : raw43074step2 = -raw43074step1 := by apply Matrix.ext; change ∀ i j, raw43074step2 i j = -(raw43074step1 i j); unfold raw43074step2 raw43074step1; decide +kernel
      have hl : raw43074step2Labels = raw43074step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43074step2 raw43074step2Labels = mixedMoment B raw43074step3 raw43074step3Labels := by
      have ha : raw43074step3 = raw43074step2 := by apply Matrix.ext; unfold raw43074step3 raw43074step2; decide +kernel
      have hl : raw43074step2Labels = labelEmbedding1 ∘ raw43074step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43074step2 raw43074step2Labels raw43074step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1505 node1505Labels := by rfl

theorem canonical43075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43075 raw43075Labels = mixedMoment B node4151 node4151Labels := by
  calc
    mixedMoment B raw43075 raw43075Labels = mixedMoment B raw43075step0 raw43075step0Labels := by
      have hz : ∀ j, raw43075 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43075step0 = (fun i j => raw43075 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43075step0 raw43075; decide +kernel
      have hl : raw43075step0Labels = raw43075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43075 raw43075Labels permutation434 hz
    mixedMoment B raw43075step0 raw43075step0Labels = mixedMoment B raw43075step1 raw43075step1Labels := by
      have ha : raw43075step1 = (fun i j => raw43075step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43075step1 raw43075step0; decide +kernel
      have hl : raw43075step1Labels = raw43075step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43075step0 raw43075step0Labels permutation146 permutation6
    _ = mixedMoment B node4151 node4151Labels := by rfl

theorem canonical43076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43076 raw43076Labels = mixedMoment B node2148 node2148Labels := by
  calc
    mixedMoment B raw43076 raw43076Labels = mixedMoment B raw43076step0 raw43076step0Labels := by
      have ha : raw43076step0 = (fun i j => raw43076 (permutation507 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43076step0 raw43076; decide +kernel
      have hl : raw43076step0Labels = raw43076Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43076 raw43076Labels permutation507 permutation4
    mixedMoment B raw43076step0 raw43076step0Labels = mixedMoment B raw43076step1 raw43076step1Labels := by
      have ha : raw43076step1 = -raw43076step0 := by apply Matrix.ext; change ∀ i j, raw43076step1 i j = -(raw43076step0 i j); unfold raw43076step1 raw43076step0; decide +kernel
      have hl : raw43076step1Labels = raw43076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43076step1 raw43076step1Labels = mixedMoment B raw43076step2 raw43076step2Labels := by
      have ha : raw43076step2 = raw43076step1 := by apply Matrix.ext; unfold raw43076step2 raw43076step1; decide +kernel
      have hl : raw43076step1Labels = labelEmbedding1 ∘ raw43076step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43076step1 raw43076step1Labels raw43076step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2148 node2148Labels := by rfl

theorem canonical43077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43077 raw43077Labels = mixedMoment B node4666 node4666Labels := by
  calc
    mixedMoment B raw43077 raw43077Labels = mixedMoment B raw43077step0 raw43077step0Labels := by
      have ha : raw43077step0 = (fun i j => raw43077 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43077step0 raw43077; decide +kernel
      have hl : raw43077step0Labels = raw43077Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43077 raw43077Labels permutation514 permutation6
    _ = mixedMoment B node4666 node4666Labels := by rfl

theorem canonical43078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43078 raw43078Labels = mixedMoment B node3511 node3511Labels := by
  calc
    mixedMoment B raw43078 raw43078Labels = mixedMoment B raw43078step0 raw43078step0Labels := by
      have ha : raw43078step0 = (fun i j => raw43078 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw43078step0 raw43078; decide +kernel
      have hl : raw43078step0Labels = raw43078Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43078 raw43078Labels permutation683 permutation2
    mixedMoment B raw43078step0 raw43078step0Labels = mixedMoment B raw43078step1 raw43078step1Labels := by
      have ha : raw43078step1 = -raw43078step0 := by apply Matrix.ext; change ∀ i j, raw43078step1 i j = -(raw43078step0 i j); unfold raw43078step1 raw43078step0; decide +kernel
      have hl : raw43078step1Labels = raw43078step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43078step1 raw43078step1Labels = mixedMoment B raw43078step2 raw43078step2Labels := by
      have ha : raw43078step2 = raw43078step1 := by apply Matrix.ext; unfold raw43078step2 raw43078step1; decide +kernel
      have hl : raw43078step1Labels = labelEmbedding1 ∘ raw43078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43078step1 raw43078step1Labels raw43078step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3511 node3511Labels := by rfl

theorem canonical43079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43079 raw43079Labels = mixedMoment B node4958 node4958Labels := by
  calc
    mixedMoment B raw43079 raw43079Labels = mixedMoment B raw43079step0 raw43079step0Labels := by
      have ha : raw43079step0 = (fun i j => raw43079 (permutation659 i) (permutation7 j)) := by apply Matrix.ext; unfold raw43079step0 raw43079; decide +kernel
      have hl : raw43079step0Labels = raw43079Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43079 raw43079Labels permutation659 permutation7
    mixedMoment B raw43079step0 raw43079step0Labels = mixedMoment B raw43079step1 raw43079step1Labels := by
      have ha : raw43079step1 = raw43079step0 := by apply Matrix.ext; unfold raw43079step1 raw43079step0; decide +kernel
      have hl : raw43079step0Labels = labelEmbedding6 ∘ raw43079step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43079step0 raw43079step0Labels raw43079step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4958 node4958Labels := by rfl

theorem canonical43080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43080 raw43080Labels = mixedMoment B node3261 node3261Labels := by
  calc
    mixedMoment B raw43080 raw43080Labels = mixedMoment B raw43080step0 raw43080step0Labels := by
      have ha : raw43080step0 = (fun i j => raw43080 (permutation650 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43080step0 raw43080; decide +kernel
      have hl : raw43080step0Labels = raw43080Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43080 raw43080Labels permutation650 permutation4
    mixedMoment B raw43080step0 raw43080step0Labels = mixedMoment B raw43080step1 raw43080step1Labels := by
      have ha : raw43080step1 = -raw43080step0 := by apply Matrix.ext; change ∀ i j, raw43080step1 i j = -(raw43080step0 i j); unfold raw43080step1 raw43080step0; decide +kernel
      have hl : raw43080step1Labels = raw43080step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43080step1 raw43080step1Labels = mixedMoment B raw43080step2 raw43080step2Labels := by
      have ha : raw43080step2 = raw43080step1 := by apply Matrix.ext; unfold raw43080step2 raw43080step1; decide +kernel
      have hl : raw43080step1Labels = labelEmbedding1 ∘ raw43080step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43080step1 raw43080step1Labels raw43080step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3261 node3261Labels := by rfl

theorem canonical43081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43081 raw43081Labels = mixedMoment B node4530 node4530Labels := by
  calc
    mixedMoment B raw43081 raw43081Labels = mixedMoment B raw43081step0 raw43081step0Labels := by
      have ha : raw43081step0 = (fun i j => raw43081 (permutation659 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43081step0 raw43081; decide +kernel
      have hl : raw43081step0Labels = raw43081Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43081 raw43081Labels permutation659 permutation6
    _ = mixedMoment B node4530 node4530Labels := by rfl

theorem canonical43082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43082 raw43082Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw43082 raw43082Labels = mixedMoment B raw43082step0 raw43082step0Labels := by
      have hz : ∀ j, raw43082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43082step0 = (fun i j => raw43082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43082step0 raw43082; decide +kernel
      have hl : raw43082step0Labels = raw43082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43082 raw43082Labels permutation434 hz
    mixedMoment B raw43082step0 raw43082step0Labels = mixedMoment B raw43082step1 raw43082step1Labels := by
      have ha : raw43082step1 = (fun i j => raw43082step0 (permutation132 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43082step1 raw43082step0; decide +kernel
      have hl : raw43082step1Labels = raw43082step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43082step0 raw43082step0Labels permutation132 permutation4
    mixedMoment B raw43082step1 raw43082step1Labels = mixedMoment B raw43082step2 raw43082step2Labels := by
      have ha : raw43082step2 = -raw43082step1 := by apply Matrix.ext; change ∀ i j, raw43082step2 i j = -(raw43082step1 i j); unfold raw43082step2 raw43082step1; decide +kernel
      have hl : raw43082step2Labels = raw43082step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43082step2 raw43082step2Labels = mixedMoment B raw43082step3 raw43082step3Labels := by
      have ha : raw43082step3 = raw43082step2 := by apply Matrix.ext; unfold raw43082step3 raw43082step2; decide +kernel
      have hl : raw43082step2Labels = labelEmbedding1 ∘ raw43082step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43082step2 raw43082step2Labels raw43082step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1515 node1515Labels := by rfl

theorem canonical43083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43083 raw43083Labels = mixedMoment B node4155 node4155Labels := by
  calc
    mixedMoment B raw43083 raw43083Labels = mixedMoment B raw43083step0 raw43083step0Labels := by
      have hz : ∀ j, raw43083 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43083step0 = (fun i j => raw43083 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43083step0 raw43083; decide +kernel
      have hl : raw43083step0Labels = raw43083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43083 raw43083Labels permutation434 hz
    mixedMoment B raw43083step0 raw43083step0Labels = mixedMoment B raw43083step1 raw43083step1Labels := by
      have ha : raw43083step1 = (fun i j => raw43083step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43083step1 raw43083step0; decide +kernel
      have hl : raw43083step1Labels = raw43083step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43083step0 raw43083step0Labels permutation146 permutation6
    _ = mixedMoment B node4155 node4155Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 384) =
      Integer.Sparse.eval keyMomentRow384 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 384).leftCharge (GramAssembly.key 384).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 356) := by
    have ha : gramCharges (GramAssembly.key 384).leftCharge (GramAssembly.key 384).rightCharge = raw39832 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39832Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39832 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 384).leftCharge (GramAssembly.key 384).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow384, Integer.Sparse.eval]

theorem keyMoment385 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 385) =
      Integer.Sparse.eval keyMomentRow385 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 385).leftCharge (GramAssembly.key 385).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 398) := by
    have ha : gramCharges (GramAssembly.key 385).leftCharge (GramAssembly.key 385).rightCharge = raw39833 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39833Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39833 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 385).leftCharge (GramAssembly.key 385).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow385, Integer.Sparse.eval]

theorem keyMoment386 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 386) =
      Integer.Sparse.eval keyMomentRow386 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 386).leftCharge (GramAssembly.key 386).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 467) := by
    have ha : gramCharges (GramAssembly.key 386).leftCharge (GramAssembly.key 386).rightCharge = raw39834 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39834Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39834 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 386).leftCharge (GramAssembly.key 386).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow386, Integer.Sparse.eval]

theorem keyMoment387 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 387) =
      Integer.Sparse.eval keyMomentRow387 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 387).leftCharge (GramAssembly.key 387).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 446) := by
    have ha : gramCharges (GramAssembly.key 387).leftCharge (GramAssembly.key 387).rightCharge = raw39835 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39835Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39835 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 387).leftCharge (GramAssembly.key 387).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow387, Integer.Sparse.eval]

theorem keyMoment388 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 388) =
      Integer.Sparse.eval keyMomentRow388 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 388).leftCharge (GramAssembly.key 388).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 288) := by
    have ha : gramCharges (GramAssembly.key 388).leftCharge (GramAssembly.key 388).rightCharge = raw39836 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39836Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39836 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 388).leftCharge (GramAssembly.key 388).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow388, Integer.Sparse.eval]

theorem keyMoment389 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 389) =
      Integer.Sparse.eval keyMomentRow389 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 389).leftCharge (GramAssembly.key 389).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 434) := by
    have ha : gramCharges (GramAssembly.key 389).leftCharge (GramAssembly.key 389).rightCharge = raw39837 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39837Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39837 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 389).leftCharge (GramAssembly.key 389).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow389, Integer.Sparse.eval]

theorem keyMoment390 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 390) =
      Integer.Sparse.eval keyMomentRow390 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 390).leftCharge (GramAssembly.key 390).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 280) := by
    have ha : gramCharges (GramAssembly.key 390).leftCharge (GramAssembly.key 390).rightCharge = raw39838 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39838Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39838 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 390).leftCharge (GramAssembly.key 390).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow390, Integer.Sparse.eval]

theorem keyMoment391 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 391) =
      Integer.Sparse.eval keyMomentRow391 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 391).leftCharge (GramAssembly.key 391).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 278) := by
    have ha : gramCharges (GramAssembly.key 391).leftCharge (GramAssembly.key 391).rightCharge = raw39839 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39839Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39839 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 391).leftCharge (GramAssembly.key 391).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow391, Integer.Sparse.eval]

theorem keyMoment392 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 392) =
      Integer.Sparse.eval keyMomentRow392 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 392).leftCharge (GramAssembly.key 392).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 313) := by
    have ha : gramCharges (GramAssembly.key 392).leftCharge (GramAssembly.key 392).rightCharge = raw39840 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39840Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39840 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 392).leftCharge (GramAssembly.key 392).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow392, Integer.Sparse.eval]

theorem keyMoment393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 393) =
      Integer.Sparse.eval keyMomentRow393 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 393).leftCharge (GramAssembly.key 393).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 123) := by
    have ha : gramCharges (GramAssembly.key 393).leftCharge (GramAssembly.key 393).rightCharge = raw39841 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39841Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39841 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 393).leftCharge (GramAssembly.key 393).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow393, Integer.Sparse.eval]

theorem keyMoment394 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 394) =
      Integer.Sparse.eval keyMomentRow394 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 394).leftCharge (GramAssembly.key 394).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 6) := by
    have ha : gramCharges (GramAssembly.key 394).leftCharge (GramAssembly.key 394).rightCharge = raw39842 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39842Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39842 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 394).leftCharge (GramAssembly.key 394).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow394, Integer.Sparse.eval]

theorem keyMoment395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 395) =
      Integer.Sparse.eval keyMomentRow395 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 395).leftCharge (GramAssembly.key 395).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 114) := by
    have ha : gramCharges (GramAssembly.key 395).leftCharge (GramAssembly.key 395).rightCharge = raw39843 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39843Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39843 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 395).leftCharge (GramAssembly.key 395).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow395, Integer.Sparse.eval]

theorem keyMoment396 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 396) =
      Integer.Sparse.eval keyMomentRow396 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 396).leftCharge (GramAssembly.key 396).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 29) := by
    have ha : gramCharges (GramAssembly.key 396).leftCharge (GramAssembly.key 396).rightCharge = raw39844 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39844Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39844 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 396).leftCharge (GramAssembly.key 396).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow396, Integer.Sparse.eval]

theorem keyMoment397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 397) =
      Integer.Sparse.eval keyMomentRow397 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 397).leftCharge (GramAssembly.key 397).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 101) := by
    have ha : gramCharges (GramAssembly.key 397).leftCharge (GramAssembly.key 397).rightCharge = raw39845 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39845Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39845 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 397).leftCharge (GramAssembly.key 397).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow397, Integer.Sparse.eval]

theorem keyMoment398 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 398) =
      Integer.Sparse.eval keyMomentRow398 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 398).leftCharge (GramAssembly.key 398).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 142) := by
    have ha : gramCharges (GramAssembly.key 398).leftCharge (GramAssembly.key 398).rightCharge = raw39846 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39846Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39846 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 398).leftCharge (GramAssembly.key 398).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow398, Integer.Sparse.eval]

theorem keyMoment399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 399) =
      Integer.Sparse.eval keyMomentRow399 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 399).leftCharge (GramAssembly.key 399).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 27) := by
    have ha : gramCharges (GramAssembly.key 399).leftCharge (GramAssembly.key 399).rightCharge = raw39847 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39847Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39847 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 399).leftCharge (GramAssembly.key 399).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow399, Integer.Sparse.eval]

theorem keyMoment400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 400) =
      Integer.Sparse.eval keyMomentRow400 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 400).leftCharge (GramAssembly.key 400).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 12) := by
    have ha : gramCharges (GramAssembly.key 400).leftCharge (GramAssembly.key 400).rightCharge = raw39848 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39848Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39848 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 400).leftCharge (GramAssembly.key 400).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow400, Integer.Sparse.eval]

theorem keyMoment401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 401) =
      Integer.Sparse.eval keyMomentRow401 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 401).leftCharge (GramAssembly.key 401).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 10) := by
    have ha : gramCharges (GramAssembly.key 401).leftCharge (GramAssembly.key 401).rightCharge = raw39849 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39849Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39849 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 401).leftCharge (GramAssembly.key 401).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow401, Integer.Sparse.eval]

theorem keyMoment402 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 402) =
      Integer.Sparse.eval keyMomentRow402 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 402).leftCharge (GramAssembly.key 402).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 229) := by
    have ha : gramCharges (GramAssembly.key 402).leftCharge (GramAssembly.key 402).rightCharge = raw39850 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39850Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39850 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 402).leftCharge (GramAssembly.key 402).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow402, Integer.Sparse.eval]

theorem keyMoment403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 403) =
      Integer.Sparse.eval keyMomentRow403 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 403).leftCharge (GramAssembly.key 403).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 240) := by
    have ha : gramCharges (GramAssembly.key 403).leftCharge (GramAssembly.key 403).rightCharge = raw39851 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39851Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39851 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 403).leftCharge (GramAssembly.key 403).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow403, Integer.Sparse.eval]

theorem keyMoment404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 404) =
      Integer.Sparse.eval keyMomentRow404 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 404).leftCharge (GramAssembly.key 404).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 184) := by
    have ha : gramCharges (GramAssembly.key 404).leftCharge (GramAssembly.key 404).rightCharge = raw39852 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39852Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39852 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 404).leftCharge (GramAssembly.key 404).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow404, Integer.Sparse.eval]

theorem keyMoment405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 405) =
      Integer.Sparse.eval keyMomentRow405 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 405).leftCharge (GramAssembly.key 405).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 167) := by
    have ha : gramCharges (GramAssembly.key 405).leftCharge (GramAssembly.key 405).rightCharge = raw39853 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39853Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39853 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 405).leftCharge (GramAssembly.key 405).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow405, Integer.Sparse.eval]

theorem keyMoment406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 406) =
      Integer.Sparse.eval keyMomentRow406 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 406).leftCharge (GramAssembly.key 406).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 434) := by
    have ha : gramCharges (GramAssembly.key 406).leftCharge (GramAssembly.key 406).rightCharge = raw39854 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39854Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39854 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 406).leftCharge (GramAssembly.key 406).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow406, Integer.Sparse.eval]

theorem keyMoment407 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 407) =
      Integer.Sparse.eval keyMomentRow407 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 407).leftCharge (GramAssembly.key 407).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 427) := by
    have ha : gramCharges (GramAssembly.key 407).leftCharge (GramAssembly.key 407).rightCharge = raw39855 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39855Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39855 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 407).leftCharge (GramAssembly.key 407).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow407, Integer.Sparse.eval]

theorem keyMoment408 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 408) =
      Integer.Sparse.eval keyMomentRow408 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 408).leftCharge (GramAssembly.key 408).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 435) := by
    have ha : gramCharges (GramAssembly.key 408).leftCharge (GramAssembly.key 408).rightCharge = raw39856 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39856Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39856 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 408).leftCharge (GramAssembly.key 408).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow408, Integer.Sparse.eval]

theorem keyMoment409 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 409) =
      Integer.Sparse.eval keyMomentRow409 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 409).leftCharge (GramAssembly.key 409).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 432) := by
    have ha : gramCharges (GramAssembly.key 409).leftCharge (GramAssembly.key 409).rightCharge = raw39857 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39857Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39857 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 409).leftCharge (GramAssembly.key 409).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow409, Integer.Sparse.eval]

theorem keyMoment410 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 410) =
      Integer.Sparse.eval keyMomentRow410 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 410).leftCharge (GramAssembly.key 410).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 282) := by
    have ha : gramCharges (GramAssembly.key 410).leftCharge (GramAssembly.key 410).rightCharge = raw39858 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39858Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39858 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 410).leftCharge (GramAssembly.key 410).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow410, Integer.Sparse.eval]

theorem keyMoment411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 411) =
      Integer.Sparse.eval keyMomentRow411 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 411).leftCharge (GramAssembly.key 411).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 426) := by
    have ha : gramCharges (GramAssembly.key 411).leftCharge (GramAssembly.key 411).rightCharge = raw39859 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39859Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39859 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 411).leftCharge (GramAssembly.key 411).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow411, Integer.Sparse.eval]

theorem keyMoment412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 412) =
      Integer.Sparse.eval keyMomentRow412 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 412).leftCharge (GramAssembly.key 412).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 428) := by
    have ha : gramCharges (GramAssembly.key 412).leftCharge (GramAssembly.key 412).rightCharge = raw39860 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39860Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39860 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 412).leftCharge (GramAssembly.key 412).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow412, Integer.Sparse.eval]

theorem keyMoment413 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 413) =
      Integer.Sparse.eval keyMomentRow413 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 413).leftCharge (GramAssembly.key 413).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 429) := by
    have ha : gramCharges (GramAssembly.key 413).leftCharge (GramAssembly.key 413).rightCharge = raw39861 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39861Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39861 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 413).leftCharge (GramAssembly.key 413).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow413, Integer.Sparse.eval]

theorem keyMoment414 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 414) =
      Integer.Sparse.eval keyMomentRow414 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 414).leftCharge (GramAssembly.key 414).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 309) := by
    have ha : gramCharges (GramAssembly.key 414).leftCharge (GramAssembly.key 414).rightCharge = raw39862 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39862Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39862 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 414).leftCharge (GramAssembly.key 414).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow414, Integer.Sparse.eval]

theorem keyMoment415 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 415) =
      Integer.Sparse.eval keyMomentRow415 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 415).leftCharge (GramAssembly.key 415).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 325) := by
    have ha : gramCharges (GramAssembly.key 415).leftCharge (GramAssembly.key 415).rightCharge = raw39863 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39863Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39863 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 415).leftCharge (GramAssembly.key 415).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow415, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt384 : keyMomentRows (384 : Fin 2886) =
    keyMomentRow384 := by decide +kernel

theorem keyMomentRowsAt385 : keyMomentRows (385 : Fin 2886) =
    keyMomentRow385 := by decide +kernel

theorem keyMomentRowsAt386 : keyMomentRows (386 : Fin 2886) =
    keyMomentRow386 := by decide +kernel

theorem keyMomentRowsAt387 : keyMomentRows (387 : Fin 2886) =
    keyMomentRow387 := by decide +kernel

theorem keyMomentRowsAt388 : keyMomentRows (388 : Fin 2886) =
    keyMomentRow388 := by decide +kernel

theorem keyMomentRowsAt389 : keyMomentRows (389 : Fin 2886) =
    keyMomentRow389 := by decide +kernel

theorem keyMomentRowsAt390 : keyMomentRows (390 : Fin 2886) =
    keyMomentRow390 := by decide +kernel

theorem keyMomentRowsAt391 : keyMomentRows (391 : Fin 2886) =
    keyMomentRow391 := by decide +kernel

theorem keyMomentRowsAt392 : keyMomentRows (392 : Fin 2886) =
    keyMomentRow392 := by decide +kernel

theorem keyMomentRowsAt393 : keyMomentRows (393 : Fin 2886) =
    keyMomentRow393 := by decide +kernel

theorem keyMomentRowsAt394 : keyMomentRows (394 : Fin 2886) =
    keyMomentRow394 := by decide +kernel

theorem keyMomentRowsAt395 : keyMomentRows (395 : Fin 2886) =
    keyMomentRow395 := by decide +kernel

theorem keyMomentRowsAt396 : keyMomentRows (396 : Fin 2886) =
    keyMomentRow396 := by decide +kernel

theorem keyMomentRowsAt397 : keyMomentRows (397 : Fin 2886) =
    keyMomentRow397 := by decide +kernel

theorem keyMomentRowsAt398 : keyMomentRows (398 : Fin 2886) =
    keyMomentRow398 := by decide +kernel

theorem keyMomentRowsAt399 : keyMomentRows (399 : Fin 2886) =
    keyMomentRow399 := by decide +kernel

theorem keyMomentRowsAt400 : keyMomentRows (400 : Fin 2886) =
    keyMomentRow400 := by decide +kernel

theorem keyMomentRowsAt401 : keyMomentRows (401 : Fin 2886) =
    keyMomentRow401 := by decide +kernel

theorem keyMomentRowsAt402 : keyMomentRows (402 : Fin 2886) =
    keyMomentRow402 := by decide +kernel

theorem keyMomentRowsAt403 : keyMomentRows (403 : Fin 2886) =
    keyMomentRow403 := by decide +kernel

theorem keyMomentRowsAt404 : keyMomentRows (404 : Fin 2886) =
    keyMomentRow404 := by decide +kernel

theorem keyMomentRowsAt405 : keyMomentRows (405 : Fin 2886) =
    keyMomentRow405 := by decide +kernel

theorem keyMomentRowsAt406 : keyMomentRows (406 : Fin 2886) =
    keyMomentRow406 := by decide +kernel

theorem keyMomentRowsAt407 : keyMomentRows (407 : Fin 2886) =
    keyMomentRow407 := by decide +kernel

theorem keyMomentRowsAt408 : keyMomentRows (408 : Fin 2886) =
    keyMomentRow408 := by decide +kernel

theorem keyMomentRowsAt409 : keyMomentRows (409 : Fin 2886) =
    keyMomentRow409 := by decide +kernel

theorem keyMomentRowsAt410 : keyMomentRows (410 : Fin 2886) =
    keyMomentRow410 := by decide +kernel

theorem keyMomentRowsAt411 : keyMomentRows (411 : Fin 2886) =
    keyMomentRow411 := by decide +kernel

theorem keyMomentRowsAt412 : keyMomentRows (412 : Fin 2886) =
    keyMomentRow412 := by decide +kernel

theorem keyMomentRowsAt413 : keyMomentRows (413 : Fin 2886) =
    keyMomentRow413 := by decide +kernel

theorem keyMomentRowsAt414 : keyMomentRows (414 : Fin 2886) =
    keyMomentRow414 := by decide +kernel

theorem keyMomentRowsAt415 : keyMomentRows (415 : Fin 2886) =
    keyMomentRow415 := by decide +kernel

theorem keyMomentChunkSound12 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 12) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 384 ∨ k.val = 385 ∨ k.val = 386 ∨ k.val = 387 ∨ k.val = 388 ∨ k.val = 389 ∨ k.val = 390 ∨ k.val = 391 ∨ k.val = 392 ∨ k.val = 393 ∨ k.val = 394 ∨ k.val = 395 ∨ k.val = 396 ∨ k.val = 397 ∨ k.val = 398 ∨ k.val = 399 ∨ k.val = 400 ∨ k.val = 401 ∨ k.val = 402 ∨ k.val = 403 ∨ k.val = 404 ∨ k.val = 405 ∨ k.val = 406 ∨ k.val = 407 ∨ k.val = 408 ∨ k.val = 409 ∨ k.val = 410 ∨ k.val = 411 ∨ k.val = 412 ∨ k.val = 413 ∨ k.val = 414 ∨ k.val = 415 := by omega
  rcases heq with h384 | h385 | h386 | h387 | h388 | h389 | h390 | h391 | h392 | h393 | h394 | h395 | h396 | h397 | h398 | h399 | h400 | h401 | h402 | h403 | h404 | h405 | h406 | h407 | h408 | h409 | h410 | h411 | h412 | h413 | h414 | h415
  · have he : k = (384 : Fin 2886) := Fin.ext h384
    subst k
    rw [keyMomentRowsAt384]
    exact keyMoment384 B hB
  · have he : k = (385 : Fin 2886) := Fin.ext h385
    subst k
    rw [keyMomentRowsAt385]
    exact keyMoment385 B hB
  · have he : k = (386 : Fin 2886) := Fin.ext h386
    subst k
    rw [keyMomentRowsAt386]
    exact keyMoment386 B hB
  · have he : k = (387 : Fin 2886) := Fin.ext h387
    subst k
    rw [keyMomentRowsAt387]
    exact keyMoment387 B hB
  · have he : k = (388 : Fin 2886) := Fin.ext h388
    subst k
    rw [keyMomentRowsAt388]
    exact keyMoment388 B hB
  · have he : k = (389 : Fin 2886) := Fin.ext h389
    subst k
    rw [keyMomentRowsAt389]
    exact keyMoment389 B hB
  · have he : k = (390 : Fin 2886) := Fin.ext h390
    subst k
    rw [keyMomentRowsAt390]
    exact keyMoment390 B hB
  · have he : k = (391 : Fin 2886) := Fin.ext h391
    subst k
    rw [keyMomentRowsAt391]
    exact keyMoment391 B hB
  · have he : k = (392 : Fin 2886) := Fin.ext h392
    subst k
    rw [keyMomentRowsAt392]
    exact keyMoment392 B hB
  · have he : k = (393 : Fin 2886) := Fin.ext h393
    subst k
    rw [keyMomentRowsAt393]
    exact keyMoment393 B hB
  · have he : k = (394 : Fin 2886) := Fin.ext h394
    subst k
    rw [keyMomentRowsAt394]
    exact keyMoment394 B hB
  · have he : k = (395 : Fin 2886) := Fin.ext h395
    subst k
    rw [keyMomentRowsAt395]
    exact keyMoment395 B hB
  · have he : k = (396 : Fin 2886) := Fin.ext h396
    subst k
    rw [keyMomentRowsAt396]
    exact keyMoment396 B hB
  · have he : k = (397 : Fin 2886) := Fin.ext h397
    subst k
    rw [keyMomentRowsAt397]
    exact keyMoment397 B hB
  · have he : k = (398 : Fin 2886) := Fin.ext h398
    subst k
    rw [keyMomentRowsAt398]
    exact keyMoment398 B hB
  · have he : k = (399 : Fin 2886) := Fin.ext h399
    subst k
    rw [keyMomentRowsAt399]
    exact keyMoment399 B hB
  · have he : k = (400 : Fin 2886) := Fin.ext h400
    subst k
    rw [keyMomentRowsAt400]
    exact keyMoment400 B hB
  · have he : k = (401 : Fin 2886) := Fin.ext h401
    subst k
    rw [keyMomentRowsAt401]
    exact keyMoment401 B hB
  · have he : k = (402 : Fin 2886) := Fin.ext h402
    subst k
    rw [keyMomentRowsAt402]
    exact keyMoment402 B hB
  · have he : k = (403 : Fin 2886) := Fin.ext h403
    subst k
    rw [keyMomentRowsAt403]
    exact keyMoment403 B hB
  · have he : k = (404 : Fin 2886) := Fin.ext h404
    subst k
    rw [keyMomentRowsAt404]
    exact keyMoment404 B hB
  · have he : k = (405 : Fin 2886) := Fin.ext h405
    subst k
    rw [keyMomentRowsAt405]
    exact keyMoment405 B hB
  · have he : k = (406 : Fin 2886) := Fin.ext h406
    subst k
    rw [keyMomentRowsAt406]
    exact keyMoment406 B hB
  · have he : k = (407 : Fin 2886) := Fin.ext h407
    subst k
    rw [keyMomentRowsAt407]
    exact keyMoment407 B hB
  · have he : k = (408 : Fin 2886) := Fin.ext h408
    subst k
    rw [keyMomentRowsAt408]
    exact keyMoment408 B hB
  · have he : k = (409 : Fin 2886) := Fin.ext h409
    subst k
    rw [keyMomentRowsAt409]
    exact keyMoment409 B hB
  · have he : k = (410 : Fin 2886) := Fin.ext h410
    subst k
    rw [keyMomentRowsAt410]
    exact keyMoment410 B hB
  · have he : k = (411 : Fin 2886) := Fin.ext h411
    subst k
    rw [keyMomentRowsAt411]
    exact keyMoment411 B hB
  · have he : k = (412 : Fin 2886) := Fin.ext h412
    subst k
    rw [keyMomentRowsAt412]
    exact keyMoment412 B hB
  · have he : k = (413 : Fin 2886) := Fin.ext h413
    subst k
    rw [keyMomentRowsAt413]
    exact keyMoment413 B hB
  · have he : k = (414 : Fin 2886) := Fin.ext h414
    subst k
    rw [keyMomentRowsAt414]
    exact keyMoment414 B hB
  · have he : k = (415 : Fin 2886) := Fin.ext h415
    subst k
    rw [keyMomentRowsAt415]
    exact keyMoment415 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment64 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 64) =
      Integer.Sparse.eval keyMomentRow64 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 64).leftCharge (GramAssembly.key 64).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 159) := by
    have ha : gramCharges (GramAssembly.key 64).leftCharge (GramAssembly.key 64).rightCharge = raw39514 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39514Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39514 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 64).leftCharge (GramAssembly.key 64).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow64, Integer.Sparse.eval]

theorem keyMoment65 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 65) =
      Integer.Sparse.eval keyMomentRow65 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 65).leftCharge (GramAssembly.key 65).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 388) := by
    have ha : gramCharges (GramAssembly.key 65).leftCharge (GramAssembly.key 65).rightCharge = raw39515 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39515Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39515 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 65).leftCharge (GramAssembly.key 65).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow65, Integer.Sparse.eval]

theorem keyMoment66 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 66) =
      Integer.Sparse.eval keyMomentRow66 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 66).leftCharge (GramAssembly.key 66).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 148) := by
    have ha : gramCharges (GramAssembly.key 66).leftCharge (GramAssembly.key 66).rightCharge = raw39516 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39516Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39516 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 66).leftCharge (GramAssembly.key 66).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow66, Integer.Sparse.eval]

theorem keyMoment67 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 67) =
      Integer.Sparse.eval keyMomentRow67 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 67).leftCharge (GramAssembly.key 67).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 342) := by
    have ha : gramCharges (GramAssembly.key 67).leftCharge (GramAssembly.key 67).rightCharge = raw39517 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39517Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39517 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 67).leftCharge (GramAssembly.key 67).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow67, Integer.Sparse.eval]

theorem keyMoment68 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 68) =
      Integer.Sparse.eval keyMomentRow68 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 68).leftCharge (GramAssembly.key 68).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 406) := by
    have ha : gramCharges (GramAssembly.key 68).leftCharge (GramAssembly.key 68).rightCharge = raw39518 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39518Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39518 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 68).leftCharge (GramAssembly.key 68).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow68, Integer.Sparse.eval]

theorem keyMoment69 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 69) =
      Integer.Sparse.eval keyMomentRow69 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 69).leftCharge (GramAssembly.key 69).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 413) := by
    have ha : gramCharges (GramAssembly.key 69).leftCharge (GramAssembly.key 69).rightCharge = raw39519 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39519Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39519 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 69).leftCharge (GramAssembly.key 69).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow69, Integer.Sparse.eval]

theorem keyMoment70 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 70) =
      Integer.Sparse.eval keyMomentRow70 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 70).leftCharge (GramAssembly.key 70).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 416) := by
    have ha : gramCharges (GramAssembly.key 70).leftCharge (GramAssembly.key 70).rightCharge = raw39520 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39520Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39520 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 70).leftCharge (GramAssembly.key 70).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow70, Integer.Sparse.eval]

theorem keyMoment71 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 71) =
      Integer.Sparse.eval keyMomentRow71 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 71).leftCharge (GramAssembly.key 71).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 340) := by
    have ha : gramCharges (GramAssembly.key 71).leftCharge (GramAssembly.key 71).rightCharge = raw39521 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39521Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39521 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 71).leftCharge (GramAssembly.key 71).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow71, Integer.Sparse.eval]

theorem keyMoment72 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 72) =
      Integer.Sparse.eval keyMomentRow72 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 72).leftCharge (GramAssembly.key 72).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 387) := by
    have ha : gramCharges (GramAssembly.key 72).leftCharge (GramAssembly.key 72).rightCharge = raw39522 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39522Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39522 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 72).leftCharge (GramAssembly.key 72).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow72, Integer.Sparse.eval]

theorem keyMoment73 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 73) =
      Integer.Sparse.eval keyMomentRow73 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 73).leftCharge (GramAssembly.key 73).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 328) := by
    have ha : gramCharges (GramAssembly.key 73).leftCharge (GramAssembly.key 73).rightCharge = raw39523 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39523Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39523 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 73).leftCharge (GramAssembly.key 73).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow73, Integer.Sparse.eval]

theorem keyMoment74 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 74) =
      Integer.Sparse.eval keyMomentRow74 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 74).leftCharge (GramAssembly.key 74).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 367) := by
    have ha : gramCharges (GramAssembly.key 74).leftCharge (GramAssembly.key 74).rightCharge = raw39524 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39524Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39524 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 74).leftCharge (GramAssembly.key 74).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow74, Integer.Sparse.eval]

theorem keyMoment75 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 75) =
      Integer.Sparse.eval keyMomentRow75 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 75).leftCharge (GramAssembly.key 75).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 271) := by
    have ha : gramCharges (GramAssembly.key 75).leftCharge (GramAssembly.key 75).rightCharge = raw39525 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39525Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39525 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 75).leftCharge (GramAssembly.key 75).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow75, Integer.Sparse.eval]

theorem keyMoment76 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 76) =
      Integer.Sparse.eval keyMomentRow76 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 76).leftCharge (GramAssembly.key 76).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 264) := by
    have ha : gramCharges (GramAssembly.key 76).leftCharge (GramAssembly.key 76).rightCharge = raw39526 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39526Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39526 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 76).leftCharge (GramAssembly.key 76).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow76, Integer.Sparse.eval]

theorem keyMoment77 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 77) =
      Integer.Sparse.eval keyMomentRow77 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 77).leftCharge (GramAssembly.key 77).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 250) := by
    have ha : gramCharges (GramAssembly.key 77).leftCharge (GramAssembly.key 77).rightCharge = raw39527 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39527Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39527 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 77).leftCharge (GramAssembly.key 77).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow77, Integer.Sparse.eval]

theorem keyMoment78 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 78) =
      Integer.Sparse.eval keyMomentRow78 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 78).leftCharge (GramAssembly.key 78).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 188) := by
    have ha : gramCharges (GramAssembly.key 78).leftCharge (GramAssembly.key 78).rightCharge = raw39528 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39528Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39528 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 78).leftCharge (GramAssembly.key 78).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow78, Integer.Sparse.eval]

theorem keyMoment79 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 79) =
      Integer.Sparse.eval keyMomentRow79 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 79).leftCharge (GramAssembly.key 79).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 228) := by
    have ha : gramCharges (GramAssembly.key 79).leftCharge (GramAssembly.key 79).rightCharge = raw39529 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39529Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39529 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 79).leftCharge (GramAssembly.key 79).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow79, Integer.Sparse.eval]

theorem keyMoment80 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 80) =
      Integer.Sparse.eval keyMomentRow80 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 80).leftCharge (GramAssembly.key 80).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 225) := by
    have ha : gramCharges (GramAssembly.key 80).leftCharge (GramAssembly.key 80).rightCharge = raw39530 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39530Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39530 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 80).leftCharge (GramAssembly.key 80).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow80, Integer.Sparse.eval]

theorem keyMoment81 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 81) =
      Integer.Sparse.eval keyMomentRow81 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 81).leftCharge (GramAssembly.key 81).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 181) := by
    have ha : gramCharges (GramAssembly.key 81).leftCharge (GramAssembly.key 81).rightCharge = raw39531 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39531Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39531 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 81).leftCharge (GramAssembly.key 81).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow81, Integer.Sparse.eval]

theorem keyMoment82 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 82) =
      Integer.Sparse.eval keyMomentRow82 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 82).leftCharge (GramAssembly.key 82).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 170) := by
    have ha : gramCharges (GramAssembly.key 82).leftCharge (GramAssembly.key 82).rightCharge = raw39532 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39532Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39532 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 82).leftCharge (GramAssembly.key 82).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow82, Integer.Sparse.eval]

theorem keyMoment83 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 83) =
      Integer.Sparse.eval keyMomentRow83 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 83).leftCharge (GramAssembly.key 83).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 194) := by
    have ha : gramCharges (GramAssembly.key 83).leftCharge (GramAssembly.key 83).rightCharge = raw39533 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39533Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39533 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 83).leftCharge (GramAssembly.key 83).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow83, Integer.Sparse.eval]

theorem keyMoment84 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 84) =
      Integer.Sparse.eval keyMomentRow84 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 84).leftCharge (GramAssembly.key 84).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 225) := by
    have ha : gramCharges (GramAssembly.key 84).leftCharge (GramAssembly.key 84).rightCharge = raw39534 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39534Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39534 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 84).leftCharge (GramAssembly.key 84).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow84, Integer.Sparse.eval]

theorem keyMoment85 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 85) =
      Integer.Sparse.eval keyMomentRow85 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 85).leftCharge (GramAssembly.key 85).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 258) := by
    have ha : gramCharges (GramAssembly.key 85).leftCharge (GramAssembly.key 85).rightCharge = raw39535 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39535Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39535 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 85).leftCharge (GramAssembly.key 85).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow85, Integer.Sparse.eval]

theorem keyMoment86 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 86) =
      Integer.Sparse.eval keyMomentRow86 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 86).leftCharge (GramAssembly.key 86).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 166) := by
    have ha : gramCharges (GramAssembly.key 86).leftCharge (GramAssembly.key 86).rightCharge = raw39536 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39536Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39536 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 86).leftCharge (GramAssembly.key 86).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow86, Integer.Sparse.eval]

theorem keyMoment87 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 87) =
      Integer.Sparse.eval keyMomentRow87 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 87).leftCharge (GramAssembly.key 87).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 208) := by
    have ha : gramCharges (GramAssembly.key 87).leftCharge (GramAssembly.key 87).rightCharge = raw39537 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39537Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39537 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 87).leftCharge (GramAssembly.key 87).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow87, Integer.Sparse.eval]

theorem keyMoment88 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 88) =
      Integer.Sparse.eval keyMomentRow88 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 88).leftCharge (GramAssembly.key 88).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 218) := by
    have ha : gramCharges (GramAssembly.key 88).leftCharge (GramAssembly.key 88).rightCharge = raw39538 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39538Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39538 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 88).leftCharge (GramAssembly.key 88).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow88, Integer.Sparse.eval]

theorem keyMoment89 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 89) =
      Integer.Sparse.eval keyMomentRow89 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 89).leftCharge (GramAssembly.key 89).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 166) := by
    have ha : gramCharges (GramAssembly.key 89).leftCharge (GramAssembly.key 89).rightCharge = raw39539 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39539Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39539 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 89).leftCharge (GramAssembly.key 89).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow89, Integer.Sparse.eval]

theorem keyMoment90 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 90) =
      Integer.Sparse.eval keyMomentRow90 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 90).leftCharge (GramAssembly.key 90).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 264) := by
    have ha : gramCharges (GramAssembly.key 90).leftCharge (GramAssembly.key 90).rightCharge = raw39540 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39540Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39540 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 90).leftCharge (GramAssembly.key 90).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow90, Integer.Sparse.eval]

theorem keyMoment91 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 91) =
      Integer.Sparse.eval keyMomentRow91 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 91).leftCharge (GramAssembly.key 91).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 263) := by
    have ha : gramCharges (GramAssembly.key 91).leftCharge (GramAssembly.key 91).rightCharge = raw39541 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39541Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39541 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 91).leftCharge (GramAssembly.key 91).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow91, Integer.Sparse.eval]

theorem keyMoment92 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 92) =
      Integer.Sparse.eval keyMomentRow92 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 92).leftCharge (GramAssembly.key 92).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 246) := by
    have ha : gramCharges (GramAssembly.key 92).leftCharge (GramAssembly.key 92).rightCharge = raw39542 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39542Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39542 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 92).leftCharge (GramAssembly.key 92).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow92, Integer.Sparse.eval]

theorem keyMoment93 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 93) =
      Integer.Sparse.eval keyMomentRow93 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 93).leftCharge (GramAssembly.key 93).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 193) := by
    have ha : gramCharges (GramAssembly.key 93).leftCharge (GramAssembly.key 93).rightCharge = raw39543 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39543Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39543 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 93).leftCharge (GramAssembly.key 93).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow93, Integer.Sparse.eval]

theorem keyMoment94 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 94) =
      Integer.Sparse.eval keyMomentRow94 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 94).leftCharge (GramAssembly.key 94).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 165) := by
    have ha : gramCharges (GramAssembly.key 94).leftCharge (GramAssembly.key 94).rightCharge = raw39544 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39544Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39544 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 94).leftCharge (GramAssembly.key 94).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow94, Integer.Sparse.eval]

theorem keyMoment95 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 95) =
      Integer.Sparse.eval keyMomentRow95 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 95).leftCharge (GramAssembly.key 95).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 191) := by
    have ha : gramCharges (GramAssembly.key 95).leftCharge (GramAssembly.key 95).rightCharge = raw39545 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39545Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39545 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 95).leftCharge (GramAssembly.key 95).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow95, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt64 : keyMomentRows (64 : Fin 2886) =
    keyMomentRow64 := by decide +kernel

theorem keyMomentRowsAt65 : keyMomentRows (65 : Fin 2886) =
    keyMomentRow65 := by decide +kernel

theorem keyMomentRowsAt66 : keyMomentRows (66 : Fin 2886) =
    keyMomentRow66 := by decide +kernel

theorem keyMomentRowsAt67 : keyMomentRows (67 : Fin 2886) =
    keyMomentRow67 := by decide +kernel

theorem keyMomentRowsAt68 : keyMomentRows (68 : Fin 2886) =
    keyMomentRow68 := by decide +kernel

theorem keyMomentRowsAt69 : keyMomentRows (69 : Fin 2886) =
    keyMomentRow69 := by decide +kernel

theorem keyMomentRowsAt70 : keyMomentRows (70 : Fin 2886) =
    keyMomentRow70 := by decide +kernel

theorem keyMomentRowsAt71 : keyMomentRows (71 : Fin 2886) =
    keyMomentRow71 := by decide +kernel

theorem keyMomentRowsAt72 : keyMomentRows (72 : Fin 2886) =
    keyMomentRow72 := by decide +kernel

theorem keyMomentRowsAt73 : keyMomentRows (73 : Fin 2886) =
    keyMomentRow73 := by decide +kernel

theorem keyMomentRowsAt74 : keyMomentRows (74 : Fin 2886) =
    keyMomentRow74 := by decide +kernel

theorem keyMomentRowsAt75 : keyMomentRows (75 : Fin 2886) =
    keyMomentRow75 := by decide +kernel

theorem keyMomentRowsAt76 : keyMomentRows (76 : Fin 2886) =
    keyMomentRow76 := by decide +kernel

theorem keyMomentRowsAt77 : keyMomentRows (77 : Fin 2886) =
    keyMomentRow77 := by decide +kernel

theorem keyMomentRowsAt78 : keyMomentRows (78 : Fin 2886) =
    keyMomentRow78 := by decide +kernel

theorem keyMomentRowsAt79 : keyMomentRows (79 : Fin 2886) =
    keyMomentRow79 := by decide +kernel

theorem keyMomentRowsAt80 : keyMomentRows (80 : Fin 2886) =
    keyMomentRow80 := by decide +kernel

theorem keyMomentRowsAt81 : keyMomentRows (81 : Fin 2886) =
    keyMomentRow81 := by decide +kernel

theorem keyMomentRowsAt82 : keyMomentRows (82 : Fin 2886) =
    keyMomentRow82 := by decide +kernel

theorem keyMomentRowsAt83 : keyMomentRows (83 : Fin 2886) =
    keyMomentRow83 := by decide +kernel

theorem keyMomentRowsAt84 : keyMomentRows (84 : Fin 2886) =
    keyMomentRow84 := by decide +kernel

theorem keyMomentRowsAt85 : keyMomentRows (85 : Fin 2886) =
    keyMomentRow85 := by decide +kernel

theorem keyMomentRowsAt86 : keyMomentRows (86 : Fin 2886) =
    keyMomentRow86 := by decide +kernel

theorem keyMomentRowsAt87 : keyMomentRows (87 : Fin 2886) =
    keyMomentRow87 := by decide +kernel

theorem keyMomentRowsAt88 : keyMomentRows (88 : Fin 2886) =
    keyMomentRow88 := by decide +kernel

theorem keyMomentRowsAt89 : keyMomentRows (89 : Fin 2886) =
    keyMomentRow89 := by decide +kernel

theorem keyMomentRowsAt90 : keyMomentRows (90 : Fin 2886) =
    keyMomentRow90 := by decide +kernel

theorem keyMomentRowsAt91 : keyMomentRows (91 : Fin 2886) =
    keyMomentRow91 := by decide +kernel

theorem keyMomentRowsAt92 : keyMomentRows (92 : Fin 2886) =
    keyMomentRow92 := by decide +kernel

theorem keyMomentRowsAt93 : keyMomentRows (93 : Fin 2886) =
    keyMomentRow93 := by decide +kernel

theorem keyMomentRowsAt94 : keyMomentRows (94 : Fin 2886) =
    keyMomentRow94 := by decide +kernel

theorem keyMomentRowsAt95 : keyMomentRows (95 : Fin 2886) =
    keyMomentRow95 := by decide +kernel

theorem keyMomentChunkSound2 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 2) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 64 ∨ k.val = 65 ∨ k.val = 66 ∨ k.val = 67 ∨ k.val = 68 ∨ k.val = 69 ∨ k.val = 70 ∨ k.val = 71 ∨ k.val = 72 ∨ k.val = 73 ∨ k.val = 74 ∨ k.val = 75 ∨ k.val = 76 ∨ k.val = 77 ∨ k.val = 78 ∨ k.val = 79 ∨ k.val = 80 ∨ k.val = 81 ∨ k.val = 82 ∨ k.val = 83 ∨ k.val = 84 ∨ k.val = 85 ∨ k.val = 86 ∨ k.val = 87 ∨ k.val = 88 ∨ k.val = 89 ∨ k.val = 90 ∨ k.val = 91 ∨ k.val = 92 ∨ k.val = 93 ∨ k.val = 94 ∨ k.val = 95 := by omega
  rcases heq with h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86 | h87 | h88 | h89 | h90 | h91 | h92 | h93 | h94 | h95
  · have he : k = (64 : Fin 2886) := Fin.ext h64
    subst k
    rw [keyMomentRowsAt64]
    exact keyMoment64 B hB
  · have he : k = (65 : Fin 2886) := Fin.ext h65
    subst k
    rw [keyMomentRowsAt65]
    exact keyMoment65 B hB
  · have he : k = (66 : Fin 2886) := Fin.ext h66
    subst k
    rw [keyMomentRowsAt66]
    exact keyMoment66 B hB
  · have he : k = (67 : Fin 2886) := Fin.ext h67
    subst k
    rw [keyMomentRowsAt67]
    exact keyMoment67 B hB
  · have he : k = (68 : Fin 2886) := Fin.ext h68
    subst k
    rw [keyMomentRowsAt68]
    exact keyMoment68 B hB
  · have he : k = (69 : Fin 2886) := Fin.ext h69
    subst k
    rw [keyMomentRowsAt69]
    exact keyMoment69 B hB
  · have he : k = (70 : Fin 2886) := Fin.ext h70
    subst k
    rw [keyMomentRowsAt70]
    exact keyMoment70 B hB
  · have he : k = (71 : Fin 2886) := Fin.ext h71
    subst k
    rw [keyMomentRowsAt71]
    exact keyMoment71 B hB
  · have he : k = (72 : Fin 2886) := Fin.ext h72
    subst k
    rw [keyMomentRowsAt72]
    exact keyMoment72 B hB
  · have he : k = (73 : Fin 2886) := Fin.ext h73
    subst k
    rw [keyMomentRowsAt73]
    exact keyMoment73 B hB
  · have he : k = (74 : Fin 2886) := Fin.ext h74
    subst k
    rw [keyMomentRowsAt74]
    exact keyMoment74 B hB
  · have he : k = (75 : Fin 2886) := Fin.ext h75
    subst k
    rw [keyMomentRowsAt75]
    exact keyMoment75 B hB
  · have he : k = (76 : Fin 2886) := Fin.ext h76
    subst k
    rw [keyMomentRowsAt76]
    exact keyMoment76 B hB
  · have he : k = (77 : Fin 2886) := Fin.ext h77
    subst k
    rw [keyMomentRowsAt77]
    exact keyMoment77 B hB
  · have he : k = (78 : Fin 2886) := Fin.ext h78
    subst k
    rw [keyMomentRowsAt78]
    exact keyMoment78 B hB
  · have he : k = (79 : Fin 2886) := Fin.ext h79
    subst k
    rw [keyMomentRowsAt79]
    exact keyMoment79 B hB
  · have he : k = (80 : Fin 2886) := Fin.ext h80
    subst k
    rw [keyMomentRowsAt80]
    exact keyMoment80 B hB
  · have he : k = (81 : Fin 2886) := Fin.ext h81
    subst k
    rw [keyMomentRowsAt81]
    exact keyMoment81 B hB
  · have he : k = (82 : Fin 2886) := Fin.ext h82
    subst k
    rw [keyMomentRowsAt82]
    exact keyMoment82 B hB
  · have he : k = (83 : Fin 2886) := Fin.ext h83
    subst k
    rw [keyMomentRowsAt83]
    exact keyMoment83 B hB
  · have he : k = (84 : Fin 2886) := Fin.ext h84
    subst k
    rw [keyMomentRowsAt84]
    exact keyMoment84 B hB
  · have he : k = (85 : Fin 2886) := Fin.ext h85
    subst k
    rw [keyMomentRowsAt85]
    exact keyMoment85 B hB
  · have he : k = (86 : Fin 2886) := Fin.ext h86
    subst k
    rw [keyMomentRowsAt86]
    exact keyMoment86 B hB
  · have he : k = (87 : Fin 2886) := Fin.ext h87
    subst k
    rw [keyMomentRowsAt87]
    exact keyMoment87 B hB
  · have he : k = (88 : Fin 2886) := Fin.ext h88
    subst k
    rw [keyMomentRowsAt88]
    exact keyMoment88 B hB
  · have he : k = (89 : Fin 2886) := Fin.ext h89
    subst k
    rw [keyMomentRowsAt89]
    exact keyMoment89 B hB
  · have he : k = (90 : Fin 2886) := Fin.ext h90
    subst k
    rw [keyMomentRowsAt90]
    exact keyMoment90 B hB
  · have he : k = (91 : Fin 2886) := Fin.ext h91
    subst k
    rw [keyMomentRowsAt91]
    exact keyMoment91 B hB
  · have he : k = (92 : Fin 2886) := Fin.ext h92
    subst k
    rw [keyMomentRowsAt92]
    exact keyMoment92 B hB
  · have he : k = (93 : Fin 2886) := Fin.ext h93
    subst k
    rw [keyMomentRowsAt93]
    exact keyMoment93 B hB
  · have he : k = (94 : Fin 2886) := Fin.ext h94
    subst k
    rw [keyMomentRowsAt94]
    exact keyMoment94 B hB
  · have he : k = (95 : Fin 2886) := Fin.ext h95
    subst k
    rw [keyMomentRowsAt95]
    exact keyMoment95 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1984 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1984) =
      Integer.Sparse.eval keyMomentRow1984 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1984).leftCharge (GramAssembly.key 1984).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1125) := by
    have ha : gramCharges (GramAssembly.key 1984).leftCharge (GramAssembly.key 1984).rightCharge = raw41397 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41397Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41397 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1984).leftCharge (GramAssembly.key 1984).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1984, Integer.Sparse.eval]

theorem keyMoment1985 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1985) =
      Integer.Sparse.eval keyMomentRow1985 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1985).leftCharge (GramAssembly.key 1985).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 597) := by
    have ha : gramCharges (GramAssembly.key 1985).leftCharge (GramAssembly.key 1985).rightCharge = raw41398 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41398Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41398 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1985).leftCharge (GramAssembly.key 1985).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1985, Integer.Sparse.eval]

theorem keyMoment1986 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1986) =
      Integer.Sparse.eval keyMomentRow1986 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1986).leftCharge (GramAssembly.key 1986).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 577) := by
    have ha : gramCharges (GramAssembly.key 1986).leftCharge (GramAssembly.key 1986).rightCharge = raw41399 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41399Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41399 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1986).leftCharge (GramAssembly.key 1986).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1986, Integer.Sparse.eval]

theorem keyMoment1987 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1987) =
      Integer.Sparse.eval keyMomentRow1987 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1987).leftCharge (GramAssembly.key 1987).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2132) := by
    have ha : gramCharges (GramAssembly.key 1987).leftCharge (GramAssembly.key 1987).rightCharge = raw41400 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41400Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41400 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1987).leftCharge (GramAssembly.key 1987).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1987, Integer.Sparse.eval]

theorem keyMoment1988 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1988) =
      Integer.Sparse.eval keyMomentRow1988 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1988).leftCharge (GramAssembly.key 1988).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1822) := by
    have ha : gramCharges (GramAssembly.key 1988).leftCharge (GramAssembly.key 1988).rightCharge = raw41401 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41401Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41401 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1988).leftCharge (GramAssembly.key 1988).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1988, Integer.Sparse.eval]

theorem keyMoment1989 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1989) =
      Integer.Sparse.eval keyMomentRow1989 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1989).leftCharge (GramAssembly.key 1989).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2088) := by
    have ha : gramCharges (GramAssembly.key 1989).leftCharge (GramAssembly.key 1989).rightCharge = raw41402 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41402Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41402 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1989).leftCharge (GramAssembly.key 1989).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1989, Integer.Sparse.eval]

theorem keyMoment1990 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1990) =
      Integer.Sparse.eval keyMomentRow1990 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1990).leftCharge (GramAssembly.key 1990).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1803) := by
    have ha : gramCharges (GramAssembly.key 1990).leftCharge (GramAssembly.key 1990).rightCharge = raw41403 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41403Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41403 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1990).leftCharge (GramAssembly.key 1990).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1990, Integer.Sparse.eval]

theorem keyMoment1991 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1991) =
      Integer.Sparse.eval keyMomentRow1991 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1991).leftCharge (GramAssembly.key 1991).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 601) := by
    have ha : gramCharges (GramAssembly.key 1991).leftCharge (GramAssembly.key 1991).rightCharge = raw41404 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41404Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41404 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1991).leftCharge (GramAssembly.key 1991).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1991, Integer.Sparse.eval]

theorem keyMoment1992 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1992) =
      Integer.Sparse.eval keyMomentRow1992 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1992).leftCharge (GramAssembly.key 1992).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 578) := by
    have ha : gramCharges (GramAssembly.key 1992).leftCharge (GramAssembly.key 1992).rightCharge = raw41405 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41405Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41405 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1992).leftCharge (GramAssembly.key 1992).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1992, Integer.Sparse.eval]

theorem keyMoment1993 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1993) =
      Integer.Sparse.eval keyMomentRow1993 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1993).leftCharge (GramAssembly.key 1993).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1823) := by
    have ha : gramCharges (GramAssembly.key 1993).leftCharge (GramAssembly.key 1993).rightCharge = raw41406 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41406Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41406 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1993).leftCharge (GramAssembly.key 1993).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1993, Integer.Sparse.eval]

theorem keyMoment1994 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1994) =
      Integer.Sparse.eval keyMomentRow1994 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1994).leftCharge (GramAssembly.key 1994).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1789) := by
    have ha : gramCharges (GramAssembly.key 1994).leftCharge (GramAssembly.key 1994).rightCharge = raw41407 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41407Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41407 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1994).leftCharge (GramAssembly.key 1994).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1994, Integer.Sparse.eval]

theorem keyMoment1995 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1995) =
      Integer.Sparse.eval keyMomentRow1995 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1995).leftCharge (GramAssembly.key 1995).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2529) := by
    have ha : gramCharges (GramAssembly.key 1995).leftCharge (GramAssembly.key 1995).rightCharge = raw41408 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41408Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41408 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1995).leftCharge (GramAssembly.key 1995).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1995, Integer.Sparse.eval]

theorem keyMoment1996 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1996) =
      Integer.Sparse.eval keyMomentRow1996 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1996).leftCharge (GramAssembly.key 1996).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2524) := by
    have ha : gramCharges (GramAssembly.key 1996).leftCharge (GramAssembly.key 1996).rightCharge = raw41409 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41409Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41409 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1996).leftCharge (GramAssembly.key 1996).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1996, Integer.Sparse.eval]

theorem keyMoment1997 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1997) =
      Integer.Sparse.eval keyMomentRow1997 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1997).leftCharge (GramAssembly.key 1997).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1111) := by
    have ha : gramCharges (GramAssembly.key 1997).leftCharge (GramAssembly.key 1997).rightCharge = raw41410 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41410Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41410 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1997).leftCharge (GramAssembly.key 1997).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1997, Integer.Sparse.eval]

theorem keyMoment1998 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1998) =
      Integer.Sparse.eval keyMomentRow1998 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1998).leftCharge (GramAssembly.key 1998).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 579) := by
    have ha : gramCharges (GramAssembly.key 1998).leftCharge (GramAssembly.key 1998).rightCharge = raw41411 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41411Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41411 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1998).leftCharge (GramAssembly.key 1998).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1998, Integer.Sparse.eval]

theorem keyMoment1999 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1999) =
      Integer.Sparse.eval keyMomentRow1999 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1999).leftCharge (GramAssembly.key 1999).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2105) := by
    have ha : gramCharges (GramAssembly.key 1999).leftCharge (GramAssembly.key 1999).rightCharge = raw41412 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41412Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41412 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1999).leftCharge (GramAssembly.key 1999).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1999, Integer.Sparse.eval]

theorem keyMoment2000 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2000) =
      Integer.Sparse.eval keyMomentRow2000 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2000).leftCharge (GramAssembly.key 2000).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1802) := by
    have ha : gramCharges (GramAssembly.key 2000).leftCharge (GramAssembly.key 2000).rightCharge = raw41413 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41413Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41413 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2000).leftCharge (GramAssembly.key 2000).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2000, Integer.Sparse.eval]

theorem keyMoment2001 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2001) =
      Integer.Sparse.eval keyMomentRow2001 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2001).leftCharge (GramAssembly.key 2001).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2051) := by
    have ha : gramCharges (GramAssembly.key 2001).leftCharge (GramAssembly.key 2001).rightCharge = raw41414 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41414Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41414 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2001).leftCharge (GramAssembly.key 2001).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2001, Integer.Sparse.eval]

theorem keyMoment2002 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2002) =
      Integer.Sparse.eval keyMomentRow2002 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2002).leftCharge (GramAssembly.key 2002).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2243) := by
    have ha : gramCharges (GramAssembly.key 2002).leftCharge (GramAssembly.key 2002).rightCharge = raw41415 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41415Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41415 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2002).leftCharge (GramAssembly.key 2002).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2002, Integer.Sparse.eval]

theorem keyMoment2003 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2003) =
      Integer.Sparse.eval keyMomentRow2003 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2003).leftCharge (GramAssembly.key 2003).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2019) := by
    have ha : gramCharges (GramAssembly.key 2003).leftCharge (GramAssembly.key 2003).rightCharge = raw41416 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41416Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41416 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2003).leftCharge (GramAssembly.key 2003).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2003, Integer.Sparse.eval]

theorem keyMoment2004 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2004) =
      Integer.Sparse.eval keyMomentRow2004 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2004).leftCharge (GramAssembly.key 2004).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3812) := by
    have ha : gramCharges (GramAssembly.key 2004).leftCharge (GramAssembly.key 2004).rightCharge = raw41417 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41417Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41417 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2004).leftCharge (GramAssembly.key 2004).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2004, Integer.Sparse.eval]

theorem keyMoment2005 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2005) =
      Integer.Sparse.eval keyMomentRow2005 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2005).leftCharge (GramAssembly.key 2005).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3786) := by
    have ha : gramCharges (GramAssembly.key 2005).leftCharge (GramAssembly.key 2005).rightCharge = raw41418 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41418Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41418 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2005).leftCharge (GramAssembly.key 2005).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2005, Integer.Sparse.eval]

theorem keyMoment2006 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2006) =
      Integer.Sparse.eval keyMomentRow2006 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2006).leftCharge (GramAssembly.key 2006).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1966) := by
    have ha : gramCharges (GramAssembly.key 2006).leftCharge (GramAssembly.key 2006).rightCharge = raw41419 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41419Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41419 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2006).leftCharge (GramAssembly.key 2006).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2006, Integer.Sparse.eval]

theorem keyMoment2007 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2007) =
      Integer.Sparse.eval keyMomentRow2007 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2007).leftCharge (GramAssembly.key 2007).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3493) := by
    have ha : gramCharges (GramAssembly.key 2007).leftCharge (GramAssembly.key 2007).rightCharge = raw41420 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41420Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41420 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2007).leftCharge (GramAssembly.key 2007).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2007, Integer.Sparse.eval]

theorem keyMoment2008 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2008) =
      Integer.Sparse.eval keyMomentRow2008 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2008).leftCharge (GramAssembly.key 2008).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3805) := by
    have ha : gramCharges (GramAssembly.key 2008).leftCharge (GramAssembly.key 2008).rightCharge = raw41421 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41421Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41421 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2008).leftCharge (GramAssembly.key 2008).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2008, Integer.Sparse.eval]

theorem keyMoment2009 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2009) =
      Integer.Sparse.eval keyMomentRow2009 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2009).leftCharge (GramAssembly.key 2009).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2807) := by
    have ha : gramCharges (GramAssembly.key 2009).leftCharge (GramAssembly.key 2009).rightCharge = raw41422 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41422Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41422 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2009).leftCharge (GramAssembly.key 2009).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2009, Integer.Sparse.eval]

theorem keyMoment2010 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2010) =
      Integer.Sparse.eval keyMomentRow2010 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2010).leftCharge (GramAssembly.key 2010).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3703) := by
    have ha : gramCharges (GramAssembly.key 2010).leftCharge (GramAssembly.key 2010).rightCharge = raw41423 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41423Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41423 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2010).leftCharge (GramAssembly.key 2010).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2010, Integer.Sparse.eval]

theorem keyMoment2011 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2011) =
      Integer.Sparse.eval keyMomentRow2011 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2011).leftCharge (GramAssembly.key 2011).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3689) := by
    have ha : gramCharges (GramAssembly.key 2011).leftCharge (GramAssembly.key 2011).rightCharge = raw41424 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41424Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41424 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2011).leftCharge (GramAssembly.key 2011).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2011, Integer.Sparse.eval]

theorem keyMoment2012 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2012) =
      Integer.Sparse.eval keyMomentRow2012 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2012).leftCharge (GramAssembly.key 2012).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1964) := by
    have ha : gramCharges (GramAssembly.key 2012).leftCharge (GramAssembly.key 2012).rightCharge = raw41425 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41425Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41425 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2012).leftCharge (GramAssembly.key 2012).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2012, Integer.Sparse.eval]

theorem keyMoment2013 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2013) =
      Integer.Sparse.eval keyMomentRow2013 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2013).leftCharge (GramAssembly.key 2013).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3496) := by
    have ha : gramCharges (GramAssembly.key 2013).leftCharge (GramAssembly.key 2013).rightCharge = raw41426 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41426Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41426 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2013).leftCharge (GramAssembly.key 2013).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2013, Integer.Sparse.eval]

theorem keyMoment2014 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2014) =
      Integer.Sparse.eval keyMomentRow2014 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2014).leftCharge (GramAssembly.key 2014).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1126) := by
    have ha : gramCharges (GramAssembly.key 2014).leftCharge (GramAssembly.key 2014).rightCharge = raw41427 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41427Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41427 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2014).leftCharge (GramAssembly.key 2014).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2014, Integer.Sparse.eval]

theorem keyMoment2015 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2015) =
      Integer.Sparse.eval keyMomentRow2015 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2015).leftCharge (GramAssembly.key 2015).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2508) := by
    have ha : gramCharges (GramAssembly.key 2015).leftCharge (GramAssembly.key 2015).rightCharge = raw41428 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41428Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41428 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2015).leftCharge (GramAssembly.key 2015).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2015, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1984 : keyMomentRows (1984 : Fin 2886) =
    keyMomentRow1984 := by decide +kernel

theorem keyMomentRowsAt1985 : keyMomentRows (1985 : Fin 2886) =
    keyMomentRow1985 := by decide +kernel

theorem keyMomentRowsAt1986 : keyMomentRows (1986 : Fin 2886) =
    keyMomentRow1986 := by decide +kernel

theorem keyMomentRowsAt1987 : keyMomentRows (1987 : Fin 2886) =
    keyMomentRow1987 := by decide +kernel

theorem keyMomentRowsAt1988 : keyMomentRows (1988 : Fin 2886) =
    keyMomentRow1988 := by decide +kernel

theorem keyMomentRowsAt1989 : keyMomentRows (1989 : Fin 2886) =
    keyMomentRow1989 := by decide +kernel

theorem keyMomentRowsAt1990 : keyMomentRows (1990 : Fin 2886) =
    keyMomentRow1990 := by decide +kernel

theorem keyMomentRowsAt1991 : keyMomentRows (1991 : Fin 2886) =
    keyMomentRow1991 := by decide +kernel

theorem keyMomentRowsAt1992 : keyMomentRows (1992 : Fin 2886) =
    keyMomentRow1992 := by decide +kernel

theorem keyMomentRowsAt1993 : keyMomentRows (1993 : Fin 2886) =
    keyMomentRow1993 := by decide +kernel

theorem keyMomentRowsAt1994 : keyMomentRows (1994 : Fin 2886) =
    keyMomentRow1994 := by decide +kernel

theorem keyMomentRowsAt1995 : keyMomentRows (1995 : Fin 2886) =
    keyMomentRow1995 := by decide +kernel

theorem keyMomentRowsAt1996 : keyMomentRows (1996 : Fin 2886) =
    keyMomentRow1996 := by decide +kernel

theorem keyMomentRowsAt1997 : keyMomentRows (1997 : Fin 2886) =
    keyMomentRow1997 := by decide +kernel

theorem keyMomentRowsAt1998 : keyMomentRows (1998 : Fin 2886) =
    keyMomentRow1998 := by decide +kernel

theorem keyMomentRowsAt1999 : keyMomentRows (1999 : Fin 2886) =
    keyMomentRow1999 := by decide +kernel

theorem keyMomentRowsAt2000 : keyMomentRows (2000 : Fin 2886) =
    keyMomentRow2000 := by decide +kernel

theorem keyMomentRowsAt2001 : keyMomentRows (2001 : Fin 2886) =
    keyMomentRow2001 := by decide +kernel

theorem keyMomentRowsAt2002 : keyMomentRows (2002 : Fin 2886) =
    keyMomentRow2002 := by decide +kernel

theorem keyMomentRowsAt2003 : keyMomentRows (2003 : Fin 2886) =
    keyMomentRow2003 := by decide +kernel

theorem keyMomentRowsAt2004 : keyMomentRows (2004 : Fin 2886) =
    keyMomentRow2004 := by decide +kernel

theorem keyMomentRowsAt2005 : keyMomentRows (2005 : Fin 2886) =
    keyMomentRow2005 := by decide +kernel

theorem keyMomentRowsAt2006 : keyMomentRows (2006 : Fin 2886) =
    keyMomentRow2006 := by decide +kernel

theorem keyMomentRowsAt2007 : keyMomentRows (2007 : Fin 2886) =
    keyMomentRow2007 := by decide +kernel

theorem keyMomentRowsAt2008 : keyMomentRows (2008 : Fin 2886) =
    keyMomentRow2008 := by decide +kernel

theorem keyMomentRowsAt2009 : keyMomentRows (2009 : Fin 2886) =
    keyMomentRow2009 := by decide +kernel

theorem keyMomentRowsAt2010 : keyMomentRows (2010 : Fin 2886) =
    keyMomentRow2010 := by decide +kernel

theorem keyMomentRowsAt2011 : keyMomentRows (2011 : Fin 2886) =
    keyMomentRow2011 := by decide +kernel

theorem keyMomentRowsAt2012 : keyMomentRows (2012 : Fin 2886) =
    keyMomentRow2012 := by decide +kernel

theorem keyMomentRowsAt2013 : keyMomentRows (2013 : Fin 2886) =
    keyMomentRow2013 := by decide +kernel

theorem keyMomentRowsAt2014 : keyMomentRows (2014 : Fin 2886) =
    keyMomentRow2014 := by decide +kernel

theorem keyMomentRowsAt2015 : keyMomentRows (2015 : Fin 2886) =
    keyMomentRow2015 := by decide +kernel

theorem keyMomentChunkSound62 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 62) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1984 ∨ k.val = 1985 ∨ k.val = 1986 ∨ k.val = 1987 ∨ k.val = 1988 ∨ k.val = 1989 ∨ k.val = 1990 ∨ k.val = 1991 ∨ k.val = 1992 ∨ k.val = 1993 ∨ k.val = 1994 ∨ k.val = 1995 ∨ k.val = 1996 ∨ k.val = 1997 ∨ k.val = 1998 ∨ k.val = 1999 ∨ k.val = 2000 ∨ k.val = 2001 ∨ k.val = 2002 ∨ k.val = 2003 ∨ k.val = 2004 ∨ k.val = 2005 ∨ k.val = 2006 ∨ k.val = 2007 ∨ k.val = 2008 ∨ k.val = 2009 ∨ k.val = 2010 ∨ k.val = 2011 ∨ k.val = 2012 ∨ k.val = 2013 ∨ k.val = 2014 ∨ k.val = 2015 := by omega
  rcases heq with h1984 | h1985 | h1986 | h1987 | h1988 | h1989 | h1990 | h1991 | h1992 | h1993 | h1994 | h1995 | h1996 | h1997 | h1998 | h1999 | h2000 | h2001 | h2002 | h2003 | h2004 | h2005 | h2006 | h2007 | h2008 | h2009 | h2010 | h2011 | h2012 | h2013 | h2014 | h2015
  · have he : k = (1984 : Fin 2886) := Fin.ext h1984
    subst k
    rw [keyMomentRowsAt1984]
    exact keyMoment1984 B hB
  · have he : k = (1985 : Fin 2886) := Fin.ext h1985
    subst k
    rw [keyMomentRowsAt1985]
    exact keyMoment1985 B hB
  · have he : k = (1986 : Fin 2886) := Fin.ext h1986
    subst k
    rw [keyMomentRowsAt1986]
    exact keyMoment1986 B hB
  · have he : k = (1987 : Fin 2886) := Fin.ext h1987
    subst k
    rw [keyMomentRowsAt1987]
    exact keyMoment1987 B hB
  · have he : k = (1988 : Fin 2886) := Fin.ext h1988
    subst k
    rw [keyMomentRowsAt1988]
    exact keyMoment1988 B hB
  · have he : k = (1989 : Fin 2886) := Fin.ext h1989
    subst k
    rw [keyMomentRowsAt1989]
    exact keyMoment1989 B hB
  · have he : k = (1990 : Fin 2886) := Fin.ext h1990
    subst k
    rw [keyMomentRowsAt1990]
    exact keyMoment1990 B hB
  · have he : k = (1991 : Fin 2886) := Fin.ext h1991
    subst k
    rw [keyMomentRowsAt1991]
    exact keyMoment1991 B hB
  · have he : k = (1992 : Fin 2886) := Fin.ext h1992
    subst k
    rw [keyMomentRowsAt1992]
    exact keyMoment1992 B hB
  · have he : k = (1993 : Fin 2886) := Fin.ext h1993
    subst k
    rw [keyMomentRowsAt1993]
    exact keyMoment1993 B hB
  · have he : k = (1994 : Fin 2886) := Fin.ext h1994
    subst k
    rw [keyMomentRowsAt1994]
    exact keyMoment1994 B hB
  · have he : k = (1995 : Fin 2886) := Fin.ext h1995
    subst k
    rw [keyMomentRowsAt1995]
    exact keyMoment1995 B hB
  · have he : k = (1996 : Fin 2886) := Fin.ext h1996
    subst k
    rw [keyMomentRowsAt1996]
    exact keyMoment1996 B hB
  · have he : k = (1997 : Fin 2886) := Fin.ext h1997
    subst k
    rw [keyMomentRowsAt1997]
    exact keyMoment1997 B hB
  · have he : k = (1998 : Fin 2886) := Fin.ext h1998
    subst k
    rw [keyMomentRowsAt1998]
    exact keyMoment1998 B hB
  · have he : k = (1999 : Fin 2886) := Fin.ext h1999
    subst k
    rw [keyMomentRowsAt1999]
    exact keyMoment1999 B hB
  · have he : k = (2000 : Fin 2886) := Fin.ext h2000
    subst k
    rw [keyMomentRowsAt2000]
    exact keyMoment2000 B hB
  · have he : k = (2001 : Fin 2886) := Fin.ext h2001
    subst k
    rw [keyMomentRowsAt2001]
    exact keyMoment2001 B hB
  · have he : k = (2002 : Fin 2886) := Fin.ext h2002
    subst k
    rw [keyMomentRowsAt2002]
    exact keyMoment2002 B hB
  · have he : k = (2003 : Fin 2886) := Fin.ext h2003
    subst k
    rw [keyMomentRowsAt2003]
    exact keyMoment2003 B hB
  · have he : k = (2004 : Fin 2886) := Fin.ext h2004
    subst k
    rw [keyMomentRowsAt2004]
    exact keyMoment2004 B hB
  · have he : k = (2005 : Fin 2886) := Fin.ext h2005
    subst k
    rw [keyMomentRowsAt2005]
    exact keyMoment2005 B hB
  · have he : k = (2006 : Fin 2886) := Fin.ext h2006
    subst k
    rw [keyMomentRowsAt2006]
    exact keyMoment2006 B hB
  · have he : k = (2007 : Fin 2886) := Fin.ext h2007
    subst k
    rw [keyMomentRowsAt2007]
    exact keyMoment2007 B hB
  · have he : k = (2008 : Fin 2886) := Fin.ext h2008
    subst k
    rw [keyMomentRowsAt2008]
    exact keyMoment2008 B hB
  · have he : k = (2009 : Fin 2886) := Fin.ext h2009
    subst k
    rw [keyMomentRowsAt2009]
    exact keyMoment2009 B hB
  · have he : k = (2010 : Fin 2886) := Fin.ext h2010
    subst k
    rw [keyMomentRowsAt2010]
    exact keyMoment2010 B hB
  · have he : k = (2011 : Fin 2886) := Fin.ext h2011
    subst k
    rw [keyMomentRowsAt2011]
    exact keyMoment2011 B hB
  · have he : k = (2012 : Fin 2886) := Fin.ext h2012
    subst k
    rw [keyMomentRowsAt2012]
    exact keyMoment2012 B hB
  · have he : k = (2013 : Fin 2886) := Fin.ext h2013
    subst k
    rw [keyMomentRowsAt2013]
    exact keyMoment2013 B hB
  · have he : k = (2014 : Fin 2886) := Fin.ext h2014
    subst k
    rw [keyMomentRowsAt2014]
    exact keyMoment2014 B hB
  · have he : k = (2015 : Fin 2886) := Fin.ext h2015
    subst k
    rw [keyMomentRowsAt2015]
    exact keyMoment2015 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 256) =
      Integer.Sparse.eval keyMomentRow256 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 256).leftCharge (GramAssembly.key 256).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 496) := by
    have ha : gramCharges (GramAssembly.key 256).leftCharge (GramAssembly.key 256).rightCharge = raw39706 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39706Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39706 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 256).leftCharge (GramAssembly.key 256).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow256, Integer.Sparse.eval]

theorem keyMoment257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 257) =
      Integer.Sparse.eval keyMomentRow257 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 257).leftCharge (GramAssembly.key 257).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 268) := by
    have ha : gramCharges (GramAssembly.key 257).leftCharge (GramAssembly.key 257).rightCharge = raw39707 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39707Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39707 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 257).leftCharge (GramAssembly.key 257).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow257, Integer.Sparse.eval]

theorem keyMoment258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 258) =
      Integer.Sparse.eval keyMomentRow258 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 258).leftCharge (GramAssembly.key 258).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 504) := by
    have ha : gramCharges (GramAssembly.key 258).leftCharge (GramAssembly.key 258).rightCharge = raw39708 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39708Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39708 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 258).leftCharge (GramAssembly.key 258).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow258, Integer.Sparse.eval]

theorem keyMoment259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 259) =
      Integer.Sparse.eval keyMomentRow259 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 259).leftCharge (GramAssembly.key 259).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 467) := by
    have ha : gramCharges (GramAssembly.key 259).leftCharge (GramAssembly.key 259).rightCharge = raw39709 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39709Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39709 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 259).leftCharge (GramAssembly.key 259).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow259, Integer.Sparse.eval]

theorem keyMoment260 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 260) =
      Integer.Sparse.eval keyMomentRow260 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 260).leftCharge (GramAssembly.key 260).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 272) := by
    have ha : gramCharges (GramAssembly.key 260).leftCharge (GramAssembly.key 260).rightCharge = raw39710 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39710Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39710 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 260).leftCharge (GramAssembly.key 260).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow260, Integer.Sparse.eval]

theorem keyMoment261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 261) =
      Integer.Sparse.eval keyMomentRow261 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 261).leftCharge (GramAssembly.key 261).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 469) := by
    have ha : gramCharges (GramAssembly.key 261).leftCharge (GramAssembly.key 261).rightCharge = raw39711 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39711Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39711 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 261).leftCharge (GramAssembly.key 261).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow261, Integer.Sparse.eval]

theorem keyMoment262 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 262) =
      Integer.Sparse.eval keyMomentRow262 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 262).leftCharge (GramAssembly.key 262).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 516) := by
    have ha : gramCharges (GramAssembly.key 262).leftCharge (GramAssembly.key 262).rightCharge = raw39712 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39712Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39712 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 262).leftCharge (GramAssembly.key 262).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow262, Integer.Sparse.eval]

theorem keyMoment263 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 263) =
      Integer.Sparse.eval keyMomentRow263 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 263).leftCharge (GramAssembly.key 263).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 410) := by
    have ha : gramCharges (GramAssembly.key 263).leftCharge (GramAssembly.key 263).rightCharge = raw39713 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39713Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39713 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 263).leftCharge (GramAssembly.key 263).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow263, Integer.Sparse.eval]

theorem keyMoment264 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 264) =
      Integer.Sparse.eval keyMomentRow264 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 264).leftCharge (GramAssembly.key 264).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 483) := by
    have ha : gramCharges (GramAssembly.key 264).leftCharge (GramAssembly.key 264).rightCharge = raw39714 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39714Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39714 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 264).leftCharge (GramAssembly.key 264).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow264, Integer.Sparse.eval]

theorem keyMoment265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 265) =
      Integer.Sparse.eval keyMomentRow265 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 265).leftCharge (GramAssembly.key 265).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 498) := by
    have ha : gramCharges (GramAssembly.key 265).leftCharge (GramAssembly.key 265).rightCharge = raw39715 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39715Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39715 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 265).leftCharge (GramAssembly.key 265).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow265, Integer.Sparse.eval]

theorem keyMoment266 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 266) =
      Integer.Sparse.eval keyMomentRow266 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 266).leftCharge (GramAssembly.key 266).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 491) := by
    have ha : gramCharges (GramAssembly.key 266).leftCharge (GramAssembly.key 266).rightCharge = raw39716 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39716Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39716 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 266).leftCharge (GramAssembly.key 266).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow266, Integer.Sparse.eval]

theorem keyMoment267 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 267) =
      Integer.Sparse.eval keyMomentRow267 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 267).leftCharge (GramAssembly.key 267).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 514) := by
    have ha : gramCharges (GramAssembly.key 267).leftCharge (GramAssembly.key 267).rightCharge = raw39717 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39717Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39717 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 267).leftCharge (GramAssembly.key 267).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow267, Integer.Sparse.eval]

theorem keyMoment268 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 268) =
      Integer.Sparse.eval keyMomentRow268 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 268).leftCharge (GramAssembly.key 268).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 515) := by
    have ha : gramCharges (GramAssembly.key 268).leftCharge (GramAssembly.key 268).rightCharge = raw39718 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39718Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39718 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 268).leftCharge (GramAssembly.key 268).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow268, Integer.Sparse.eval]

theorem keyMoment269 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 269) =
      Integer.Sparse.eval keyMomentRow269 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 269).leftCharge (GramAssembly.key 269).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 512) := by
    have ha : gramCharges (GramAssembly.key 269).leftCharge (GramAssembly.key 269).rightCharge = raw39719 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39719Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39719 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 269).leftCharge (GramAssembly.key 269).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow269, Integer.Sparse.eval]

theorem keyMoment270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 270) =
      Integer.Sparse.eval keyMomentRow270 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 270).leftCharge (GramAssembly.key 270).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 513) := by
    have ha : gramCharges (GramAssembly.key 270).leftCharge (GramAssembly.key 270).rightCharge = raw39720 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39720Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39720 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 270).leftCharge (GramAssembly.key 270).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow270, Integer.Sparse.eval]

theorem keyMoment271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 271) =
      Integer.Sparse.eval keyMomentRow271 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 271).leftCharge (GramAssembly.key 271).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 4) := by
    have ha : gramCharges (GramAssembly.key 271).leftCharge (GramAssembly.key 271).rightCharge = raw39721 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39721Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39721 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 271).leftCharge (GramAssembly.key 271).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow271, Integer.Sparse.eval]

theorem keyMoment272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 272) =
      Integer.Sparse.eval keyMomentRow272 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 272).leftCharge (GramAssembly.key 272).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 489) := by
    have ha : gramCharges (GramAssembly.key 272).leftCharge (GramAssembly.key 272).rightCharge = raw39722 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39722Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39722 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 272).leftCharge (GramAssembly.key 272).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow272, Integer.Sparse.eval]

theorem keyMoment273 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 273) =
      Integer.Sparse.eval keyMomentRow273 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 273).leftCharge (GramAssembly.key 273).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 268) := by
    have ha : gramCharges (GramAssembly.key 273).leftCharge (GramAssembly.key 273).rightCharge = raw39723 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39723Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39723 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 273).leftCharge (GramAssembly.key 273).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow273, Integer.Sparse.eval]

theorem keyMoment274 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 274) =
      Integer.Sparse.eval keyMomentRow274 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 274).leftCharge (GramAssembly.key 274).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 467) := by
    have ha : gramCharges (GramAssembly.key 274).leftCharge (GramAssembly.key 274).rightCharge = raw39724 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39724Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39724 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 274).leftCharge (GramAssembly.key 274).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow274, Integer.Sparse.eval]

theorem keyMoment275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 275) =
      Integer.Sparse.eval keyMomentRow275 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 275).leftCharge (GramAssembly.key 275).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 498) := by
    have ha : gramCharges (GramAssembly.key 275).leftCharge (GramAssembly.key 275).rightCharge = raw39725 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39725Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39725 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 275).leftCharge (GramAssembly.key 275).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow275, Integer.Sparse.eval]

theorem keyMoment276 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 276) =
      Integer.Sparse.eval keyMomentRow276 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 276).leftCharge (GramAssembly.key 276).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 381) := by
    have ha : gramCharges (GramAssembly.key 276).leftCharge (GramAssembly.key 276).rightCharge = raw39726 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39726Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39726 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 276).leftCharge (GramAssembly.key 276).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow276, Integer.Sparse.eval]

theorem keyMoment277 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 277) =
      Integer.Sparse.eval keyMomentRow277 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 277).leftCharge (GramAssembly.key 277).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 480) := by
    have ha : gramCharges (GramAssembly.key 277).leftCharge (GramAssembly.key 277).rightCharge = raw39727 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39727Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39727 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 277).leftCharge (GramAssembly.key 277).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow277, Integer.Sparse.eval]

theorem keyMoment278 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 278) =
      Integer.Sparse.eval keyMomentRow278 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 278).leftCharge (GramAssembly.key 278).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 444) := by
    have ha : gramCharges (GramAssembly.key 278).leftCharge (GramAssembly.key 278).rightCharge = raw39728 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39728Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39728 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 278).leftCharge (GramAssembly.key 278).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow278, Integer.Sparse.eval]

theorem keyMoment279 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 279) =
      Integer.Sparse.eval keyMomentRow279 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 279).leftCharge (GramAssembly.key 279).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 443) := by
    have ha : gramCharges (GramAssembly.key 279).leftCharge (GramAssembly.key 279).rightCharge = raw39729 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39729Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39729 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 279).leftCharge (GramAssembly.key 279).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow279, Integer.Sparse.eval]

theorem keyMoment280 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 280) =
      Integer.Sparse.eval keyMomentRow280 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 280).leftCharge (GramAssembly.key 280).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 485) := by
    have ha : gramCharges (GramAssembly.key 280).leftCharge (GramAssembly.key 280).rightCharge = raw39730 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39730Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39730 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 280).leftCharge (GramAssembly.key 280).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow280, Integer.Sparse.eval]

theorem keyMoment281 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 281) =
      Integer.Sparse.eval keyMomentRow281 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 281).leftCharge (GramAssembly.key 281).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 499) := by
    have ha : gramCharges (GramAssembly.key 281).leftCharge (GramAssembly.key 281).rightCharge = raw39731 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39731Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39731 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 281).leftCharge (GramAssembly.key 281).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow281, Integer.Sparse.eval]

theorem keyMoment282 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 282) =
      Integer.Sparse.eval keyMomentRow282 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 282).leftCharge (GramAssembly.key 282).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 521) := by
    have ha : gramCharges (GramAssembly.key 282).leftCharge (GramAssembly.key 282).rightCharge = raw39732 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39732Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39732 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 282).leftCharge (GramAssembly.key 282).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow282, Integer.Sparse.eval]

theorem keyMoment283 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 283) =
      Integer.Sparse.eval keyMomentRow283 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 283).leftCharge (GramAssembly.key 283).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 479) := by
    have ha : gramCharges (GramAssembly.key 283).leftCharge (GramAssembly.key 283).rightCharge = raw39733 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39733Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39733 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 283).leftCharge (GramAssembly.key 283).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow283, Integer.Sparse.eval]

theorem keyMoment284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 284) =
      Integer.Sparse.eval keyMomentRow284 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 284).leftCharge (GramAssembly.key 284).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 409) := by
    have ha : gramCharges (GramAssembly.key 284).leftCharge (GramAssembly.key 284).rightCharge = raw39734 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39734Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39734 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 284).leftCharge (GramAssembly.key 284).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow284, Integer.Sparse.eval]

theorem keyMoment285 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 285) =
      Integer.Sparse.eval keyMomentRow285 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 285).leftCharge (GramAssembly.key 285).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 387) := by
    have ha : gramCharges (GramAssembly.key 285).leftCharge (GramAssembly.key 285).rightCharge = raw39735 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39735Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39735 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 285).leftCharge (GramAssembly.key 285).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow285, Integer.Sparse.eval]

theorem keyMoment286 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 286) =
      Integer.Sparse.eval keyMomentRow286 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 286).leftCharge (GramAssembly.key 286).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 150) := by
    have ha : gramCharges (GramAssembly.key 286).leftCharge (GramAssembly.key 286).rightCharge = raw39736 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39736Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39736 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 286).leftCharge (GramAssembly.key 286).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow286, Integer.Sparse.eval]

theorem keyMoment287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 287) =
      Integer.Sparse.eval keyMomentRow287 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 287).leftCharge (GramAssembly.key 287).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 145) := by
    have ha : gramCharges (GramAssembly.key 287).leftCharge (GramAssembly.key 287).rightCharge = raw39737 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39737Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39737 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 287).leftCharge (GramAssembly.key 287).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow287, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt256 : keyMomentRows (256 : Fin 2886) =
    keyMomentRow256 := by decide +kernel

theorem keyMomentRowsAt257 : keyMomentRows (257 : Fin 2886) =
    keyMomentRow257 := by decide +kernel

theorem keyMomentRowsAt258 : keyMomentRows (258 : Fin 2886) =
    keyMomentRow258 := by decide +kernel

theorem keyMomentRowsAt259 : keyMomentRows (259 : Fin 2886) =
    keyMomentRow259 := by decide +kernel

theorem keyMomentRowsAt260 : keyMomentRows (260 : Fin 2886) =
    keyMomentRow260 := by decide +kernel

theorem keyMomentRowsAt261 : keyMomentRows (261 : Fin 2886) =
    keyMomentRow261 := by decide +kernel

theorem keyMomentRowsAt262 : keyMomentRows (262 : Fin 2886) =
    keyMomentRow262 := by decide +kernel

theorem keyMomentRowsAt263 : keyMomentRows (263 : Fin 2886) =
    keyMomentRow263 := by decide +kernel

theorem keyMomentRowsAt264 : keyMomentRows (264 : Fin 2886) =
    keyMomentRow264 := by decide +kernel

theorem keyMomentRowsAt265 : keyMomentRows (265 : Fin 2886) =
    keyMomentRow265 := by decide +kernel

theorem keyMomentRowsAt266 : keyMomentRows (266 : Fin 2886) =
    keyMomentRow266 := by decide +kernel

theorem keyMomentRowsAt267 : keyMomentRows (267 : Fin 2886) =
    keyMomentRow267 := by decide +kernel

theorem keyMomentRowsAt268 : keyMomentRows (268 : Fin 2886) =
    keyMomentRow268 := by decide +kernel

theorem keyMomentRowsAt269 : keyMomentRows (269 : Fin 2886) =
    keyMomentRow269 := by decide +kernel

theorem keyMomentRowsAt270 : keyMomentRows (270 : Fin 2886) =
    keyMomentRow270 := by decide +kernel

theorem keyMomentRowsAt271 : keyMomentRows (271 : Fin 2886) =
    keyMomentRow271 := by decide +kernel

theorem keyMomentRowsAt272 : keyMomentRows (272 : Fin 2886) =
    keyMomentRow272 := by decide +kernel

theorem keyMomentRowsAt273 : keyMomentRows (273 : Fin 2886) =
    keyMomentRow273 := by decide +kernel

theorem keyMomentRowsAt274 : keyMomentRows (274 : Fin 2886) =
    keyMomentRow274 := by decide +kernel

theorem keyMomentRowsAt275 : keyMomentRows (275 : Fin 2886) =
    keyMomentRow275 := by decide +kernel

theorem keyMomentRowsAt276 : keyMomentRows (276 : Fin 2886) =
    keyMomentRow276 := by decide +kernel

theorem keyMomentRowsAt277 : keyMomentRows (277 : Fin 2886) =
    keyMomentRow277 := by decide +kernel

theorem keyMomentRowsAt278 : keyMomentRows (278 : Fin 2886) =
    keyMomentRow278 := by decide +kernel

theorem keyMomentRowsAt279 : keyMomentRows (279 : Fin 2886) =
    keyMomentRow279 := by decide +kernel

theorem keyMomentRowsAt280 : keyMomentRows (280 : Fin 2886) =
    keyMomentRow280 := by decide +kernel

theorem keyMomentRowsAt281 : keyMomentRows (281 : Fin 2886) =
    keyMomentRow281 := by decide +kernel

theorem keyMomentRowsAt282 : keyMomentRows (282 : Fin 2886) =
    keyMomentRow282 := by decide +kernel

theorem keyMomentRowsAt283 : keyMomentRows (283 : Fin 2886) =
    keyMomentRow283 := by decide +kernel

theorem keyMomentRowsAt284 : keyMomentRows (284 : Fin 2886) =
    keyMomentRow284 := by decide +kernel

theorem keyMomentRowsAt285 : keyMomentRows (285 : Fin 2886) =
    keyMomentRow285 := by decide +kernel

theorem keyMomentRowsAt286 : keyMomentRows (286 : Fin 2886) =
    keyMomentRow286 := by decide +kernel

theorem keyMomentRowsAt287 : keyMomentRows (287 : Fin 2886) =
    keyMomentRow287 := by decide +kernel

theorem keyMomentChunkSound8 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 8) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 256 ∨ k.val = 257 ∨ k.val = 258 ∨ k.val = 259 ∨ k.val = 260 ∨ k.val = 261 ∨ k.val = 262 ∨ k.val = 263 ∨ k.val = 264 ∨ k.val = 265 ∨ k.val = 266 ∨ k.val = 267 ∨ k.val = 268 ∨ k.val = 269 ∨ k.val = 270 ∨ k.val = 271 ∨ k.val = 272 ∨ k.val = 273 ∨ k.val = 274 ∨ k.val = 275 ∨ k.val = 276 ∨ k.val = 277 ∨ k.val = 278 ∨ k.val = 279 ∨ k.val = 280 ∨ k.val = 281 ∨ k.val = 282 ∨ k.val = 283 ∨ k.val = 284 ∨ k.val = 285 ∨ k.val = 286 ∨ k.val = 287 := by omega
  rcases heq with h256 | h257 | h258 | h259 | h260 | h261 | h262 | h263 | h264 | h265 | h266 | h267 | h268 | h269 | h270 | h271 | h272 | h273 | h274 | h275 | h276 | h277 | h278 | h279 | h280 | h281 | h282 | h283 | h284 | h285 | h286 | h287
  · have he : k = (256 : Fin 2886) := Fin.ext h256
    subst k
    rw [keyMomentRowsAt256]
    exact keyMoment256 B hB
  · have he : k = (257 : Fin 2886) := Fin.ext h257
    subst k
    rw [keyMomentRowsAt257]
    exact keyMoment257 B hB
  · have he : k = (258 : Fin 2886) := Fin.ext h258
    subst k
    rw [keyMomentRowsAt258]
    exact keyMoment258 B hB
  · have he : k = (259 : Fin 2886) := Fin.ext h259
    subst k
    rw [keyMomentRowsAt259]
    exact keyMoment259 B hB
  · have he : k = (260 : Fin 2886) := Fin.ext h260
    subst k
    rw [keyMomentRowsAt260]
    exact keyMoment260 B hB
  · have he : k = (261 : Fin 2886) := Fin.ext h261
    subst k
    rw [keyMomentRowsAt261]
    exact keyMoment261 B hB
  · have he : k = (262 : Fin 2886) := Fin.ext h262
    subst k
    rw [keyMomentRowsAt262]
    exact keyMoment262 B hB
  · have he : k = (263 : Fin 2886) := Fin.ext h263
    subst k
    rw [keyMomentRowsAt263]
    exact keyMoment263 B hB
  · have he : k = (264 : Fin 2886) := Fin.ext h264
    subst k
    rw [keyMomentRowsAt264]
    exact keyMoment264 B hB
  · have he : k = (265 : Fin 2886) := Fin.ext h265
    subst k
    rw [keyMomentRowsAt265]
    exact keyMoment265 B hB
  · have he : k = (266 : Fin 2886) := Fin.ext h266
    subst k
    rw [keyMomentRowsAt266]
    exact keyMoment266 B hB
  · have he : k = (267 : Fin 2886) := Fin.ext h267
    subst k
    rw [keyMomentRowsAt267]
    exact keyMoment267 B hB
  · have he : k = (268 : Fin 2886) := Fin.ext h268
    subst k
    rw [keyMomentRowsAt268]
    exact keyMoment268 B hB
  · have he : k = (269 : Fin 2886) := Fin.ext h269
    subst k
    rw [keyMomentRowsAt269]
    exact keyMoment269 B hB
  · have he : k = (270 : Fin 2886) := Fin.ext h270
    subst k
    rw [keyMomentRowsAt270]
    exact keyMoment270 B hB
  · have he : k = (271 : Fin 2886) := Fin.ext h271
    subst k
    rw [keyMomentRowsAt271]
    exact keyMoment271 B hB
  · have he : k = (272 : Fin 2886) := Fin.ext h272
    subst k
    rw [keyMomentRowsAt272]
    exact keyMoment272 B hB
  · have he : k = (273 : Fin 2886) := Fin.ext h273
    subst k
    rw [keyMomentRowsAt273]
    exact keyMoment273 B hB
  · have he : k = (274 : Fin 2886) := Fin.ext h274
    subst k
    rw [keyMomentRowsAt274]
    exact keyMoment274 B hB
  · have he : k = (275 : Fin 2886) := Fin.ext h275
    subst k
    rw [keyMomentRowsAt275]
    exact keyMoment275 B hB
  · have he : k = (276 : Fin 2886) := Fin.ext h276
    subst k
    rw [keyMomentRowsAt276]
    exact keyMoment276 B hB
  · have he : k = (277 : Fin 2886) := Fin.ext h277
    subst k
    rw [keyMomentRowsAt277]
    exact keyMoment277 B hB
  · have he : k = (278 : Fin 2886) := Fin.ext h278
    subst k
    rw [keyMomentRowsAt278]
    exact keyMoment278 B hB
  · have he : k = (279 : Fin 2886) := Fin.ext h279
    subst k
    rw [keyMomentRowsAt279]
    exact keyMoment279 B hB
  · have he : k = (280 : Fin 2886) := Fin.ext h280
    subst k
    rw [keyMomentRowsAt280]
    exact keyMoment280 B hB
  · have he : k = (281 : Fin 2886) := Fin.ext h281
    subst k
    rw [keyMomentRowsAt281]
    exact keyMoment281 B hB
  · have he : k = (282 : Fin 2886) := Fin.ext h282
    subst k
    rw [keyMomentRowsAt282]
    exact keyMoment282 B hB
  · have he : k = (283 : Fin 2886) := Fin.ext h283
    subst k
    rw [keyMomentRowsAt283]
    exact keyMoment283 B hB
  · have he : k = (284 : Fin 2886) := Fin.ext h284
    subst k
    rw [keyMomentRowsAt284]
    exact keyMoment284 B hB
  · have he : k = (285 : Fin 2886) := Fin.ext h285
    subst k
    rw [keyMomentRowsAt285]
    exact keyMoment285 B hB
  · have he : k = (286 : Fin 2886) := Fin.ext h286
    subst k
    rw [keyMomentRowsAt286]
    exact keyMoment286 B hB
  · have he : k = (287 : Fin 2886) := Fin.ext h287
    subst k
    rw [keyMomentRowsAt287]
    exact keyMoment287 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2880 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2880) =
      Integer.Sparse.eval keyMomentRow2880 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2880).leftCharge (GramAssembly.key 2880).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3255) := by
    have ha : gramCharges (GramAssembly.key 2880).leftCharge (GramAssembly.key 2880).rightCharge = raw43072 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43072Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43072 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2880).leftCharge (GramAssembly.key 2880).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4527) := by
    have ha : gramCharges (GramAssembly.key 2880).leftCharge (GramAssembly.key 2880).rightCharge = raw43073 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43073Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43073 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2880).leftCharge (GramAssembly.key 2880).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2880).leftCharge (GramAssembly.key 2880).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2880, Integer.Sparse.eval] <;> ring

theorem keyMoment2881 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2881) =
      Integer.Sparse.eval keyMomentRow2881 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2881).leftCharge (GramAssembly.key 2881).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1505) := by
    have ha : gramCharges (GramAssembly.key 2881).leftCharge (GramAssembly.key 2881).rightCharge = raw43074 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43074Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43074 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2881).leftCharge (GramAssembly.key 2881).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4151) := by
    have ha : gramCharges (GramAssembly.key 2881).leftCharge (GramAssembly.key 2881).rightCharge = raw43075 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43075Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43075 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2881).leftCharge (GramAssembly.key 2881).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2881).leftCharge (GramAssembly.key 2881).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2881, Integer.Sparse.eval] <;> ring

theorem keyMoment2882 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2882) =
      Integer.Sparse.eval keyMomentRow2882 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2882).leftCharge (GramAssembly.key 2882).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2148) := by
    have ha : gramCharges (GramAssembly.key 2882).leftCharge (GramAssembly.key 2882).rightCharge = raw43076 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43076Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43076 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2882).leftCharge (GramAssembly.key 2882).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4666) := by
    have ha : gramCharges (GramAssembly.key 2882).leftCharge (GramAssembly.key 2882).rightCharge = raw43077 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43077Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43077 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2882).leftCharge (GramAssembly.key 2882).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2882).leftCharge (GramAssembly.key 2882).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2882, Integer.Sparse.eval] <;> ring

theorem keyMoment2883 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2883) =
      Integer.Sparse.eval keyMomentRow2883 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2883).leftCharge (GramAssembly.key 2883).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3511) := by
    have ha : gramCharges (GramAssembly.key 2883).leftCharge (GramAssembly.key 2883).rightCharge = raw43078 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43078Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43078 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2883).leftCharge (GramAssembly.key 2883).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4958) := by
    have ha : gramCharges (GramAssembly.key 2883).leftCharge (GramAssembly.key 2883).rightCharge = raw43079 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43079Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43079 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2883).leftCharge (GramAssembly.key 2883).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2883).leftCharge (GramAssembly.key 2883).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2883, Integer.Sparse.eval] <;> ring

theorem keyMoment2884 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2884) =
      Integer.Sparse.eval keyMomentRow2884 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2884).leftCharge (GramAssembly.key 2884).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3261) := by
    have ha : gramCharges (GramAssembly.key 2884).leftCharge (GramAssembly.key 2884).rightCharge = raw43080 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43080Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43080 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2884).leftCharge (GramAssembly.key 2884).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4530) := by
    have ha : gramCharges (GramAssembly.key 2884).leftCharge (GramAssembly.key 2884).rightCharge = raw43081 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43081Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43081 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2884).leftCharge (GramAssembly.key 2884).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2884).leftCharge (GramAssembly.key 2884).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2884, Integer.Sparse.eval] <;> ring

theorem keyMoment2885 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2885) =
      Integer.Sparse.eval keyMomentRow2885 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2885).leftCharge (GramAssembly.key 2885).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1515) := by
    have ha : gramCharges (GramAssembly.key 2885).leftCharge (GramAssembly.key 2885).rightCharge = raw43082 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43082Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43082 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2885).leftCharge (GramAssembly.key 2885).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4155) := by
    have ha : gramCharges (GramAssembly.key 2885).leftCharge (GramAssembly.key 2885).rightCharge = raw43083 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43083Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43083 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2885).leftCharge (GramAssembly.key 2885).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2885).leftCharge (GramAssembly.key 2885).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2885, Integer.Sparse.eval] <;> ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2880 : keyMomentRows (2880 : Fin 2886) =
    keyMomentRow2880 := by decide +kernel

theorem keyMomentRowsAt2881 : keyMomentRows (2881 : Fin 2886) =
    keyMomentRow2881 := by decide +kernel

theorem keyMomentRowsAt2882 : keyMomentRows (2882 : Fin 2886) =
    keyMomentRow2882 := by decide +kernel

theorem keyMomentRowsAt2883 : keyMomentRows (2883 : Fin 2886) =
    keyMomentRow2883 := by decide +kernel

theorem keyMomentRowsAt2884 : keyMomentRows (2884 : Fin 2886) =
    keyMomentRow2884 := by decide +kernel

theorem keyMomentRowsAt2885 : keyMomentRows (2885 : Fin 2886) =
    keyMomentRow2885 := by decide +kernel

theorem keyMomentChunkSound90 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 90) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2880 ∨ k.val = 2881 ∨ k.val = 2882 ∨ k.val = 2883 ∨ k.val = 2884 ∨ k.val = 2885 := by omega
  rcases heq with h2880 | h2881 | h2882 | h2883 | h2884 | h2885
  · have he : k = (2880 : Fin 2886) := Fin.ext h2880
    subst k
    rw [keyMomentRowsAt2880]
    exact keyMoment2880 B hB
  · have he : k = (2881 : Fin 2886) := Fin.ext h2881
    subst k
    rw [keyMomentRowsAt2881]
    exact keyMoment2881 B hB
  · have he : k = (2882 : Fin 2886) := Fin.ext h2882
    subst k
    rw [keyMomentRowsAt2882]
    exact keyMoment2882 B hB
  · have he : k = (2883 : Fin 2886) := Fin.ext h2883
    subst k
    rw [keyMomentRowsAt2883]
    exact keyMoment2883 B hB
  · have he : k = (2884 : Fin 2886) := Fin.ext h2884
    subst k
    rw [keyMomentRowsAt2884]
    exact keyMoment2884 B hB
  · have he : k = (2885 : Fin 2886) := Fin.ext h2885
    subst k
    rw [keyMomentRowsAt2885]
    exact keyMoment2885 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem allKeyMomentChunks (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (c : Fin 91) (k : Fin 2886) (hk : k.val / 32 = c.val) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  fin_cases c
  · exact keyMomentChunkSound0_e B hB k hk
  · exact keyMomentChunkSound1_e B hB k hk
  · exact keyMomentChunkSound2 B hB k hk
  · exact keyMomentChunkSound3_e B hB k hk
  · exact keyMomentChunkSound4_e B hB k hk
  · exact keyMomentChunkSound5_e B hB k hk
  · exact keyMomentChunkSound6_e B hB k hk
  · exact keyMomentChunkSound7_e B hB k hk
  · exact keyMomentChunkSound8 B hB k hk
  · exact keyMomentChunkSound9_e B hB k hk
  · exact keyMomentChunkSound10_e B hB k hk
  · exact keyMomentChunkSound11_e B hB k hk
  · exact keyMomentChunkSound12 B hB k hk
  · exact keyMomentChunkSound13_e B hB k hk
  · exact keyMomentChunkSound14_e B hB k hk
  · exact keyMomentChunkSound15_e B hB k hk
  · exact keyMomentChunkSound16_e B hB k hk
  · exact keyMomentChunkSound17_e B hB k hk
  · exact keyMomentChunkSound18_e B hB k hk
  · exact keyMomentChunkSound19_e B hB k hk
  · exact keyMomentChunkSound20_e B hB k hk
  · exact keyMomentChunkSound21_e B hB k hk
  · exact keyMomentChunkSound22_e B hB k hk
  · exact keyMomentChunkSound23_e B hB k hk
  · exact keyMomentChunkSound24_e B hB k hk
  · exact keyMomentChunkSound25_e B hB k hk
  · exact keyMomentChunkSound26_e B hB k hk
  · exact keyMomentChunkSound27_e B hB k hk
  · exact keyMomentChunkSound28_e B hB k hk
  · exact keyMomentChunkSound29_e B hB k hk
  · exact keyMomentChunkSound30_e B hB k hk
  · exact keyMomentChunkSound31_e B hB k hk
  · exact keyMomentChunkSound32_e B hB k hk
  · exact keyMomentChunkSound33_e B hB k hk
  · exact keyMomentChunkSound34_e B hB k hk
  · exact keyMomentChunkSound35_e B hB k hk
  · exact keyMomentChunkSound36_e B hB k hk
  · exact keyMomentChunkSound37_e B hB k hk
  · exact keyMomentChunkSound38_e B hB k hk
  · exact keyMomentChunkSound39_e B hB k hk
  · exact keyMomentChunkSound40_e B hB k hk
  · exact keyMomentChunkSound41_e B hB k hk
  · exact keyMomentChunkSound42_e B hB k hk
  · exact keyMomentChunkSound43_e B hB k hk
  · exact keyMomentChunkSound44_e B hB k hk
  · exact keyMomentChunkSound45_e B hB k hk
  · exact keyMomentChunkSound46_e B hB k hk
  · exact keyMomentChunkSound47_e B hB k hk
  · exact keyMomentChunkSound48_e B hB k hk
  · exact keyMomentChunkSound49_e B hB k hk
  · exact keyMomentChunkSound50_e B hB k hk
  · exact keyMomentChunkSound51_e B hB k hk
  · exact keyMomentChunkSound52_e B hB k hk
  · exact keyMomentChunkSound53_e B hB k hk
  · exact keyMomentChunkSound54_e B hB k hk
  · exact keyMomentChunkSound55_e B hB k hk
  · exact keyMomentChunkSound56_e B hB k hk
  · exact keyMomentChunkSound57_e B hB k hk
  · exact keyMomentChunkSound58_e B hB k hk
  · exact keyMomentChunkSound59_e B hB k hk
  · exact keyMomentChunkSound60_e B hB k hk
  · exact keyMomentChunkSound61_e B hB k hk
  · exact keyMomentChunkSound62 B hB k hk
  · exact keyMomentChunkSound63_e B hB k hk
  · exact keyMomentChunkSound64_e B hB k hk
  · exact keyMomentChunkSound65_e B hB k hk
  · exact keyMomentChunkSound66_e B hB k hk
  · exact keyMomentChunkSound67_e B hB k hk
  · exact keyMomentChunkSound68_e B hB k hk
  · exact keyMomentChunkSound69_e B hB k hk
  · exact keyMomentChunkSound70_e B hB k hk
  · exact keyMomentChunkSound71_e B hB k hk
  · exact keyMomentChunkSound72_e B hB k hk
  · exact keyMomentChunkSound73_e B hB k hk
  · exact keyMomentChunkSound74_e B hB k hk
  · exact keyMomentChunkSound75_e B hB k hk
  · exact keyMomentChunkSound76_e B hB k hk
  · exact keyMomentChunkSound77_e B hB k hk
  · exact keyMomentChunkSound78_e B hB k hk
  · exact keyMomentChunkSound79_e B hB k hk
  · exact keyMomentChunkSound80_e B hB k hk
  · exact keyMomentChunkSound81_e B hB k hk
  · exact keyMomentChunkSound82_e B hB k hk
  · exact keyMomentChunkSound83_e B hB k hk
  · exact keyMomentChunkSound84_e B hB k hk
  · exact keyMomentChunkSound85_e B hB k hk
  · exact keyMomentChunkSound86_e B hB k hk
  · exact keyMomentChunkSound87_e B hB k hk
  · exact keyMomentChunkSound88_e B hB k hk
  · exact keyMomentChunkSound89_e B hB k hk
  · exact keyMomentChunkSound90 B hB k hk

theorem allKeyMoments_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B) (k : Fin 2886) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  exact allKeyMomentChunks B hB ⟨k.val / 32, by omega⟩ k rfl

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.allKeyMoments_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.allKeyMoments_e_oai
