-- Prove2me | solution 1 for OAI.BufferedIsing.extremeLogOdds_eq_actualCoupling
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:51:29.313282+00:00
-- url     : https://prove2.me/submissions/7f7fa372-57dd-42f1-bbec-2153d6af6c57

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Contraction.lean:L319-L344
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.extremeLogOdds_eq_actualCoupling. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction
import Theorems.Thm_OAI_BufferedIsing_comparison_empty_preserves_I
import Theorems.Thm_OAI_BufferedIsing_contractedInteraction_energy
import Theorems.Thm_OAI_BufferedIsing_energy_pinExtension
import Theorems.Thm_OAI_BufferedIsing_interactionGraph_coupling
import Theorems.Thm_OAI_BufferedIsing_pairTable_contractedPinned
import Theorems.Thm_OAI_BufferedIsing_pairTable_quotient

-- ---- from OAI.Probability.Ising.PinnedMarginal ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma extremeLogOdds_eq_effective {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) (τ : Spins n) :
    extremeLogOdds G h I J F τ =
      4 * tableCoupling (pairTable (contractedPinnedWeight G h I J F τ) i j) := by
  simp only [tableCoupling, pairTable_contractedPinned G h I J F hIF hJF i j hi hj]
  unfold extremeLogOdds
  change _ = 4 * ((Real.log (jointWeight G h I J F τ ⊤ ⊤) +
    Real.log (jointWeight G h I J F τ ⊥ ⊥) - Real.log (jointWeight G h I J F τ ⊤ ⊥) -
    Real.log (jointWeight G h I J F τ ⊥ ⊤)) / 4)
  ring

lemma weight_pinExtension {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ : Spins n) (σ : KeptVertex F → Bool) :
    weight G h (pinExtension F τ σ) = Real.exp (pinConstant G h F τ) *
      Real.exp (deletedEnergy G F σ + ∑ v : KeptVertex F, pinField G h F τ v * spin (σ v)) := by
  unfold weight
  rw [energy_pinExtension]
  rw [← Real.exp_add]
  congr 1
  ring

end BufferedIsing

end OAI

-- ---- from OAI.Probability.Ising.Contraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma pairTable_scale {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → Bool) → ℝ) (c : ℝ) (u v : V) (s t : Bool) :
    pairTable (fun σ => c * f σ) u v s t = c * pairTable f u v s t := by
  classical
  unfold pairTable
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

lemma tableCoupling_scale (w : Bool → Bool → ℝ) (hw : ∀ s t, 0 < w s t)
    (c : ℝ) (hc : 0 < c) : tableCoupling (fun s t => c * w s t) = tableCoupling w := by
  simp only [tableCoupling, Real.log_mul hc.ne' (hw _ _).ne']
  ring

lemma pairTable_pos_of_weight_pos {V : Type*} [Fintype V] [DecidableEq V]
    (W : (V → Bool) → ℝ) (hW : ∀ σ, 0 < W σ) (u v : V) (huv : u ≠ v)
    (s t : Bool) : 0 < pairTable W u v s t := by
  classical
  unfold pairTable
  apply Finset.sum_pos'
  · intro σ _
    split_ifs
    · exact (hW σ).le
    · exact le_rfl
  · refine ⟨fun x => if x = u then s else t, Finset.mem_univ _, ?_⟩
    simp only [ite_eq_right (Ne.symm huv), and_self, ite_true]
    exact hW _

lemma contractedPinned_quotient_weight {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ : Spins n)
    (c : ContractedVertex G I J F → Bool) :
    weight G h (pinExtension F τ (fun v => c (Quotient.mk _ v))) =
      Real.exp (pinConstant G h F τ) *
        interactionWeight (contractedInteraction G I J F)
          (quotientField (comparisonSetoid G I J F ∅) (pinField G h F τ)) c := by
  rw [weight_pinExtension]
  unfold interactionWeight
  rw [contractedInteraction_energy]

lemma contractedPinned_pairTable_quotient {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ : Spins n)
    (i j : KeptVertex F) (s t : Bool) :
    pairTable (contractedPinnedWeight G h I J F τ) i j s t =
      Real.exp (pinConstant G h F τ) *
        pairTable (interactionWeight (contractedInteraction G I J F)
          (quotientField (comparisonSetoid G I J F ∅) (pinField G h F τ)))
          (Quotient.mk _ i) (Quotient.mk _ j) s t := by
  unfold contractedPinnedWeight
  rw [pairTable_quotient]
  simp_rw [contractedPinned_quotient_weight]
  rw [pairTable_scale]

lemma contractedTerminal_ne {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) :
    Quotient.mk (comparisonSetoid G I J F ∅) i ≠ Quotient.mk _ j := by
  intro H
  exact Finset.disjoint_left.mp hIJ
    ((comparison_empty_preserves_I G I J F hIJ i j (Quotient.exact H)).mp hi) hj

/-- The extreme log odds equals four times the effective coupling after deletion and separate terminal contraction, with fields induced by the common pins. -/
lemma extremeLogOdds_eq_actualCoupling {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) (τ : Spins n) :
    extremeLogOdds G h I J F τ = 4 * tableCoupling (pairTable
      (weight (actualComparisonGraph G I J F) (actualComparisonField G h I J F τ))
      (actualTerminal G I J F i) (actualTerminal G I J F j)) := by
  classical
  rw [extremeLogOdds_eq_effective G h I J F hIF hJF i j hi hj τ]
  congr 1
  have H : pairTable (contractedPinnedWeight G h I J F τ) i j =
      fun s t => Real.exp (pinConstant G h F τ) * pairTable
        (interactionWeight (contractedInteraction G I J F)
          (quotientField (comparisonSetoid G I J F ∅) (pinField G h F τ)))
        (Quotient.mk _ i) (Quotient.mk _ j) s t := by
    funext s t
    exact contractedPinned_pairTable_quotient G h I J F τ i j s t
  have hp : ∀ s t, 0 < pairTable
      (interactionWeight (contractedInteraction G I J F)
        (quotientField (comparisonSetoid G I J F ∅) (pinField G h F τ)))
      (Quotient.mk _ i) (Quotient.mk _ j) s t :=
    pairTable_pos_of_weight_pos _ (fun σ => Real.exp_pos _)
      _ _ (contractedTerminal_ne G I J F hIJ i j hi hj)
  rw [H, tableCoupling_scale _ hp (Real.exp (pinConstant G h F τ)) (Real.exp_pos _)]
  exact (interactionGraph_coupling _ _ _ _ (contractedTerminal_ne G I J F hIJ i j hi hj)).symm

end BufferedIsing

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem solution {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) (τ : Spins n) :
    extremeLogOdds G h I J F τ = 4 * tableCoupling (pairTable
      (weight (actualComparisonGraph G I J F) (actualComparisonField G h I J F τ))
      (actualTerminal G I J F i) (actualTerminal G I J F j)) := by
  first
    | exact OAI.BufferedIsing.extremeLogOdds_eq_actualCoupling G h I J F hIJ hIF hJF i j hi hj τ
    | exact OAI.BufferedIsing.extremeLogOdds_eq_actualCoupling
    | (apply OAI.BufferedIsing.extremeLogOdds_eq_actualCoupling <;> assumption)
    | (intros; apply OAI.BufferedIsing.extremeLogOdds_eq_actualCoupling <;> assumption)
