-- Prove2me | solution 1 for OAI.BufferedIsing.constrainedSum_delete_variables
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:33:11.425958+00:00
-- url     : https://prove2.me/submissions/e4b27cf1-8543-46ab-9977-a74b236ca412

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/SpinCorrelation.lean:L46-L66
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.constrainedSum_delete_variables. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation

-- ---- from OAI.Probability.Ising.SpinCorrelation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma constrainedSum_delete_variables {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ : Spins n) (P : Spins n → Prop) :
    constrainedSum G h (fun σ => AgreesOn F σ τ ∧ P σ) =
      ∑ σ : KeptVertex F → Bool,
        if P (pinExtension F τ σ) then weight G h (pinExtension F τ σ) else 0 := by
  classical
  calc
    _ = ∑ σ : Spins n, if AgreesOn F σ τ then
        (if P σ then weight G h σ else 0) else 0 := by
      unfold constrainedSum
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hF : AgreesOn F σ τ <;> by_cases hP : P σ <;> simp [hF, hP]
    _ = ∑ σ ∈ Finset.univ.filter (fun σ : Spins n => AgreesOn F σ τ),
        if P σ then weight G h σ else 0 := (Finset.sum_filter _ _).symm
    _ = ∑ σ : {σ : Spins n // AgreesOn F σ τ},
        if P σ.val then weight G h σ.val else 0 :=
      Finset.sum_subtype _ (by intro σ; simp only [Finset.mem_filter,
        Finset.mem_univ, true_and]) _
    _ = _ := (Equiv.sum_comp (pinExtensionEquiv F τ)
      (fun σ => if P σ.val then weight G h σ.val else 0)).symm

end BufferedIsing

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem solution {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ : Spins n) (P : Spins n → Prop) :
    constrainedSum G h (fun σ => AgreesOn F σ τ ∧ P σ) =
      ∑ σ : KeptVertex F → Bool,
        if P (pinExtension F τ σ) then weight G h (pinExtension F τ σ) else 0 := by
  first
    | exact OAI.BufferedIsing.constrainedSum_delete_variables G h F τ P
    | exact OAI.BufferedIsing.constrainedSum_delete_variables
    | (apply OAI.BufferedIsing.constrainedSum_delete_variables <;> assumption)
    | (intros; apply OAI.BufferedIsing.constrainedSum_delete_variables <;> assumption)
