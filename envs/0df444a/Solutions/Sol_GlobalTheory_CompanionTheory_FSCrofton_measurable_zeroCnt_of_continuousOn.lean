-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt_of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:20:12.953445+00:00
-- url     : https://prove2.me/submissions/a7e60a91-b4bf-4f20-b08c-0ceb2ca843a6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCount
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_measurableSet_natCast_le_encard_zeroSetIn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
namespace GlobalTheory.CompanionTheory.FSCrofton
open TopologicalSpace
variable {X : Type} [TopologicalSpace X] {d : ℕ} {α : Type} [Fintype α]
private theorem measurable_of_natCast_le_lemma {β : Type} [MeasurableSpace β] (g : β → ℕ∞)
    (hg : ∀ N : ℕ, MeasurableSet {x | (N : ℕ∞) ≤ g x}) : Measurable g := by
  refine measurable_to_countable' fun x => ?_
  induction x using ENat.recTopCoe with
  | top =>
    have h : g ⁻¹' {⊤} = ⋂ N : ℕ, {x | (N : ℕ∞) ≤ g x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      generalize g y = t
      induction t using ENat.recTopCoe with
      | top => exact ⟨fun _ _ => le_top, fun _ => rfl⟩
      | coe m =>
        constructor
        · intro hy
          exact absurd hy (ENat.natCast_ne_top m)
        · intro hy
          exfalso
          have h1 := hy (m + 1)
          norm_cast at h1
          omega
    rw [h]
    exact MeasurableSet.iInter hg
  | coe n =>
    have h : g ⁻¹' {(n : ℕ∞)} = {x | (n : ℕ∞) ≤ g x} \ {x | ((n + 1 : ℕ) : ℕ∞) ≤ g x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
      generalize g y = t
      induction t using ENat.recTopCoe with
      | top => simp
      | coe m =>
        norm_cast
        constructor
        · intro h1
          omega
        · intro h1
          omega
    rw [h]
    exact (hg n).diff (hg (n + 1))
end GlobalTheory.CompanionTheory.FSCrofton
end

set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton
open TopologicalSpace
variable {X : Type} [TopologicalSpace X] {d : ℕ} {α : Type} [Fintype α]
namespace GlobalTheory.CompanionTheory.FSCrofton
theorem _root_.solution [T2Space X] [SecondCountableTopology X]
    [LocallyCompactSpace X] {A : Set X} (hA : IsSigmaCompact A) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) A) :
    Measurable (zeroCnt d A b : (Fin d → α → ℂ) → ℝ≥0∞) := by
  have hg : Measurable fun C : Fin d → α → ℂ => (zeroSetIn A b C).encard :=
    measurable_of_natCast_le_lemma _ fun N => measurableSet_natCast_le_encard_zeroSetIn hA hb N
  exact (Measurable.of_discrete (f := fun n : ℕ∞ => (n : ℝ≥0∞))).comp hg
end GlobalTheory.CompanionTheory.FSCrofton
