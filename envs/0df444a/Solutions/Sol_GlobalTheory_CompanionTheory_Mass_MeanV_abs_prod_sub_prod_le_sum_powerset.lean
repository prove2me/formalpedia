-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.abs_prod_sub_prod_le_sum_powerset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:51:11.338788+00:00
-- url     : https://prove2.me/submissions/920fda56-6b8a-46f6-a998-8782797111d5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProductDifferenceBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV
namespace GlobalTheory.CompanionTheory.Mass.MeanV
theorem _root_.solution (V : Type) (a : V → ℝ) (A U : Finset V) (hAU : A ⊆ U) :
    |∏ v ∈ U, a v - ∏ v ∈ A, a v| ≤ ∑ D ∈ U.powerset with ¬ D ⊆ A, ∏ v ∈ D, |a v - 1| := by
  have hexp : ∀ S : Finset V, ∏ v ∈ S, a v = ∑ D ∈ S.powerset, ∏ v ∈ D, (a v - 1) := by
    intro S
    rw [← Finset.prod_one_add]
    exact Finset.prod_congr rfl fun v _ => by ring
  have hfilt : U.powerset.filter (fun D => D ⊆ A) = A.powerset := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hAU, h⟩⟩
  rw [hexp U, hexp A, ← Finset.sum_filter_add_sum_filter_not U.powerset (fun D => D ⊆ A), hfilt,
    add_sub_cancel_left]
  calc |∑ D ∈ U.powerset with ¬ D ⊆ A, ∏ v ∈ D, (a v - 1)|
      ≤ ∑ D ∈ U.powerset with ¬ D ⊆ A, |∏ v ∈ D, (a v - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ D ∈ U.powerset with ¬ D ⊆ A, ∏ v ∈ D, |a v - 1| := by simp_rw [Finset.abs_prod]
end GlobalTheory.CompanionTheory.Mass.MeanV
