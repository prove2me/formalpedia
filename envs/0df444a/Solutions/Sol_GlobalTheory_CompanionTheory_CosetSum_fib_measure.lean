-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CosetSum.fib_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:12.844022+00:00
-- url     : https://prove2.me/submissions/ec1e061b-e749-4d05-83a8-df1351fbf1eb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetIntegralUnramified
import Theorems.Thm_GlobalTheory_CompanionTheory_CosetSum_fib_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CosetSum
variable {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
namespace GlobalTheory.CompanionTheory.CosetSum
theorem _root_.solution (ν : Measure G) [ν.IsAddLeftInvariant] (H : AddSubgroup G)
    (h1 : ν (H : Set G) = 1) (c : G ⧸ H) : ν (fib H c) = 1 := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hpre : fib H (g : G ⧸ H) = (fun x => -g + x) ⁻¹' (H : Set G) := by
    rw [fib_mk]
    ext x
    simp [neg_add_eq_sub]
  rw [hpre, measure_preimage_add, h1]
end GlobalTheory.CompanionTheory.CosetSum
