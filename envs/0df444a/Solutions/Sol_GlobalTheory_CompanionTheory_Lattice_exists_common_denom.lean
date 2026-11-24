-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Lattice.exists_common_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:30.885797+00:00
-- url     : https://prove2.me/submissions/2c582cec-d4d9-4c60-bad2-fbbf16e10677

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SandwichStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Lattice
open CompanionTheory.Rg.FlB
open scoped NormedField Valued
namespace GlobalTheory.CompanionTheory.Lattice
theorem _root_.solution {L ι : Type} [Field L] (O : Subring L)
    (hfrac : ∀ x : L, ∃ a : O, (a : L) ≠ 0 ∧ (a : L) * x ∈ O) (s : Finset ι) (g : ι → L) :
    ∃ d : O, (d : L) ≠ 0 ∧ ∀ i ∈ s, (d : L) * g i ∈ O := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert i s _ ih =>
    obtain ⟨d, hd, h⟩ := ih
    obtain ⟨a, ha, hi⟩ := hfrac (g i)
    refine ⟨a * d, by simp [ha, hd], fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · have : ((a * d : O) : L) * g j = (d : L) * ((a : L) * g j) := by push_cast; ring
      rw [this]
      exact O.mul_mem d.2 hi
    · have : ((a * d : O) : L) * g j = (a : L) * ((d : L) * g j) := by push_cast; ring
      rw [this]
      exact O.mul_mem a.2 (h j hj)
end GlobalTheory.CompanionTheory.Lattice
