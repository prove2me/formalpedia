-- Prove2me | solution 1 for GlobalTheory.NonGenericLocalCheck.lamStd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:54:24.593507+00:00
-- url     : https://prove2.me/submissions/ea7ea130-4781-4156-a6a4-bbe3efd98cd3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_TransversalityLocal_FramePairFixatorUnitaryAndFixesFrame
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
open GlobalTheory GlobalTheory.NonGenericLocalCheck
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}
variable (M) (m : ℕ)
namespace GlobalTheory.NonGenericLocalCheck
theorem _root_.solution (c : F) : (frame M m c).LamStd (inn M m c) =
    Submodule.span M.L.O {v | ∀ i, v i ∈ M.L.O} := by
  unfold FrameD.LamStd
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, IsEmpty.forall_iff, true_and]
  constructor
  · rintro ⟨w, hw, hwL⟩
    have hv : v = w.1 := by
      rw [hw]
      simp [FrameD.prF]
    rw [hv]
    exact (mem_inn M m c w).mp hwL
  · intro hv
    exact ⟨⟨v, mem_perp_zero _ _⟩, by simp [FrameD.prF], (mem_inn M m c _).mpr hv⟩
end GlobalTheory.NonGenericLocalCheck
