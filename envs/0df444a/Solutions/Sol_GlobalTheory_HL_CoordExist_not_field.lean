-- Prove2me | solution 1 for GlobalTheory.HL.CoordExist.not_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:06:35.309798+00:00
-- url     : https://prove2.me/submissions/ac6bd328-71df-4d66-9460-c4738898d15e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField
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
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordExist
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
namespace GlobalTheory.HL.CoordExist
theorem _root_.solution (L : LocE F E) (g : SplitG L) : ¬ IsField E := by
  intro hE
  have hx : g.e.symm (1, 0) ≠ 0 := by
    intro h0
    have h1 := congrArg g.e h0
    simp at h1
  obtain ⟨x', hx'⟩ := hE.mul_inv_cancel hx
  have hxy : g.e.symm (1, 0) * g.e.symm (0, 1) = 0 := by
    rw [← map_mul]
    simp
  have hy : g.e.symm (0, 1) = 0 := by
    calc g.e.symm (0, 1) = (x' * g.e.symm (1, 0)) * g.e.symm (0, 1) := by
          rw [mul_comm x', hx', one_mul]
      _ = 0 := by rw [mul_assoc, hxy, mul_zero]
  have h1 := congrArg g.e hy
  simp at h1
end GlobalTheory.HL.CoordExist
