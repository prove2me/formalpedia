-- Prove2me | solution 1 for GlobalTheory.HL.Inhab.extZ_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:00:18.448463+00:00
-- url     : https://prove2.me/submissions/668cd1dd-c592-4a3d-86a3-095eef06d294

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
import Theorems.Thm_GlobalTheory_HL_Inhab_mem_stdLat
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
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {s m N : ℕ} (e : Fin s ⊕ Fin m ≃ Fin N)
namespace GlobalTheory.HL.Inhab
theorem _root_.solution (L : LocE F E) (x : Fin s → E) (hx : ∀ i, x i ∈ L.O) : extZ e x ∈ stdLat L N := by
  rw [mem_stdLat]
  intro i
  simp only [extZ, Function.comp_apply]
  rcases e.symm i with a | a
  · exact hx a
  · exact zero_mem _
end GlobalTheory.HL.Inhab
