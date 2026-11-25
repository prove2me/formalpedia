-- Prove2me | solution 1 for GlobalTheory.HL.HermJacobian.isHerm_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:48:48.403836+00:00
-- url     : https://prove2.me/submissions/092a2415-01c8-451c-ac95-00efa72450e5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobian
import Theorems.Thm_GlobalTheory_HL_HermJacobian_coord_apply
import Theorems.Thm_GlobalTheory_HL_HermJacobian_isHerm_iff
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical Kronecker
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.HermJacobian
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.HermJacobian
theorem _root_.solution (L : LocE F E) {m : ℕ} {ω e : E} (h : (ω - L.cj ω) * e = 1)
    (v : Fin m × Fin m → F) : IsHerm L (coord m ω (L.cj ω) e h fun k => algebraMap F E (v k)) := by
  refine (isHerm_iff L _).2 fun i j => ?_
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [coord_apply, hij, hij.not_gt, L.cj_cj]
  · simp [coord_apply]
  · simp [coord_apply, hij, hij.not_gt]
end GlobalTheory.HL.HermJacobian
