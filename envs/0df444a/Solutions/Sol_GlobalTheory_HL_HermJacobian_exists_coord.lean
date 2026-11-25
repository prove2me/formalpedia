-- Prove2me | solution 1 for GlobalTheory.HL.HermJacobian.exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:38:52.729474+00:00
-- url     : https://prove2.me/submissions/0cd1d00f-521b-4ae6-81ac-5ffec0039f47

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
import Theorems.Thm_GlobalTheory_HL_HermJacobian_coord_symm_apply
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
    (X : Matrix (Fin m) (Fin m) E) (hX : IsHerm L X) (k : Fin m × Fin m) :
    ∃ a : F, algebraMap F E a = (coord m ω (L.cj ω) e h).symm X k := by
  have he' : (L.cj ω - ω) * L.cj e = 1 := by simpa [L.cj_cj] using congrArg L.cj h
  have hce : L.cj e = -e := by linear_combination (-e) * he' - (L.cj e) * h
  rw [← L.cj_fix]
  obtain ⟨i, j⟩ := k
  have h1 := (isHerm_iff L X).1 hX i j
  have h2 := (isHerm_iff L X).1 hX j i
  rw [coord_symm_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp only [hij, if_true, map_sub, map_mul, hce, h1, h2]
    linear_combination (X i j - X j i) * h
  · simp [h1]
  · simp only [hij, hij.not_gt, if_true, if_false, map_sub, map_mul, hce, h1, h2]
    ring
end GlobalTheory.HL.HermJacobian
