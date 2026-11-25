-- Prove2me | solution 1 for GlobalTheory.HL.HermJacobian.det_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:40:07.369773+00:00
-- url     : https://prove2.me/submissions/9c4a3f10-8d30-470e-a969-0d2d7e338ff9

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
variable {E : Type} [CommRing E] {m : ℕ}
namespace GlobalTheory.HL.HermJacobian
theorem _root_.solution {F : Type} [Field F] [Algebra F E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → F) →ₗ[F] (ι → F)) (g : (ι → E) →ₗ[E] (ι → E))
    (h : ∀ v, g (fun k => algebraMap F E (v k)) = fun k => algebraMap F E (f v k)) :
    algebraMap F E (LinearMap.det f) = LinearMap.det g := by
  rw [← LinearMap.det_toMatrix' f, ← LinearMap.det_toMatrix' g, RingHom.map_det]
  congr 1
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  have h2 : (fun k => algebraMap F E ((Pi.single j 1 : ι → F) k)) = Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  rw [h2] at this
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix'_apply]
  exact this.symm
end GlobalTheory.HL.HermJacobian
