-- Prove2me | solution 1 for GlobalTheory.T.relIndex_tupleLattice_hermitianLattice_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:41:46.357105+00:00
-- url     : https://prove2.me/submissions/dffa3e59-8b29-4219-bc73-37427e5397f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizer
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizerStatement
import Theorems.Thm_GlobalTheory_HL_LatCard_relIndex_tupLat_hermLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ m j : ℕ, ((tupLat L Λs m).map (DistribMulAction.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ j)))).relIndex (tupLat L Λs m) = resQ ϖ ^ (2 * n * m * j) ∧ ((hermLat L m).map (DistribMulAction.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ j)))).relIndex (hermLat L m) = resQ ϖ ^ (m ^ 2 * j) := by
  first | exact @GlobalTheory.HL.LatCard.relIndex_tupLat_hermLat | exact GlobalTheory.HL.LatCard.relIndex_tupLat_hermLat | (intros; apply GlobalTheory.HL.LatCard.relIndex_tupLat_hermLat <;> assumption)
end _root_.GlobalTheory.T
