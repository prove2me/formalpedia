-- Prove2me | solution 1 for GlobalTheory.HL.LatCard.relIndex_map_of_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:39:56.6597+00:00
-- url     : https://prove2.me/submissions/31b6c08e-0ad3-44d1-a6b2-680826a2e2f4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizer
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LatCard
namespace GlobalTheory.HL.LatCard
theorem _root_.solution {G W : Type*} [AddCommGroup G] [AddCommGroup W] (f : G →+ W)
    (hf : Function.Injective f) (A : AddSubgroup W) (hA : ∀ w, w ∈ A ↔ ∃ g, f g = w)
    (T : W →+ W) (t : G → G) (ht : ∀ g, f (t g) = T (f g)) (H : AddSubgroup G)
    (hH : ∀ g, g ∈ H ↔ ∃ g', t g' = g) : (A.map T).relIndex A = H.index := by
  have hA' : A = (⊤ : AddSubgroup G).map f := by
    ext w
    simp [hA]
  have hT : A.map T = H.map f := by
    ext w
    simp [hA, hH, ht]
  rw [hT, hA', AddSubgroup.relIndex_map_map_of_injective _ _ hf, AddSubgroup.relIndex_top_right]
end GlobalTheory.HL.LatCard
