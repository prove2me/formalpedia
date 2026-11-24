-- Prove2me | solution 1 for GlobalTheory.CoverGlue.of_isPullback_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:01:31.022462+00:00
-- url     : https://prove2.me/submissions/e0c4a595-f4f6-4476-a090-28701e2f3c66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsAbelianSchemeAndRelDimOfOpenCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoverGlue
namespace GlobalTheory.CoverGlue
theorem _root_.solution (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {S X : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {Z : I → Scheme.{0}} {p : X ⟶ S}
    {q : ∀ i, Z i ⟶ (U i).toScheme} {ψ : ∀ i, Z i ⟶ X} (h : ∀ i, IsPullback (ψ i) (q i) p (U i).ι)
    (hq : ∀ i, Q (q i)) : Q p := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i => ?_
  have hr := (isPullback_morphismRestrict p (U i)).flip
  rw [← IsPullback.isoIsPullback_hom_snd _ _ hr (h i)]
  exact (MorphismProperty.cancel_left_of_respectsIso Q _ _).2 (hq i)
end GlobalTheory.CoverGlue
