-- Prove2me | solution 1 for GlobalTheory.GlueLineBundle.gm_glue_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:11:04.618116+00:00
-- url     : https://prove2.me/submissions/635b7f2f-31b5-49d3-a4a4-6a4987fbf9cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueLineBundles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} (V : A → X.Opens) (M : ∀ a, LB (V a).toScheme)
namespace GlobalTheory.GlueLineBundle
theorem _root_.solution (a : A) {Y : Scheme.{0}} (f : Y ⟶ (V a).toScheme) (y : Y) (i k : (M a).ι)
    (hi : f y ∈ (M a).U i) (hk : f y ∈ (M a).U k) :
    gm (f ≫ (V a).ι) y _ ((glue V M).g ⟨a, i⟩ ⟨a, k⟩) = gm f y ((M a).U i ⊓ (M a).U k) ((M a).g i k) :=
  Classical.choose_spec (exists_gSpec V M ⟨a, i⟩ ⟨a, k⟩) a Y f y i k rfl rfl hi hk
end GlobalTheory.GlueLineBundle
