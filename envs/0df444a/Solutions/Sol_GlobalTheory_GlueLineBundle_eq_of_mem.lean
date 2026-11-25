-- Prove2me | solution 1 for GlobalTheory.GlueLineBundle.eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:38:14.811866+00:00
-- url     : https://prove2.me/submissions/c80f80d9-6a3f-4c92-8d4a-1740f4f98a83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueLineBundles
import Theorems.Thm_GlobalTheory_GlueLineBundle_mem_of_mem_NU

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
variable {V M}
namespace GlobalTheory.GlueLineBundle
theorem _root_.solution (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) {a b : A} (w : (V a).toScheme) {k : (M b).ι}
    (h : (V a).ι w ∈ NU V M ⟨b, k⟩) : a = b :=
  hdisj a b _ w.2 (mem_of_mem_NU V M h)
end GlobalTheory.GlueLineBundle
