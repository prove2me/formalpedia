-- Prove2me | solution 1 for GlobalTheory.Cartier.SecMaps.eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:55.26427+00:00
-- url     : https://prove2.me/submissions/050c75b2-0cd3-4f8f-ad33-900ccb6b632c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_ext_germ
import Theorems.Thm_GlobalTheory_Cartier_sec_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_mem_of_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.Cartier
namespace SecMaps
theorem _root_.solution {A B : LB X} (hA : A.IsLB) {w : LB.Iso A B} {a : A.Sec} {b b' : B.Sec}
    (h : SecMaps w a b) (h' : SecMaps w a b') : b = b' :=
  sec_ext fun p => ext_germ fun x hx => by
    obtain ⟨q, hq⟩ := LB.mem_of_cover hA x
    have hm : x ∈ B.U p ⊓ A.U q := ⟨hx, hq⟩
    have := congrArg (X.presheaf.germ (B.U p ⊓ A.U q) x hm).hom
      ((h (p, q)).trans (h' (p, q)).symm)
    rwa [germ_resG, germ_resG] at this
end SecMaps
end GlobalTheory.Cartier
