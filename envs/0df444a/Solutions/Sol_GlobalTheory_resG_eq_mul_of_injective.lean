-- Prove2me | solution 1 for GlobalTheory.resG_eq_mul_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:55:25.924905+00:00
-- url     : https://prove2.me/submissions/5fa21e21-656f-4c03-b56c-0dd9328eb36a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_resG_resG
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y : Scheme.{0}}
namespace GlobalTheory
theorem _root_.solution {A B G T A' B' T' : X.Opens} (hA : T ≤ A) (hB : T ≤ B)
    (hG : T ≤ G) (hA' : A' ≤ A) (hB' : B' ≤ B) (hT : T' ≤ T) (kA : T' ≤ A') (kB : T' ≤ B')
    (hi : Function.Injective (resG X hT)) {a : Γ(X, A)} {b : Γ(X, B)} {g : Γ(X, G)}
    (h : resG X kA (resG X hA' a) = resG X (hT.trans hG) g * resG X kB (resG X hB' b)) :
    resG X hA a = resG X hG g * resG X hB b := by
  apply hi
  simpa only [map_mul, resG_resG] using h
end GlobalTheory
