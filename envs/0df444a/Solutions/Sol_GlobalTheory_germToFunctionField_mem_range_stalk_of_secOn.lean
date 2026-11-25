-- Prove2me | solution 1 for GlobalTheory.germToFunctionField_mem_range_stalk_of_secOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:05:25.424257+00:00
-- url     : https://prove2.me/submissions/04f516f6-3ee6-422d-a4fa-2c5badf6ea72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_germToFunctionField_mem_range_stalk
import Theorems.Thm_GlobalTheory_germToFunctionField_res
import Theorems.Thm_GlobalTheory_nonempty_inf_of_isIntegral
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
variable [IsIntegral X]
namespace GlobalTheory
theorem _root_.solution {L : LB X} {W : X.Opens}
    {s : ∀ i, Γ(X, W ⊓ L.U i)} (hs : s ∈ secOn L W) {x : X} {i j : L.ι} (hi : x ∈ L.U i)
    (hj : x ∈ L.U j) [Nonempty (W ⊓ L.U i : X.Opens)] [Nonempty (W ⊓ L.U j : X.Opens)]
    (h : X.germToFunctionField _ (s j) ∈
      (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    X.germToFunctionField _ (s i) ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  have : Nonempty (L.U j) := ⟨⟨x, hj⟩⟩
  have : Nonempty (L.U i ⊓ L.U j : X.Opens) := ⟨⟨x, hi, hj⟩⟩
  have := nonempty_inf_of_isIntegral (W ⊓ L.U i) (L.U j)
  have e := congrArg (X.germToFunctionField (W ⊓ L.U i ⊓ L.U j)) (hs i j)
  rw [map_mul] at e
  erw [germToFunctionField_res, germToFunctionField_res, germToFunctionField_res] at e
  rw [e]
  exact mul_mem (germToFunctionField_mem_range_stalk _ _ ⟨hi, hj⟩) h
end GlobalTheory
