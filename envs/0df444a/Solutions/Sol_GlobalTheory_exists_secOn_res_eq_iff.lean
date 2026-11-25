-- Prove2me | solution 1 for GlobalTheory.exists_secOn_res_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:27:03.506944+00:00
-- url     : https://prove2.me/submissions/3b74f41b-c3b9-4ed3-a431-765320e3bcac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_germToFunctionField_mem_range_stalk
import Theorems.Thm_GlobalTheory_germToFunctionField_res
import Theorems.Thm_GlobalTheory_resG_eq_mul_of_injective
import Theorems.Thm_GlobalTheory_nonempty_inf_of_isIntegral
import Theorems.Thm_GlobalTheory_injective_resG_of_inf_le
import Theorems.Thm_GlobalTheory_exists_resG_eq_of_secOn
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_mem_of_cover


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
variable [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
namespace GlobalTheory
theorem _root_.solution {L : LB X} (hL : L.IsLB) {V W : X.Opens} (h : W ≤ V) [Nonempty W]
    {s : ∀ i, Γ(X, W ⊓ L.U i)} (hs : s ∈ secOn L W) :
    (∃ t ∈ secOn L V, ∀ i, resG X (inf_le_inf_right _ h) (t i) = s i) ↔
      ∀ x ∈ V, Order.coheight x = 1 → x ∉ W →
        ∃ (i : L.ι) (_ : Nonempty (W ⊓ L.U i : X.Opens)), x ∈ L.U i ∧
          X.germToFunctionField (W ⊓ L.U i) (s i) ∈
            (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  constructor
  · rintro ⟨t, -, ht⟩ x hx - -
    obtain ⟨i, hi⟩ := LB.mem_of_cover hL x
    have : Nonempty (L.U i) := ⟨⟨x, hi⟩⟩
    have : Nonempty (V ⊓ L.U i : X.Opens) := ⟨⟨x, hx, hi⟩⟩
    have := nonempty_inf_of_isIntegral W (L.U i)
    refine ⟨i, this, hi, ?_⟩
    rw [← ht]
    erw [germToFunctionField_res]
    exact germToFunctionField_mem_range_stalk _ _ ⟨hx, hi⟩
  · intro H
    choose t ht using fun i ↦ exists_resG_eq_of_secOn hs i (inf_le_inf_right _ h) inf_le_right
      fun x hx ↦ H x hx.1
    refine ⟨t, fun i j ↦ ?_, ht⟩
    refine resG_eq_mul_of_injective _ _ _ (inf_le_inf_right _ h) (inf_le_inf_right _ h)
      (inf_le_inf_right _ (inf_le_inf_right _ h) : W ⊓ L.U i ⊓ L.U j ≤ _) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (injective_resG_of_inf_le W _ fun x hx ↦ ⟨⟨hx.1, hx.2.1.2⟩, hx.2.2⟩) ?_
    rw [ht, ht]
    exact hs i j
end GlobalTheory
