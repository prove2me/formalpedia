-- Prove2me | solution 1 for GlobalTheory.exists_sec_res_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:45:10.722494+00:00
-- url     : https://prove2.me/submissions/e3e67afd-2d9f-4549-a37f-7ff178ed6721

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_resG_resG
import Theorems.Thm_GlobalTheory_resG_refl
import Theorems.Thm_GlobalTheory_resG_eq_mul_of_injective
import Theorems.Thm_GlobalTheory_res_sec_mem_secOn
import Theorems.Thm_GlobalTheory_injective_resG_of_inf_le
import Theorems.Thm_GlobalTheory_exists_resG_eq_of_secOn
import Theorems.Thm_GlobalTheory_exists_secOn_res_eq_iff
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
variable [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
namespace GlobalTheory
theorem _root_.solution {L : LB X} (hL : L.IsLB) {W : X.Opens} [Nonempty W]
    {s : ∀ i, Γ(X, W ⊓ L.U i)} (hs : s ∈ secOn L W) :
    (∃ t : L.Sec, ∀ i, resG X inf_le_right (t.f i) = s i) ↔
      ∀ x : X, Order.coheight x = 1 → x ∉ W →
        ∃ (i : L.ι) (_ : Nonempty (W ⊓ L.U i : X.Opens)), x ∈ L.U i ∧
          X.germToFunctionField (W ⊓ L.U i) (s i) ∈
            (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  constructor
  · rintro ⟨t, ht⟩
    exact fun x ↦ (exists_secOn_res_eq_iff hL le_top hs).mp
      ⟨_, res_sec_mem_secOn ⊤ t, fun i ↦ (resG_resG _ _ _).trans (ht i)⟩ x trivial
  · intro H
    choose t ht using fun i ↦ exists_resG_eq_of_secOn hs i inf_le_right le_rfl fun x _ ↦ H x
    refine ⟨⟨t, fun i j ↦ ?_⟩, ht⟩
    refine Eq.trans ?_ (congrArg (· * _) (resG_refl _))
    refine resG_eq_mul_of_injective _ _ _ inf_le_right inf_le_right
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W ⊓ L.U i ⊓ L.U j ≤ _) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (injective_resG_of_inf_le W _ fun x hx ↦ ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩) ?_
    rw [ht, ht]
    exact hs i j
end GlobalTheory
