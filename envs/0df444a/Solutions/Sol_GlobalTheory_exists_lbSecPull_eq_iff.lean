-- Prove2me | solution 1 for GlobalTheory.exists_lbSecPull_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:54:17.483171+00:00
-- url     : https://prove2.me/submissions/0e20329e-7260-494e-9776-871abf67aea3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_lbSec_ext
import Theorems.Thm_GlobalTheory_exists_sec_res_eq_iff
import Theorems.Thm_P2M_GlobalTheory_bijective___appLE_4ffb2aed58ba
import Theorems.Thm_GlobalTheory_existsUnique_secOn_of_pull
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
theorem _root_.solution [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    {L : LB X} (hL : L.IsLB) {W : X.Opens} [Nonempty W] (r : (L.pull W.ι).Sec) :
    (∃ t : L.Sec, lbSecPull L t W.ι = r) ↔
      ∀ x : X, Order.coheight x = 1 → x ∉ W →
        ∃ (i : L.ι) (_ : Nonempty (W ⊓ L.U i : X.Opens)) (a : Γ(X, W ⊓ L.U i)), x ∈ L.U i ∧
          (W.ι.appLE (W ⊓ L.U i) _ (lb_pull_ι_U L W fun _ ↦ i).le).hom a = r.f (fun _ ↦ i) ∧
          X.germToFunctionField (W ⊓ L.U i) a ∈
            (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  have hb (j : PUnit.{1} → L.ι) := bijective_ι_appLE W inf_le_left (lb_pull_ι_U L W j)
  obtain ⟨s, ⟨hs, hr⟩, -⟩ := existsUnique_secOn_of_pull L W r
  have h1 : (∃ t : L.Sec, lbSecPull L t W.ι = r) ↔
      ∃ t : L.Sec, ∀ i, resG X inf_le_right (t.f i) = s i := by
    refine exists_congr fun t ↦ ⟨fun h i ↦ (hb fun _ ↦ i).1 ?_, fun h ↦ lbSec_ext fun j ↦ ?_⟩
    · refine (appLE_res_apply W.ι _ _ _).trans (Eq.trans ?_ (hr fun _ ↦ i).symm)
      rw [← h]
      rfl
    · refine Eq.trans ?_ (hr j)
      rw [← h]
      exact (appLE_res_apply W.ι _ _ _).symm
  rw [h1, exists_sec_res_eq_iff hL hs]
  refine forall₃_congr fun x _ _ ↦ exists₂_congr fun i _ ↦
    ⟨fun h ↦ ⟨s i, h.1, hr fun _ ↦ i, h.2⟩, fun ⟨a, h1, h2, h3⟩ ↦ ⟨h1, ?_⟩⟩
  rwa [← (hb fun _ ↦ i).1 (h2.trans (hr fun _ ↦ i).symm)]
end GlobalTheory
