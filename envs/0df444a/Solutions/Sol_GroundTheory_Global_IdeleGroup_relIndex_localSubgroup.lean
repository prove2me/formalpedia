-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.relIndex_localSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:54:22.798428+00:00
-- url     : https://prove2.me/submissions/32041fc1-ad89-43f7-b3f1-ea722e5713b2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Theorems.Thm_GroundTheory_Global_IdeleGroup_ker_localQuotientMap
import Theorems.Thm_GroundTheory_Global_IdeleGroup_localQuotientMap_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable (S T : Set (HeightOneSpectrum (𝓞 K)))
  (H : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
  (H' : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ)
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (localSubgroup S T H H').relIndex (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) =
      (∏ v ∈ S, (H v).index) * ∏ w : InfinitePlace K, (H' w).index := by
  have hk := Subgroup.index_ker (G' := (∀ v : S, (v.1.adicCompletion K)ˣ ⧸ H v.1) ×
    (∀ w : InfinitePlace K, (w.Completion)ˣ ⧸ H' w)) (localQuotientMap T H H' S)
  rw [Subgroup.relIndex, ← ker_localQuotientMap, hk,
    MonoidHom.range_eq_top_of_surjective _ (localQuotientMap_surjective T H H' S),
    Subgroup.card_top, Nat.card_prod, Nat.card_pi, Nat.card_pi, ← Finset.prod_coe_sort S]
  rfl
end GroundTheory.Global.IdeleGroup
