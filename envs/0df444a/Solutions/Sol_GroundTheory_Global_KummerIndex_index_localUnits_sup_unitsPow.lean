-- Prove2me | solution 1 for GroundTheory.Global.KummerIndex.index_localUnits_sup_unitsPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:07.111613+00:00
-- url     : https://prove2.me/submissions/75c36243-5390-4a87-b723-4cffa240106a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_KummerIndexLemma_HasEnoughRootsOfUnityOfRingHom
import Theorems.Thm_GroundTheory_Global_KummerIndex_ordMod_surjective
import Theorems.Thm_GroundTheory_Global_KummerIndex_ker_ordMod
import Theorems.Thm_GroundTheory_Global_coe_integerEquivAdicCompletionIntegers
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_ProfCoh_kummerPairingLeft_apply
import Theorems.Thm_GroundTheory_ProfCoh_kummerPairingRight_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.coe_integerEquivAdicCompletionIntegers
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.ProfCoh.kummerPairingLeft_apply
attribute [local simp] GroundTheory.ProfCoh.kummerPairingRight_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh WithZero
open GroundTheory.Global.KummerIndex
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global.KummerIndex
theorem _root_.solution (p : ℕ) [NeZero p] :
    (localUnits v ⊔ unitsPow (v.adicCompletion K) p).index = p := by
  rw [← ker_ordMod, Subgroup.index_ker, (ordMod v p).range_eq_top_of_surjective
    (ordMod_surjective v p), Subgroup.card_top, Nat.card_eq_fintype_card]
  simp
end GroundTheory.Global.KummerIndex
