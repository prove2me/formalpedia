-- Prove2me | solution 1 for GroundTheory.Global.KummerIndex.ordMod_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:36:01.563635+00:00
-- url     : https://prove2.me/submissions/844293e2-54b6-4f8d-bd2c-4dc9f1d9516e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_KummerIndexLemma_HasEnoughRootsOfUnityOfRingHom
import Theorems.Thm_GroundTheory_Global_KummerIndex_exists_uniformizer_unit
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
theorem _root_.solution (p : ℕ) [NeZero p] : Function.Surjective (ordMod v p) := by
  obtain ⟨π, hπ⟩ := exists_uniformizer_unit v
  intro z
  refine ⟨π ^ (Multiplicative.toAdd z).val, ?_⟩
  change Multiplicative.ofAdd (((-log (Valued.v ((π ^ (Multiplicative.toAdd z).val :
    (v.adicCompletion K)ˣ) : v.adicCompletion K)) : ℤ) : ZMod p)) = z
  rw [Units.val_pow_eq_pow_val, map_pow, hπ, ← exp_nsmul, log_exp]
  simp only [smul_neg, nsmul_eq_mul, mul_one, neg_neg, Int.cast_natCast, ZMod.natCast_zmod_val]
  rfl
end GroundTheory.Global.KummerIndex
