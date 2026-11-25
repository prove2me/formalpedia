-- Prove2me | solution 1 for GroundTheory.Global.KummerIndex.natCard_localUnitClasses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:22:33.877225+00:00
-- url     : https://prove2.me/submissions/e7331c7c-6de9-4044-b60c-53529fa4fe16

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_KummerIndexLemma_HasEnoughRootsOfUnityOfRingHom
import Theorems.Thm_GroundTheory_Global_KummerIndex_index_localUnits_sup_unitsPow
import Theorems.Thm_GroundTheory_Global_KummerIndex_index_unitsPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh WithZero
open GroundTheory.Global.KummerIndex
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global.KummerIndex
theorem _root_.solution (p : ℕ) [NeZero p] [HasEnoughRootsOfUnity K p]
    (hv : (p : 𝓞 K) ∉ v.asIdeal) : Nat.card (localUnitClasses v p) = p := by
  have hidx : (localUnitClasses v p).index = p := by
    rw [localUnitClasses, Subgroup.index_map, QuotientGroup.ker_mk',
      (QuotientGroup.mk' _).range_eq_top_of_surjective (QuotientGroup.mk'_surjective _),
      Subgroup.index_top, mul_one, index_localUnits_sup_unitsPow]
  have hcard : Nat.card (UnitsModPow (v.adicCompletion K) p) = p ^ 2 :=
    index_unitsPow v p hv
  have h := Subgroup.card_mul_index (localUnitClasses v p)
  rw [hidx, hcard, pow_two] at h
  exact Nat.eq_of_mul_eq_mul_right (NeZero.pos p) h
end GroundTheory.Global.KummerIndex
