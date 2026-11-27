-- Prove2me | solution 1 for GroundTheory.Global.KummerIndex.exists_mul_zpow_inv_mem_unitsPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:45:31.330433+00:00
-- url     : https://prove2.me/submissions/6da6b3f3-f5e9-4067-aaf7-4c1e279ac92d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_KummerIndexLemma_HasEnoughRootsOfUnityOfRingHom
import Theorems.Thm_GroundTheory_Global_KummerIndex_natCard_localUnitClasses

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
theorem _root_.solution (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity K p]
    (hv : (p : 𝓞 K) ∉ v.asIdeal) {a x : (v.adicCompletion K)ˣ} (ha : a ∈ localUnits v)
    (hx : x ∈ localUnits v) (hap : a ∉ unitsPow (v.adicCompletion K) p) :
    ∃ k : ℤ, x * (a ^ k)⁻¹ ∈ unitsPow (v.adicCompletion K) p := by
  let g : localUnitClasses v p := ⟨QuotientGroup.mk' _ a, Subgroup.mem_map_of_mem _ ha⟩
  let g' : localUnitClasses v p := ⟨QuotientGroup.mk' _ x, Subgroup.mem_map_of_mem _ hx⟩
  have hg : g ≠ 1 := by
    intro h
    apply hap
    have h' : QuotientGroup.mk' (unitsPow (v.adicCompletion K) p) a = 1 := congrArg Subtype.val h
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (mem_zpowers_of_prime_card (natCard_localUnitClasses v p hv) hg (g' := g'))
  refine ⟨k, ?_⟩
  have h' : QuotientGroup.mk' (unitsPow (v.adicCompletion K) p) a ^ k =
      QuotientGroup.mk' (unitsPow (v.adicCompletion K) p) x := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_zpow] at this
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
  change QuotientGroup.mk' _ x * (QuotientGroup.mk' _ a ^ k)⁻¹ = 1
  rw [h']
  exact mul_inv_cancel _
end GroundTheory.Global.KummerIndex
