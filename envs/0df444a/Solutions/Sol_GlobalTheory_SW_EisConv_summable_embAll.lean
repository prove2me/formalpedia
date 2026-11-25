-- Prove2me | solution 1 for GlobalTheory.SW.EisConv.summable_embAll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:17.586352+00:00
-- url     : https://prove2.me/submissions/086dd312-3082-4fd9-bf2e-97651a75a774

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant
import Theorems.Thm_GlobalTheory_SW_EisConv_one_le_norm_embAll
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisConv
namespace GlobalTheory.SW.EisConv
theorem _root_.solution (E m : Type) [Field E] [NumberField E] [Fintype m] (k : ℕ)
    (hk : Fintype.card m * Module.finrank ℚ E < k) :
    Summable fun w : m → 𝓞 E => ‖embAll E m w‖⁻¹ ^ k := by
  have hinj : Function.Injective (embAll E m) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    by_contra h
    have := one_le_norm_embAll h
    rw [hw, norm_zero] at this
    exact absurd this (by norm_num)
  set L := LinearMap.range (embAll E m) with hL
  have : DiscreteTopology L := by
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have : ({0} : Set L) = Metric.ball 0 1 := by
      ext ⟨_, w, rfl⟩
      by_cases h : w = 0
      · subst h; simp [Subtype.ext_iff]
      · have h1 := one_le_norm_embAll h
        have h2 : embAll E m w ≠ 0 := fun h2 => h (hinj (h2.trans (map_zero _).symm))
        simp [Subtype.ext_iff, h2, h1]
    rw [this]; exact Metric.isOpen_ball
  have hr : Module.finrank ℤ L < k := by
    rw [hL, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype]
    simpa [RingOfIntegers.rank] using hk
  exact (ZLattice.summable_norm_pow_inv L k hr).comp_injective
    (i := fun w => (⟨embAll E m w, w, rfl⟩ : L)) fun v w h => hinj (congrArg Subtype.val h)
end GlobalTheory.SW.EisConv
