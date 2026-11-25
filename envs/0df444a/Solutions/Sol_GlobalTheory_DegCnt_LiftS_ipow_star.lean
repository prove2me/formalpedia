-- Prove2me | solution 1 for GlobalTheory.DegCnt.LiftS.ipow_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:20:57.292355+00:00
-- url     : https://prove2.me/submissions/bc4d9168-d6ff-427a-bd06-8d21bac633d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_star_one_mem
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_pow_star

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.LiftS
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace GlobalTheory.DegCnt.LiftS
theorem _root_.solution (𝔡 : Ideal (𝓞 K)) (h0 : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℤ)
    {x : K} (hx : x ∈ ipow 𝔡 n) : star x ∈ ipow 𝔡 n := by
  unfold ipow at hx ⊢
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast] at hx ⊢
    exact pow_star 𝔡 hs m x hx
  · have hne : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ m) ≠ 0 :=
      pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 h0)
    rw [zpow_neg, zpow_natCast] at hx ⊢
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff hne] at hx ⊢
    intro y hy
    have h1 := hx (star y) (pow_star 𝔡 hs m y hy)
    rw [FractionalIdeal.mem_one_iff] at h1 ⊢
    obtain ⟨w, hw⟩ := h1
    have h2 : star (algebraMap (𝓞 K) K w) ∈ (1 : Submodule (𝓞 K) K) :=
      star_one_mem (Submodule.mem_one.2 ⟨w, rfl⟩)
    obtain ⟨v, hv⟩ := Submodule.mem_one.1 h2
    refine ⟨v, ?_⟩
    rw [hv, hw, star_mul, star_star, mul_comm]
end GlobalTheory.DegCnt.LiftS
