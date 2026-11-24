-- Prove2me | solution 1 for GlobalTheory.KSp.OpenCrit.eventually_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:31:58.920977+00:00
-- url     : https://prove2.me/submissions/3c8768a2-64c8-41e9-a6fb-86b97d0e6619

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSubgroupOfSiegelAndOppositeNhds
import Theorems.Thm_P2M_GlobalTheory_KSp_OpenCrit_continuous_blk___234ddeb328d5
import Theorems.Thm_P2M_GlobalTheory_KSp_OpenCrit_blk___one_6219ba4e2bbf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary Filter Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.OpenCrit
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]
variable [TopologicalSpace E] [IsTopologicalRing E] [ContinuousInv₀ E] [T2Space E]
namespace GlobalTheory.KSp.OpenCrit
theorem _root_.solution : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), IsUnit (mat c g).toBlocks₂₂.det := by
  have h : Tendsto (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂.det) (𝓝 1) (𝓝 1) := by
    have := ((continuous_blk₂₂ c).matrix_det).tendsto (1 : UG c (stdJ ν E))
    rwa [blk₂₂_one, det_one] at this
  filter_upwards [h.eventually_ne one_ne_zero] with g hg
  exact isUnit_iff_ne_zero.mpr hg
end GlobalTheory.KSp.OpenCrit
