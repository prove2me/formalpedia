-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.IsPeriodic.limPunctured_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:18.197402+00:00
-- url     : https://prove2.me/submissions/cce95ba7-9c32-4a63-8411-2a39a9d07d91

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Theorems.Thm_GroundTheory_Global_Elliptic_tendsto_limPunctured
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℂ E]
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
namespace IsPeriodic
theorem _root_.solution {f : ℂ → E} (hp : IsPeriodic L f) {z l : ℂ}
    (hl : l ∈ L.lattice) (hf : MeromorphicAt f z) (ho : 0 ≤ meromorphicOrderAt f z) :
    limPunctured f (z + l) = limPunctured f z := by
  have h1 : Tendsto (fun w ↦ w - l) (𝓝[≠] (z + l)) (𝓝[≠] z) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun w ↦ w - l) (𝓝 (z + l)) (𝓝 (z + l - l)) :=
        (continuous_id.sub continuous_const).tendsto _
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      intro h
      apply hw
      simp only [mem_singleton_iff] at h ⊢
      rw [← h]; ring
  have h2 := (tendsto_limPunctured hf ho).comp h1
  have e : (f ∘ fun w ↦ w - l) = f := funext fun w ↦ hp.sub w hl
  rw [e] at h2
  exact h2.limUnder_eq
end IsPeriodic
end GroundTheory.Global.Elliptic
