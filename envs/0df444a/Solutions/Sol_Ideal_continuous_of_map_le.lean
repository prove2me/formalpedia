-- Prove2me | solution 1 for Ideal.continuous_of_map_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:49.012479+00:00
-- url     : https://prove2.me/submissions/1f53b83b-0d3b-46d6-b625-4ae9581fae01

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open WittVector Filter Topology
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
omit hp [IsPerfectoidField K p]
namespace GroundTheory.PAdicHodge.AInf
namespace _root_.Ideal
theorem _root_.solution {A B F : Type*} [CommRing A] [CommRing B] [FunLike F A B]
    [RingHomClass F A B] (f : F) {I : Ideal A} {J : Ideal B} (h : I.map f ≤ J) :
    @Continuous A B I.adicTopology J.adicTopology f := by
  refine (@continuous_iff_continuousAt A B I.adicTopology J.adicTopology f).2 fun x => ?_
  change Tendsto f (@nhds A I.adicTopology x) (@nhds B J.adicTopology (f x))
  rw [(I.hasBasis_nhds_adic x).tendsto_iff (J.hasBasis_nhds_adic (f x))]
  intro n _
  refine ⟨n, trivial, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  refine ⟨f d, ?_, (map_add f x d).symm⟩
  have : f d ∈ (I.map f) ^ n := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f hd
  exact Ideal.pow_right_mono h n this
end _root_.Ideal
end GroundTheory.PAdicHodge.AInf
