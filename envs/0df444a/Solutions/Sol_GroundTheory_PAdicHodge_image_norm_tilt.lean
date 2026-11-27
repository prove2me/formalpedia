-- Prove2me | solution 1 for GroundTheory.PAdicHodge.image_norm_tilt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:48:37.963124+00:00
-- url     : https://prove2.me/submissions/2c309f17-fafb-4c2c-86fd-842b5a23ed32

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_TiltCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Theorems.Thm_GroundTheory_PAdicHodge_exists_tilt_norm_eq

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
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology NNReal
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "♮" x:max => ((PreTilt.untilt x : normInteger K) : K)
namespace GroundTheory.PAdicHodge
theorem _root_.solution :
    (fun x : K♭ => ‖x‖) '' {0}ᶜ = (fun y : K => ‖y‖) '' {0}ᶜ := by
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨tiltSharp K p x, fun h => hx ?_, rfl⟩
    exact tiltSharp_eq_zero_iff.1 h
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx⟩ := exists_tilt_norm_eq (K := K) (p := p) hy
    refine ⟨x, fun h => hy ?_, hx⟩
    rw [Set.mem_singleton_iff] at h
    rw [h, norm_zero, eq_comm, norm_eq_zero] at hx
    exact hx
end GroundTheory.PAdicHodge
