-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.iotaM_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:42:10.390723+00:00
-- url     : https://prove2.me/submissions/a9f6ad59-ea8f-4e27-9078-be7e8c9ffee5

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdR
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdRInj
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_ACris_eval__iota_3d791609d947


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
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution {y : ACris K p} (hy : iota K p y = 0) (m : ℕ) : embedding₂ K p m y = 0 := by
  have h := evalₐ_iota (K := K) (p := p) m y
  have h0 : @Eq (_root_.AdicCompletion (kerAway K p) 𝔸) (iota K p y) 0 := hy
  rw [h0, map_zero] at h
  exact Subtype.ext h.symm
end GroundTheory.PAdicHodge.ACris
