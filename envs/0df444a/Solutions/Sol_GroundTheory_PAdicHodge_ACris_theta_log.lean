-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.theta_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:07.483267+00:00
-- url     : https://prove2.me/submissions/1778b069-c2c6-4360-bbf3-686e409648d8

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Theorems.Thm_GroundTheory_PAdicHodge_IsAdicSum_unique
import Theorems.Thm_GroundTheory_PAdicHodge_isAdicSum_of_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_isAdicSum_log
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_theta_logTerm

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
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
variable [CharZero K]
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution {x : AInf K p} (hx : x ∈ RingHom.ker θ) : theta K p (log hx) = 0 := by
  have hle : 𝔭 ≤ (Ideal.span {(p : 𝒪)}).comap (theta K p) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _
  have h := (isAdicSum_log hx).map (theta K p) hle
  have h0 : IsAdicSum (Ideal.span {(p : 𝒪)}) (fun n => theta K p (logTerm hx n)) 0 := by
    have := isAdicSum_of_eq_zero (I := Ideal.span {(p : 𝒪)})
      (a := fun n => theta K p (logTerm hx n)) (m := 0) (fun n _ => theta_logTerm hx n)
    simpa using this
  exact h.unique h0
end GroundTheory.PAdicHodge.ACris
