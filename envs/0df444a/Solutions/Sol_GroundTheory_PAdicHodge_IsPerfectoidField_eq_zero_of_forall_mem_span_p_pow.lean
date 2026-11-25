-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.eq_zero_of_forall_mem_span_p_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:14.065931+00:00
-- url     : https://prove2.me/submissions/2709fe6b-db87-41d6-9e32-8c0baf77ff69

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_BdRLattice

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
open Ideal WittVector IsLocalRing
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔹" => BDeRhamPlus (normInteger K) p
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger K) p))
omit [CharZero K]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {b : 𝒪} (h : ∀ M : ℕ, b ∈ span {(p : 𝒪) ^ M}) : b = 0 := by
  have := isAdicComplete (K := K) p
  refine IsHausdorff.haus (I := span {(p : 𝒪)}) inferInstance _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, mul_top, span_singleton_pow]
  exact h n
end GroundTheory.PAdicHodge.IsPerfectoidField
