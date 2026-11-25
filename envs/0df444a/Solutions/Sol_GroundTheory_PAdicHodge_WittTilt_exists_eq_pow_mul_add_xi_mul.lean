-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.exists_eq_pow_mul_add_xi_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:55:03.002071+00:00
-- url     : https://prove2.me/submissions/4b5feeef-915c-41ba-abd7-db7939c86b0f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_norm_p_pos
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_norm_theta_le
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_surjective_fontaineTheta


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
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector Laurent
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p
variable {ρ : ℝ}
variable [CharZero K]
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ}) {k : ℕ}
    {y : AInf K p} (hy : gn K p ‖(p : K)‖ (algebraMap (AInf K p) 𝔸 y) ≤ ‖(p : K)‖ ^ k) :
    ∃ w z : AInf K p, y = (p : AInf K p) ^ k * w + ξ * z := by
  have hθ := (norm_theta_le y).trans hy
  have hpk : ((p : K) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  set c : K := ((θ y : 𝒪) : K) / (p : K) ^ k with hc_def
  have hc : ‖c‖ ≤ 1 := by
    rw [hc_def, norm_div, norm_pow, div_le_one (pow_pos norm_p_pos k)]
    exact hθ
  obtain ⟨w, hw⟩ := IsPerfectoidField.surjective_fontaineTheta (K := K) (p := p) ⟨c, mem_normInteger.2 hc⟩
  have hker : y - (p : AInf K p) ^ k * w ∈ RingHom.ker θ := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_pow, map_natCast, hw]
    apply Subtype.ext
    push_cast
    rw [hc_def]
    field_simp
    ring
  rw [hξ] at hker
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hker
  exact ⟨w, z, by rw [mul_comm ξ, hz]; ring⟩
end GroundTheory.PAdicHodge.WittTilt
