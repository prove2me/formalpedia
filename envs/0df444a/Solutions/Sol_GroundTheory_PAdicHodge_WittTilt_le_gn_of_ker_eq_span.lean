-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.le_gn_of_ker_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:15:56.481713+00:00
-- url     : https://prove2.me/submissions/31606d97-8ed5-4de0-8d1d-0ce41b41ccb2

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdRInj
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonApprox
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_surjective_fontaineTheta
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_le_gaussNorm
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_convergesAt_zcoeff_incl
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_algebraMap
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_algebraMap_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_mul
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_norm_p_lt_one
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_norm_p_pos
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_zcoeff_incl_zero
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_untilt_eq_norm_natCast


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
open _root_.WittVector Laurent ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p
variable {ρ : ℝ}
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ}) :
    ‖(p : K)‖ ≤ gn K p ‖(p : K)‖ (algebraMap (AInf K p) 𝔸 ξ) := by
  set r₀ := ‖(p : K)‖ with hr₀
  obtain ⟨w, hw⟩ := exists_norm_untilt_eq_norm_natCast (K := K) (p := p)
  set u : K := ((PreTilt.untilt w : 𝒪) : K) / p with hu_def
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hr0 : 0 < ‖(p : K)‖ := norm_p_pos
  have hr1 : ‖(p : K)‖ < 1 := norm_p_lt_one
  have hu : ‖u‖ ≤ 1 := by rw [hu_def, norm_div, hw, div_self hr0.ne']
  obtain ⟨v, hv⟩ := IsPerfectoidField.surjective_fontaineTheta (K := K) (p := p)
    ⟨u, mem_normInteger.2 hu⟩
  have hker : teichmuller p w - (p : AInf K p) * v ∈ RingHom.ker θ := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_natCast, fontaineTheta_teichmuller, hv]
    apply Subtype.ext
    push_cast
    rw [hu_def]
    field_simp
    ring
  rw [hξ] at hker
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hker
  have h0 : (teichmuller p w - (p : AInf K p) * v).coeff 0 = w := by
    show WittVector.constantCoeff (teichmuller p w - (p : AInf K p) * v) = w
    rw [map_sub, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, sub_zero]
    exact teichmuller_coeff_zero p w
  have hlow : r₀ ≤ gn K p r₀ (algebraMap (AInf K p) 𝔸 (teichmuller p w - (p : AInf K p) * v)) := by
    rw [gn_algebraMap]
    have := (convergesAt_zcoeff_incl (teichmuller p w - (p : AInf K p) * v) hr0
      hr1).le_gaussNorm 0
    rw [zcoeff_incl_zero, h0, norm_algebraMap_preTilt, zpow_zero, mul_one, preTilt_norm_def, hw] at this
    exact this
  rw [← hz, map_mul, gn_mul hr0 hr1] at hlow
  exact hlow.trans (mul_le_of_le_one_left (gn_nonneg hr0 _)
    (gn_algebraMap_le_one hr0 hr1.le z))
end GroundTheory.PAdicHodge.WittTilt
