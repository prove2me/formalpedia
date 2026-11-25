-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.norm_xi_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:28:08.093211+00:00
-- url     : https://prove2.me/submissions/18e61a76-b15b-40bf-8141-3b1aa90e9a84

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_sub_one_pow
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_ne_one_of_untilt_ne_one
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_xi_coeff_zero

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
open WittVector
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    ‖(xi ε).coeff 0‖ = ‖(p : K)‖ := by
  set e := (_root_.frobeniusEquiv 𝒪♭ p).symm ε
  have hgeom : (xi ε).coeff 0 * (e - 1) = ε - 1 := by
    rw [xi_coeff_zero, geom_sum_mul, frobeniusEquiv_symm_pow_p]
  have hfrob : ‖e - 1‖ ^ p = ‖ε - 1‖ := by
    rw [← norm_pow, sub_pow_char, one_pow, frobeniusEquiv_symm_pow_p]
  have hne : ‖ε - 1‖ ≠ 0 := by
    rw [norm_ne_zero_iff, sub_ne_zero]
    exact ne_one_of_untilt_ne_one hζ
  have h1 : ‖(xi ε).coeff 0‖ ^ p * ‖ε - 1‖ = ‖(p : K)‖ ^ p * ‖ε - 1‖ :=
    calc ‖(xi ε).coeff 0‖ ^ p * ‖ε - 1‖ = ‖(xi ε).coeff 0‖ ^ p * ‖e - 1‖ ^ p := by rw [hfrob]
      _ = ‖(xi ε).coeff 0 * (e - 1)‖ ^ p := by rw [norm_mul, mul_pow]
      _ = ‖ε - 1‖ ^ p := by rw [hgeom]
      _ = ‖ε - 1‖ ^ (p - 1) * ‖ε - 1‖ := by rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
      _ = ‖(p : K)‖ ^ p * ‖ε - 1‖ := by rw [norm_sub_one_pow hε hζ]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hp.out.ne_zero).1
    (mul_right_cancel₀ hne h1)
end GroundTheory.PAdicHodge.AInf
