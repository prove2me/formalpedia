-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.sub_one_dvd_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:58:04.085893+00:00
-- url     : https://prove2.me/submissions/a3047417-29f8-40b0-b8ce-e94303326d48

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaAInf
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_exists_mul_frobeniusEquiv_symm_pow_mu_eq
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_constantCoeff_mu
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_constantCoeff_frobeniusEquiv_symm_pow_mu
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_frobeniusEquiv_symm_pow_sub_one_pow
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_ne_one_of_untilt_ne_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
open _root_.WittVector
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {a : AInf K p}
    (ha : ∀ n : ℕ, θ ((φ ^ n) a) = 0) : ε - 1 ∣ WittVector.constantCoeff a := by
  rw [preTilt_dvd_iff_norm_le]
  set r := ‖ε - 1‖ with hr
  set x := ‖WittVector.constantCoeff a‖ with hx
  have hr0 : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 (ne_one_of_untilt_ne_one hζ))
  have key : ∀ N : ℕ, x ^ p ^ N * r ≤ r ^ p ^ N := by
    intro N
    obtain ⟨c, hc⟩ := exists_mul_frobeniusEquiv_symm_pow_mu_eq hε hζ N a ha
    have h := congrArg (fun y : AInf K p => ‖WittVector.constantCoeff y‖ ^ p ^ N) hc
    simp only [map_mul, norm_mul, mul_pow, constantCoeff_mu,
      constantCoeff_frobeniusEquiv_symm_pow_mu, norm_frobeniusEquiv_symm_pow_sub_one_pow] at h
    rw [h]
    calc r ^ p ^ N * ‖WittVector.constantCoeff c‖ ^ p ^ N ≤ r ^ p ^ N * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) (preTilt_norm_le_one _)
      _ = r ^ p ^ N := mul_one _
  by_contra hlt
  push_neg at hlt
  set q := x / r with hq
  have hq1 : 1 < q := by rw [hq, one_lt_div hr0]; exact hlt
  have hbound : ∀ N : ℕ, q ^ p ^ N * r ≤ 1 := by
    intro N
    have h := key N
    have hxq : x = q * r := by rw [hq, div_mul_cancel₀ _ hr0.ne']
    rw [hxq, mul_pow] at h
    have hrN : 0 < r ^ p ^ N := pow_pos hr0 _
    nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (r * (q - 1)))
  have hpN : (N : ℝ) < (p ^ N : ℕ) := by exact_mod_cast Nat.lt_pow_self hp.out.one_lt
  have hB := one_add_mul_le_pow (a := q - 1) (by linarith) (p ^ N)
  rw [add_sub_cancel] at hB
  have h3 := hbound N
  have hq0 : 0 < q - 1 := by linarith
  have h4 : (1 : ℝ) / (r * (q - 1)) < ((p ^ N : ℕ) : ℝ) := hN.trans hpN
  rw [div_lt_iff₀ (mul_pos hr0 hq0)] at h4
  push_cast at h4 hB
  nlinarith
end GroundTheory.PAdicHodge.AInf
