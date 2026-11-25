-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.exists_mul_frobeniusEquiv_symm_pow_mu_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:49:39.24419+00:00
-- url     : https://prove2.me/submissions/d50ad9e8-673f-4e3d-9974-5f218c439d4b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaAInf
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_frobenius_pow_succ_xi
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_natCast_ne_zero
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_ker_fontaineTheta_eq_span_xi
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_mu_eq_xi_mul


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
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) (N : ℕ) :
    ∀ a : AInf K p, (∀ n : ℕ, θ ((φ ^ n) a) = 0) →
      ∃ c : AInf K p, a * ((φ).symm ^ N) (mu ε) = mu ε * c := by
  induction N with
  | zero => exact fun a _ => ⟨a, by rw [pow_zero, RingAut.one_apply, mul_comm]⟩
  | succ N ih =>
    intro a ha
    have h0 : a ∈ RingHom.ker θ := by
      rw [RingHom.mem_ker]
      simpa using ha 0
    rw [ker_fontaineTheta_eq_span_xi hε hζ, Ideal.mem_span_singleton'] at h0
    obtain ⟨a₁, rfl⟩ := h0
    have hp0 := natCast_ne_zero hε hζ
    have h1 : ∀ n : ℕ, θ ((φ ^ n) (φ a₁)) = 0 := by
      intro n
      have h := ha (n + 1)
      rw [map_mul, map_mul, fontaineTheta_frobenius_pow_succ_xi hε n, mul_eq_zero] at h
      rw [← RingAut.mul_apply, ← pow_succ]
      exact h.resolve_right hp0
    obtain ⟨c, hc⟩ := ih _ h1
    refine ⟨(φ).symm c, ?_⟩
    have h2 := congrArg (φ).symm hc
    rw [map_mul, map_mul, RingEquiv.symm_apply_apply] at h2
    calc a₁ * xi ε * ((φ).symm ^ (N + 1)) (mu ε)
        = xi ε * (a₁ * (φ).symm (((φ).symm ^ N) (mu ε))) := by
          rw [pow_succ', RingAut.mul_apply]; ring
      _ = xi ε * ((φ).symm (mu ε) * (φ).symm c) := by rw [h2]
      _ = mu ε * (φ).symm c := by
          conv_rhs => rw [mu_eq_xi_mul ε]
          ring
end GroundTheory.PAdicHodge.AInf
