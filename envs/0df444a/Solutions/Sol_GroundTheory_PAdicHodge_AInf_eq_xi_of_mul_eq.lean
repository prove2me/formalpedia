-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.eq_xi_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T15:27:49.060794+00:00
-- url     : https://prove2.me/submissions/1cd84de2-c263-42bf-996a-f5da85080ca2

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
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

open GroundTheory.PAdicHodge.AInf in
theorem solution {ε : 𝒪♭}
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {x : AInf K p}
    (h : x * (φ).symm (mu ε) = mu ε) : x = xi ε := by
  set ε' := (_root_.frobeniusEquiv 𝒪♭ p).symm ε with hε'
  have hsymm : (φ).symm (teichmuller p ε) = teichmuller p ε' := by
    rw [show (φ).symm (teichmuller p ε) =
        WittVector.map (_root_.frobeniusEquiv (PreTilt (normInteger K) p) p).symm
          (teichmuller p ε) from rfl, map_teichmuller]
    simp [ε']
  have hμ : (φ).symm (mu ε) = teichmuller p ε' - 1 := by
    rw [mu, map_sub, map_one, hsymm]
  have hpow : teichmuller p ε = teichmuller p ε' ^ p := by
    have : ε = (_root_.frobeniusEquiv 𝒪♭ p) ε' := (Equiv.apply_symm_apply _ ε).symm
    rw [this]
    change teichmuller p (_root_.frobenius (PreTilt (normInteger K) p) p ε') =
      teichmuller p ε' ^ p
    rw [frobenius_def, map_pow]
  have hgeom :
      (∑ i ∈ Finset.range p, teichmuller p ε' ^ i) * (teichmuller p ε' - 1) =
        teichmuller p ε' ^ p - 1 :=
    geom_sum_mul (teichmuller p ε') p
  have hxi : mu ε = xi ε * (φ).symm (mu ε) := by
    calc
      mu ε = teichmuller p ε - 1 := rfl
      _ = teichmuller p ε' ^ p - 1 := by rw [hpow]
      _ = (∑ i ∈ Finset.range p, teichmuller p ε' ^ i) * (teichmuller p ε' - 1) := hgeom.symm
      _ = xi ε * (φ).symm (mu ε) := by
          rw [hμ, xi, hε']
  have hne : (φ).symm (mu ε) ≠ 0 := by
    intro h0
    have : teichmuller p ε' = 1 := sub_eq_zero.mp (hμ ▸ h0)
    have hcoeff : ε' = 1 := by
      simpa [teichmuller_coeff_zero, one_coeff_zero] using
        congrArg (fun w : AInf K p => w.coeff 0) this
    exact hζ (by rw [hcoeff, map_one])
  have : x * (φ).symm (mu ε) = xi ε * (φ).symm (mu ε) := by
    rw [h]
    exact hxi
  exact mul_right_cancel₀ hne this
