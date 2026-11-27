-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.ker_fontaineTheta_comp_frobeniusEquiv_symm_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-27T03:09:10.286353+00:00
-- url     : https://prove2.me/submissions/e98f67f3-e04f-4f42-88ab-0c5745800678

import Mathlib
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_ker_fontaineTheta_eq_span_xi
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
theorem solution {ε : 𝒪♭}
    (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    RingHom.ker ((fontaineTheta (normInteger K) p).comp ((φ).symm : AInf K p ≃+* AInf K p).toRingHom) =
      Ideal.span {∑ i ∈ Finset.range p, teichmuller p ε ^ i} := by
  have hφ : ∀ x : 𝒪♭, (φ) (teichmuller p ((_root_.frobeniusEquiv 𝒪♭ p).symm x)) = teichmuller p x := by
    intro x
    rw [WittVector.frobeniusEquiv_apply, WittVector.frobenius_eq_map_frobenius,
      WittVector.map_teichmuller, frobenius_apply_frobeniusEquiv_symm]
  rw [← RingHom.comap_ker, AInf.ker_fontaineTheta_eq_span_xi hε hζ]
  have h1 : Ideal.comap ((φ).symm : AInf K p ≃+* AInf K p).toRingHom (Ideal.span {xi ε}) =
      Ideal.map ((φ).symm : AInf K p ≃+* AInf K p).symm (Ideal.span {xi ε}) :=
    (Ideal.map_symm _).symm
  rw [h1, Ideal.map_span, Set.image_singleton]
  congr 2
  rw [RingEquiv.symm_symm, xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, hφ]
