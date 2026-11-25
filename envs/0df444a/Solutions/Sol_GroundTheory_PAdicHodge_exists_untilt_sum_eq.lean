-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_untilt_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:14.486814+00:00
-- url     : https://prove2.me/submissions/f251ebb2-78d2-4acc-a589-e2978257d288

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_UntiltField
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
local notation "θ" => WittVector.fontaineTheta (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution {N : IntermediateField K♭ C♭} [FiniteDimensional K♭ N] {ι : Type*}
    (s : Finset ι) (a : ι → integerTilt K C p N) :
    ∃ z ∈ untiltInteger K C p N, PreTilt.untilt (∑ i ∈ s, (a i : 𝒪C♭)) =
      ∑ i ∈ s, PreTilt.untilt (a i : 𝒪C♭) + (p : normInteger C) * z := by
  set x : WittVector p (integerTilt K C p N) :=
    WittVector.teichmuller p (∑ i ∈ s, a i) - ∑ i ∈ s, WittVector.teichmuller p (a i)
  have hmem : x ∈ Ideal.span {(p : WittVector p (integerTilt K C p N))} := by
    have hs : (∑ i ∈ s, WittVector.teichmuller p (a i)).coeff 0 = ∑ i ∈ s, a i := by
      have := map_sum (WittVector.constantCoeff (p := p) (R := integerTilt K C p N))
        (fun i => WittVector.teichmuller p (a i)) s
      simpa only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] using this
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    show (WittVector.teichmuller p (∑ i ∈ s, a i) -
      ∑ i ∈ s, WittVector.teichmuller p (a i)).coeff 0 = 0
    have h := map_sub (WittVector.constantCoeff (p := p) (R := integerTilt K C p N))
      (WittVector.teichmuller p (∑ i ∈ s, a i)) (∑ i ∈ s, WittVector.teichmuller p (a i))
    simp only [WittVector.constantCoeff_apply] at h
    rw [h, hs, WittVector.teichmuller_coeff_zero, sub_self]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨_, ⟨v, rfl⟩, ?_⟩
  have hx : WittVector.teichmuller p (∑ i ∈ s, a i) =
      ∑ i ∈ s, WittVector.teichmuller p (a i) + v * p := by rw [hv]; ring
  have := congrArg (RingHom.comp θ (WittVector.map (integerTilt K C p N).subtype)) hx
  simp only [RingHom.comp_apply, map_add, map_sum, map_mul, map_natCast,
    WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller, map_sum] at this
  rw [mul_comm] at this
  convert this using 2 <;> rfl
end GroundTheory.PAdicHodge
