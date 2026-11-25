-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_eq_untilt_add_p_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:16.911311+00:00
-- url     : https://prove2.me/submissions/8c3cfb01-3afc-4ac9-bf16-54cd8c2c6790

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
theorem _root_.solution {N : IntermediateField K♭ C♭} [FiniteDimensional K♭ N]
    {z : normInteger C} (hz : z ∈ untiltInteger K C p N) :
    ∃ a ∈ integerTilt K C p N, ∃ z' ∈ untiltInteger K C p N,
      z = PreTilt.untilt a + (p : normInteger C) * z' := by
  obtain ⟨u, rfl⟩ := hz
  set a0 : integerTilt K C p N := u.coeff 0
  have hmem : u - WittVector.teichmuller p a0 ∈ Ideal.span {(p : WittVector p (integerTilt K C p N))} := by
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    have h := map_sub (WittVector.constantCoeff (p := p) (R := integerTilt K C p N)) u
      (WittVector.teichmuller p a0)
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h
    rw [h, sub_self]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨a0, a0.2, _, ⟨v, rfl⟩, ?_⟩
  have hu : u = WittVector.teichmuller p a0 + v * p := by rw [hv]; ring
  conv_lhs => rw [hu]
  rw [RingHom.comp_apply, map_add, map_mul, map_natCast, map_add, map_mul, map_natCast,
    WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller, RingHom.comp_apply, mul_comm]
  rfl
end GroundTheory.PAdicHodge
