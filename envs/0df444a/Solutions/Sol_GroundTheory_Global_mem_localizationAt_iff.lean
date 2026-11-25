-- Prove2me | solution 1 for GroundTheory.Global.mem_localizationAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:56.488258+00:00
-- url     : https://prove2.me/submissions/6893679b-803c-4f43-9b7b-8d234d11b5a8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Polynomial
noncomputable section
variable (L : Type*) [Field L] [NumberField L]
variable {L}
namespace GroundTheory.Global
theorem _root_.solution {v : HeightOneSpectrum (𝓞 L)} {x : L} :
    x ∈ localizationAt L v ↔ ∃ a s : 𝓞 L, s ∉ v.asIdeal ∧
      x = algebraMap (𝓞 L) L a * (algebraMap (𝓞 L) L s)⁻¹ := by
  unfold localizationAt Localization.subalgebra.ofField
  rw [← SetLike.mem_coe, Subalgebra.coe_copy]
  simp only [Set.mem_ofPred_eq, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_compl_iff, SetLike.mem_coe, exists_prop]
end GroundTheory.Global
