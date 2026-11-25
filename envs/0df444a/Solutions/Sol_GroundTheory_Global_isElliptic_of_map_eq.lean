-- Prove2me | solution 1 for GroundTheory.Global.isElliptic_of_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:49.78825+00:00
-- url     : https://prove2.me/submissions/1e51eec4-5e69-4d43-af92-a6ac97a33262

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll

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
open NumberField IsDedekindDomain IsLocalRing
noncomputable section
variable {L : Type*} [Field L] [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution {v : HeightOneSpectrum (𝓞 L)} {E : WeierstrassCurve L} [E.IsElliptic]
    {W : WeierstrassCurve (localizationAt L v)} (h : W.map (algebraMap (localizationAt L v) L) = E)
    (hΔ : E.Δ⁻¹ ∈ localizationAt L v) : W.IsElliptic := by
  have hW : algebraMap (localizationAt L v) L W.Δ = E.Δ := by
    rw [← WeierstrassCurve.map_Δ, h]
  rw [WeierstrassCurve.isElliptic_iff]
  refine isUnit_iff_exists_inv.mpr ⟨⟨E.Δ⁻¹, hΔ⟩, Subtype.ext ?_⟩
  change algebraMap (localizationAt L v) L W.Δ * E.Δ⁻¹ = 1
  rw [hW]
  exact mul_inv_cancel₀ E.isUnit_Δ.ne_zero
end GroundTheory.Global
