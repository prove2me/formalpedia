-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSStabLink.deriv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:17.990928+00:00
-- url     : https://prove2.me/submissions/49e1c01f-5b4a-48ea-883e-616b7cda7b2e

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExpMemUJ
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix Finset Filter Topology Set
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSStabLink
open PI.UpqRep CompanionTheory.D.DSIC
namespace GlobalTheory.CompanionTheory.DSStabLink
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (c : ℝ → H) (z : H) (hc : ∀ t, c t ∈ W) (hz : HasDerivAt c z 0) :
    z ∈ W := by
  set Q : H →L[ℂ] H := Wᗮ.starProjection with hQ
  have hQW : ∀ w ∈ W, Q w = 0 := fun w hw => Submodule.starProjection_orthogonal_apply_eq_zero hw
  have hQs : ∀ x, x - Q x ∈ W := fun x => by
    have := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) x
    rwa [Submodule.orthogonal_orthogonal] at this
  have h1 : HasDerivAt (fun t => Q (c t)) (Q z) 0 :=
    (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hz
  have h2 : (fun t => Q (c t)) = fun _ => 0 := funext fun t => hQW _ (hc t)
  rw [h2] at h1
  have h3 : Q z = 0 := h1.unique (hasDerivAt_const _ _)
  simpa [h3] using hQs z
end GlobalTheory.CompanionTheory.DSStabLink
