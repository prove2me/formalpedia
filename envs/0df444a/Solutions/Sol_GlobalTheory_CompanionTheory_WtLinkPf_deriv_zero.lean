-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WtLinkPf.deriv_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:15:50.104285+00:00
-- url     : https://prove2.me/submissions/1984efb9-4d19-4484-abc9-fc26b7da6d88

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExpMul
import Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_diag_inG
import Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_exp_diag
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
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WtLinkPf
open PI.UpqRep
variable {n : ℕ}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace GlobalTheory.CompanionTheory.WtLinkPf
theorem _root_.solution {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ S} (h : CompanionTheory.D.DSIC.IsSmMod ε σ S E) (θ : Fin n → ℝ) (v : S) :
    HasDerivAt (fun t : ℝ => σ (tor (t • θ)) v) (∑ a, ((θ a : ℂ) * Complex.I) • (E a a v : H)) 0 := by
  have h1 := h.real (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) (diag_inG ε θ) v
  simp only [exp_diag] at h1
  convert h1 using 1
  simp [Matrix.diagonal_apply]
end GlobalTheory.CompanionTheory.WtLinkPf
