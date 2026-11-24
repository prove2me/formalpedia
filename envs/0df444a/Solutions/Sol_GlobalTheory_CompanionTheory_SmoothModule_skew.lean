-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:01:27.825057+00:00
-- url     : https://prove2.me/submissions/7e7e2a34-1e43-48a0-8d51-ddd063f42a77

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_exp_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_inner_rep
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
open scoped InnerProductSpace
open PI.UpqRep (IsURepOn UJset inG)
open PI.DSInfCharCap (dsigC thetaJ)
open PI.PhMeasCore (dsig smoothVecs)
open Formalism.REAL (Jm)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothModule
variable {n : ℕ} {ε : Fin n → Bool}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
namespace GlobalTheory.CompanionTheory.SmoothModule
theorem _root_.solution (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v w v' w' : H}
    (hv : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0)
    (hw : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) w) w' 0) :
    ⟪v', w⟫_ℂ = -⟪v, w'⟫_ℂ := by
  have h := HasDerivAt.inner ℂ hv hw
  simp only [inner_rep hσ (exp_mem (inG_smul _ hX)), Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero,
    hσ.1.1, one_apply_eq_self] at h
  have := h.unique (hasDerivAt_const _ _)
  linear_combination this
end GlobalTheory.CompanionTheory.SmoothModule
