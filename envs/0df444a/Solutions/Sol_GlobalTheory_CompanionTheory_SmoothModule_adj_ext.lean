-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.adj_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:15.816649+00:00
-- url     : https://prove2.me/submissions/cc8360d2-8581-4e81-9637-37c6108b084b

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket
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
namespace GlobalTheory.CompanionTheory.SmoothModule
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ V)
    (h : ∀ X, inG ε X → ∀ x y, ⟪C X x, y⟫_ℂ = -⟪x, C X y⟫_ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) (x y : V) :
    ⟪C Y x, y⟫_ℂ = -⟪x, C (thetaJ ε Y) y⟫_ℂ := by
  rw [← re_add_im (ε := ε) Y, theta_pair (inG_re Y) (inG_im Y)]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    inner_add_left, inner_sub_right, inner_smul_left, inner_smul_right, h _ (inG_re Y), h _ (inG_im Y),
    Complex.conj_I]
  ring
end GlobalTheory.CompanionTheory.SmoothModule
