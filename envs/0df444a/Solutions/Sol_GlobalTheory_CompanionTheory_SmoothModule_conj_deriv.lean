-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.conj_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:01:27.213581+00:00
-- url     : https://prove2.me/submissions/49b4058a-3884-4713-895e-0fccd0129387

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_UJ_isUnit
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_UJ_inv_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_UJ_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_exp_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (hσ : IsURepOn (UJset ε) σ) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (hg : g ∈ UJset ε) {v v' : H}
    (hv : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g v)) (σ g v') 0 := by
  have h := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hv
  refine HasDerivAt.congr_of_eventuallyEq h (Filter.Eventually.of_forall fun t => ?_)
  have he := exp_mem (inG_smul t hX)
  have h1 : (t : ℂ) • (g * X * g⁻¹) = g * ((t : ℂ) • X) * g⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have h2 := hσ.1.2 _ (UJ_mul (UJ_mul hg he) (UJ_inv_mem hg)) g hg
  rw [Matrix.mul_assoc _ g⁻¹ g, nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (UJ_isUnit hg)),
    Matrix.mul_one, hσ.1.2 _ hg _ he] at h2
  beta_reduce
  rw [h1, Matrix.exp_conj _ _ (UJ_isUnit hg)]
  exact (congrArg (fun T : H →L[ℂ] H => T v) h2).symm
end GlobalTheory.CompanionTheory.SmoothModule
