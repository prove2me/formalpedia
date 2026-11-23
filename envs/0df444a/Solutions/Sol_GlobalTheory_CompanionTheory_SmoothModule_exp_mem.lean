-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.exp_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:48.585624+00:00
-- url     : https://prove2.me/submissions/931c88fa-3094-4a2a-9bcf-c46bbb882b68

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
theorem _root_.solution {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : NormedSpace.exp X ∈ UJset ε := by
  change (NormedSpace.exp X)ᴴ * Jm ε * NormedSpace.exp X = Jm ε
  have hu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, J_mul_J ε, J_mul_J ε⟩, rfl⟩
  have hinv : (Jm ε)⁻¹ = Jm ε := inv_eq_left_inv (J_mul_J ε)
  have h1 : Xᴴ = Jm ε * (-X) * (Jm ε)⁻¹ := by
    conv_rhs => rw [← inG_iff.1 hX]
    rw [hinv]
    simp only [thetaJ, neg_neg, Matrix.mul_assoc, J_J_mul, J_mul_J, Matrix.mul_one]
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hu, hinv, Matrix.exp_neg, Matrix.mul_assoc _ (Jm ε) (Jm ε),
    J_mul_J, Matrix.mul_one, Matrix.mul_assoc,
    nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp X)), Matrix.mul_one]
end GlobalTheory.CompanionTheory.SmoothModule
