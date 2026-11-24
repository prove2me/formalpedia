-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WtLinkPf.tor_mem_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:01:29.691823+00:00
-- url     : https://prove2.me/submissions/b27d9416-0901-474e-bd25-c238d11ea85e

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExpMul
import Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_star_exp_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WtLinkPf
open PI.UpqRep
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.WtLinkPf
theorem _root_.solution (ε : Fin n → Bool) (θ : Fin n → ℝ) : tor θ ∈ Kset ε := by
  show tor θ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ tor θ * PI.UpqRep.Jm ε = PI.UpqRep.Jm ε * tor θ
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    unfold tor
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      show (1 : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun _ => 1) from Matrix.diagonal_one.symm]
    congr 1
    funext a
    rw [Pi.star_apply]
    exact star_exp_mul (θ a)
  · unfold tor PI.UpqRep.Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring
end GlobalTheory.CompanionTheory.WtLinkPf
