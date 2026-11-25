-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeDeriv.dR_wedge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:01:28.108156+00:00
-- url     : https://prove2.me/submissions/600d4682-542f-4038-92a6-4ae0f3a068f7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorDifferentialMatrixUnitFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeDeriv_hasDerivAt_det
import Theorems.Thm_PI_ComplexConjugateDerivative_exp_entry


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeDeriv
namespace GlobalTheory.CompanionTheory.WedgeDeriv
theorem _root_.solution (k r m : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (J J' : Sub (2 * r + k + 1) m) :
    (wedge k r m).dR X J J' = ∑ j, ∑ i, adjugate ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).submatrix (J.1.orderEmbOfFin J.2)
      (J'.1.orderEmbOfFin J'.2)) j i * X (J.1.orderEmbOfFin J.2 i) (J'.1.orderEmbOfFin J'.2 j) := by
  have h := hasDerivAt_det (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)).submatrix (J.1.orderEmbOfFin J.2)
      (J'.1.orderEmbOfFin J'.2)) (X.submatrix (J.1.orderEmbOfFin J.2) (J'.1.orderEmbOfFin J'.2))
      fun i j => PI.ComplexConjugateDerivative.exp_entry X _ _
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, submatrix_apply] at h
  exact h.deriv
end GlobalTheory.CompanionTheory.WedgeDeriv
