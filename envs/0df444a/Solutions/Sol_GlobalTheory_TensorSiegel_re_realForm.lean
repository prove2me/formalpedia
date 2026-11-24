-- Prove2me | solution 1 for GlobalTheory.TensorSiegel.re_realForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:27:42.096537+00:00
-- url     : https://prove2.me/submissions/d6e8f0a2-cc77-4ef6-985a-f8fc4d60e112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.PTheta Matrix
open scoped Kronecker
noncomputable section
open GlobalTheory GlobalTheory.TensorSiegel
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.TensorSiegel
theorem _root_.solution (M : Matrix ι ι ℝ) (z w : ι → ℂ) :
    (z ⬝ᵥ (M.map Complex.ofReal) *ᵥ star w).re =
      (fun i => (z i).re) ⬝ᵥ M *ᵥ (fun i => (w i).re) +
        (fun i => (z i).im) ⬝ᵥ M *ᵥ (fun i => (w i).im) := by
  simp [dotProduct, mulVec, Complex.re_sum, Complex.im_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
end GlobalTheory.TensorSiegel
