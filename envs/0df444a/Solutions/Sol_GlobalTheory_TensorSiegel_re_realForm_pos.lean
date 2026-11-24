-- Prove2me | solution 1 for GlobalTheory.TensorSiegel.re_realForm_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:46:09.985417+00:00
-- url     : https://prove2.me/submissions/7df09063-1928-40d5-b283-d61cac976aee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd
import Theorems.Thm_GlobalTheory_TensorSiegel_re_realForm

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
theorem _root_.solution {M : Matrix ι ι ℝ} (hM : M.PosDef) {z : ι → ℂ} (hz : z ≠ 0) :
    0 < (z ⬝ᵥ (M.map Complex.ofReal) *ᵥ star z).re := by
  rw [re_realForm]
  have h1 := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => (z i).re)
  have h2 := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => (z i).im)
  rw [star_trivial] at h1 h2
  by_cases hr : (fun i => (z i).re) = 0
  · have hi : (fun i => (z i).im) ≠ 0 := fun hi =>
      hz (funext fun i => Complex.ext (congrFun hr i) (congrFun hi i))
    have := hM.dotProduct_mulVec_pos hi
    rw [star_trivial] at this
    linarith
  · have := hM.dotProduct_mulVec_pos hr
    rw [star_trivial] at this
    linarith
end GlobalTheory.TensorSiegel
