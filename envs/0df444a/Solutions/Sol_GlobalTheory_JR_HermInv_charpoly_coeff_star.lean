-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.charpoly_coeff_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:59:48.872508+00:00
-- url     : https://prove2.me/submissions/ae8041ef-ff9a-4483-8f2e-1098ef58cc87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ}
namespace GlobalTheory.JR.HermInv
theorem _root_.solution (A : Matrix (Fin r) (Fin r) E) (hA : IsSelfAdjoint A) (i : ℕ) :
    star (A.charpoly.coeff i) = A.charpoly.coeff i := by
  have hT : A.map (starRingEnd E) = Aᵀ := by
    ext k l
    have := congrFun (congrFun hA l) k
    rw [Matrix.star_apply] at this
    rw [Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply, this]
  calc star (A.charpoly.coeff i) = (A.charpoly.map (starRingEnd E)).coeff i := by
        rw [Polynomial.coeff_map]; rfl
    _ = A.charpoly.coeff i := by rw [← Matrix.charpoly_map, hT, Matrix.charpoly_transpose]
end GlobalTheory.JR.HermInv
