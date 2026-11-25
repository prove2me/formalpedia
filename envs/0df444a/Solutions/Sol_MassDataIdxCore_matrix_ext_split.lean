-- Prove2me | solution 1 for MassDataIdxCore.matrix_ext_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:33.66681+00:00
-- url     : https://prove2.me/submissions/7a665057-5532-44ed-87dc-bb2f0972a82e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_KerBack
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PairMatrixSecondSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]
variable (θ : T ≃ₐ[K] K × K)
namespace MassDataIdxCore
theorem _root_.solution (M N : Matrix n n T) (h1 : M.map (t1 θ) = N.map (t1 θ)) (h2 : M.map (t2 θ) = N.map (t2 θ)) :
    M = N := by
  ext i j
  apply θ.injective
  have e1 := congrFun (congrFun h1 i) j
  have e2 := congrFun (congrFun h2 i) j
  simp only [Matrix.map_apply] at e1 e2
  exact Prod.ext (by simpa [t1] using e1) (by simpa [t2] using e2)
end MassDataIdxCore
