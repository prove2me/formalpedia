-- Prove2me | solution 1 for MassDataIdxFrA.intVec_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:37:53.762005+00:00
-- url     : https://prove2.me/submissions/af4d6185-f66f-46f4-96e3-ae54be9e3d24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_CongSpanSingleIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxFrA
variable {F k : Type} [Field F] [Field k] (O : ValuationSubring F) (π : O →+* k) (γ : O)
  {ι : Type} [Fintype ι] [DecidableEq ι]
open Matrix
variable {F : Type} [Field F] (O : ValuationSubring F) (γ : O) {ι : Type} [Fintype ι] [DecidableEq ι]
namespace MassDataIdxFrA
theorem _root_.solution (M : Matrix ι ι F) (hM : ∀ i j, M i j ∈ O) {z : ι → F} (hz : IntVec O z) :
    IntVec O (M *ᵥ z) := by
  intro i
  show (∑ j, M i j * z j) ∈ O
  exact sum_mem fun j _ => mul_mem (hM i j) (hz j)
end MassDataIdxFrA
