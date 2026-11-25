-- Prove2me | solution 1 for GlobalTheory.DetPowDegree.C_mem_freeIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:34:43.010329+00:00
-- url     : https://prove2.me/submissions/265839d8-51f1-43b5-bf41-24647f82b971

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetFrobeniusSubPowSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPolynomial
open GlobalTheory GlobalTheory.DetPowDegree
variable {α : Type} [Fintype α]
variable {l : ℤ} {L E : ℕ}
namespace GlobalTheory.DetPowDegree
theorem _root_.solution : (MvPolynomial.C l : MvPolynomial (α ⊕ α) ℤ) ∈ freeIdeal α l := by
  classical
  intro m _
  rw [coeff_C]
  split_ifs <;> simp
end GlobalTheory.DetPowDegree
