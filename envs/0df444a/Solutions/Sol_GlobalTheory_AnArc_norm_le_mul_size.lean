-- Prove2me | solution 1 for GlobalTheory.AnArc.norm_le_mul_size
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:45.392239+00:00
-- url     : https://prove2.me/submissions/163878cb-894a-4538-8446-b09f05f943a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution {E : Type*} [SeminormedAddCommGroup E] (f : A.X →+ E) {C : ℝ}
    (hC : ∀ i, ‖f (Module.Free.chooseBasis ℤ A.X i)‖ ≤ C) (μ : A.X) : ‖f μ‖ ≤ C * A.size μ := by
  conv_lhs => rw [← (Module.Free.chooseBasis ℤ A.X).sum_repr μ, map_sum]
  rw [size, Finset.mul_sum]
  refine norm_sum_le_of_le _ fun i _ => ?_
  rw [map_zsmul]
  refine (norm_zsmul_le _ _).trans ?_
  rw [mul_comm, Int.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hC i) (abs_nonneg _)
end GlobalTheory.AnArc
