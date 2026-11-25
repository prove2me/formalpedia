-- Prove2me | solution 1 for GlobalTheory.covolume_eq_relIndex_mul_of_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:41.359263+00:00
-- url     : https://prove2.me/submissions/ae73a62a-86e0-4395-8338-4b61029f70a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroForallNormLeOfCovolumeLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module MeasureTheory Metric Set
open scoped Real ENNReal
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
set_option backward.isDefEq.respectTransparency.types false
namespace GlobalTheory
theorem _root_.solution (L' L : Submodule ℤ V) [DiscreteTopology L']
    [IsZLattice ℝ L'] [DiscreteTopology L] [IsZLattice ℝ L] (h : L' ≤ L) :
    ZLattice.covolume L' μ =
      (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L μ := by
  classical
  let b : Basis (Fin (finrank ℝ V)) ℤ L := finBasisOfFinrankEq ℤ L (ZLattice.rank ℝ L)
  let b' : Basis (Fin (finrank ℝ V)) ℤ L' := finBasisOfFinrankEq ℤ L' (ZLattice.rank ℝ L')
  rw [AddSubgroup.relIndex_eq_natAbs_det L'.toAddSubgroup L.toAddSubgroup h b' b,
    Nat.cast_natAbs, Int.cast_abs,
    ZLattice.covolume_eq_det_mul_measureReal L' μ b' (b.ofZLatticeBasis ℝ),
    ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ)]
  congr 2
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  exact (b.ofZLatticeBasis_repr_apply ℝ L ⟨b' j, h (SetLike.coe_mem _)⟩ i)
end GlobalTheory
