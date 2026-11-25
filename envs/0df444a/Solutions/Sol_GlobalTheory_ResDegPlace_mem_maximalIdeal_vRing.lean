-- Prove2me | solution 1 for GlobalTheory.ResDegPlace.mem_maximalIdeal_vRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:11:10.160751+00:00
-- url     : https://prove2.me/submissions/451516ff-df30-434b-a630-537d9f4fee8e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FdegEqFinrankResidueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResDegPlace
open IsLocalRing
namespace GlobalTheory.ResDegPlace
theorem _root_.solution {L : Type*} [Field L] (w : AddValuation L (WithTop ℤ))
    (x : vRing w) : x ∈ maximalIdeal (vRing w) ↔ 0 < w (x : L) := by
  have hunit : IsUnit x ↔ w (x : L) = 0 :=
    (Valuation.valuationSubring.integers (w : Valuation L _)).isUnit_iff_valuation_eq_one
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
  exact ⟨fun h => lt_of_le_of_ne x.2 (Ne.symm h), fun h => h.ne'⟩
end GlobalTheory.ResDegPlace
