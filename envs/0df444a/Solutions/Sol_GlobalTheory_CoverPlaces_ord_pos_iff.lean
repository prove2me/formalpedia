-- Prove2me | solution 1 for GlobalTheory.CoverPlaces.ord_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:23.947083+00:00
-- url     : https://prove2.me/submissions/903dfd9a-9b35-4ae8-bbb7-faa80ea60c2d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsIntegralIffMemSpanOneTmulIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemIntegralClosureOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsPtOrdEqAddValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FdegEqFinrankResidueFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsEquivCoverPointsPlacesBaseChange
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_of_mem
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_eq_zero_iff


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
open GlobalTheory
open GlobalTheory.CoverPlaces
variable {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A]
  [Algebra O A] {ϖ : O}
namespace GlobalTheory.CoverPlaces
theorem _root_.solution (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] (a : As O A) :
    0 < ord ϖ ζ (a : A) ↔ a ∈ ζ.asIdeal := by
  rw [ord_of_mem ζ h a.2, ← not_iff_not, ← vL_eq_zero_iff]
  change ¬ 0 < (vL ζ a).map (Nat.cast : ℕ → ℤ) ↔ _
  generalize vL ζ a = v
  cases v with
  | top => simp
  | coe j =>
    rw [ENat.map_natCast, ← WithTop.coe_zero, WithTop.coe_lt_coe]
    simp
end GlobalTheory.CoverPlaces
