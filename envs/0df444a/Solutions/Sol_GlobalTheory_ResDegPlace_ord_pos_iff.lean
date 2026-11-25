-- Prove2me | solution 1 for GlobalTheory.ResDegPlace.ord_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:12:12.260486+00:00
-- url     : https://prove2.me/submissions/200ad0f1-8e8b-47f1-8d7a-e1c553c333b7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FdegEqFinrankResidueField
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
open GlobalTheory GlobalTheory.ResDegPlace
open IsLocalRing
variable {O A : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A]
  [Algebra O A] {ϖ : O}
namespace GlobalTheory.ResDegPlace
theorem _root_.solution (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] (a : As O A) :
    0 < ord ϖ ζ (a : A) ↔ a ∈ ζ.asIdeal := by
  rw [ord_of_mem ζ h a.2, ← not_not (a := a ∈ ζ.asIdeal), ← vL_eq_zero_iff ζ a]
  change 0 < (vL ζ a).map (Nat.cast : ℕ → ℤ) ↔ _
  generalize vL ζ a = v
  cases v with
  | top => simp
  | coe n =>
    rw [ENat.map_natCast, WithTop.coe_pos]
    simp [Nat.pos_iff_ne_zero]
end GlobalTheory.ResDegPlace
