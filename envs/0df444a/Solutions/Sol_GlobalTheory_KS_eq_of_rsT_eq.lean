-- Prove2me | solution 1 for GlobalTheory.KS.eq_of_rsT_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:51.432327+00:00
-- url     : https://prove2.me/submissions/8080251c-7a6b-4470-ab58-7e17966413d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Theorems.Thm_GlobalTheory_KS_rsT_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS
variable {Y Z : Scheme.{0}}
namespace GlobalTheory.KS
theorem _root_.solution {J : Type} (V : J → Y.Opens) {O : Y.Opens} (hV : ∀ k, V k ≤ O) (hc : O ≤ iSup V)
    (s t : Γ(Y, O)) (h : ∀ k, rsT s (V k) = rsT t (V k)) : s = t := by
  refine Y.sheaf.eq_of_locally_eq' V O (fun k => homOfLE (hV k)) hc s t fun k => ?_
  have := h k
  rw [rsT_of_le (hV k), rsT_of_le (hV k)] at this
  exact this
end GlobalTheory.KS
