-- Prove2me | solution 1 for GlobalTheory.KS.exists_rsT_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:53.765927+00:00
-- url     : https://prove2.me/submissions/2b017395-b41c-4d1d-a4ce-78031ebffbdb

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
    (s : ∀ k, Γ(Y, V k)) (h : ∀ k l, rsT (s k) (V k ⊓ V l) = rsT (s l) (V k ⊓ V l)) :
    ∃ t : Γ(Y, O), ∀ k, rsT t (V k) = s k := by
  obtain ⟨t, ht, -⟩ := Y.sheaf.existsUnique_gluing' V O (fun k => homOfLE (hV k)) hc s (fun k l => by
    have := h k l
    rw [rsT_of_le inf_le_left, rsT_of_le inf_le_right] at this
    exact this)
  exact ⟨t, fun k => (rsT_of_le (hV k) _).trans (ht k)⟩
end GlobalTheory.KS
