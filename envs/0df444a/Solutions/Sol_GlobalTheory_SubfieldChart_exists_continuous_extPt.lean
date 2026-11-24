-- Prove2me | solution 1 for GlobalTheory.SubfieldChart.exists_continuous_extPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:58:38.954062+00:00
-- url     : https://prove2.me/submissions/616d007e-fad7-4416-b760-3c4edd72ef53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolomorphicChart
import Theorems.Thm_GlobalTheory_SubfieldChart_extPt_tmul

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
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.SubfieldChart
variable {k A : Type} [Field k] [Algebra k ℂ] [CommRing A] [Algebra k A]
namespace GlobalTheory.SubfieldChart
theorem _root_.solution (t : ℂ ⊗[k] A) :
    ∃ F : (A → ℂ) → ℂ, Continuous F ∧ ∀ x : A →ₐ[k] ℂ, F x = extPt x t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨fun _ => 0, continuous_const, fun x => by simp⟩
  | tmul c a => exact ⟨fun u => c * u a, by fun_prop, fun x => (extPt_tmul x c a).symm⟩
  | add s t hs ht =>
    obtain ⟨F, hF, hF'⟩ := hs
    obtain ⟨G, hG, hG'⟩ := ht
    exact ⟨fun u => F u + G u, hF.add hG, fun x => by simp [hF', hG']⟩
end GlobalTheory.SubfieldChart
