-- Prove2me | solution 1 for GlobalTheory.VolFin.tr_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:11:57.606769+00:00
-- url     : https://prove2.me/submissions/4e4d1f75-6291-44f3-bfa2-f39f801f38e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleGlobalSectionsFunctionFieldIff
import Theorems.Thm_GlobalTheory_VolFin_ffMap_gen
import Theorems.Thm_GlobalTheory_VolFin_tr_linComb

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
open GlobalTheory.ZV
open GlobalTheory.AbLaw (rs pw)
noncomputable section
open GlobalTheory GlobalTheory.VolFin
variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
namespace GlobalTheory.VolFin
theorem _root_.solution (N : LB Y) (ψ : X ⟶ Y) (hψ) (J J' : PUnit → N.ι) (h) (h') (k) (k') :
    tr (N.pull ψ) J J' h h' = ffMap ψ hψ (tr N (J ⟨⟩) (J' ⟨⟩) k k') := by
  have h'' : genericPoint X ∈ ψ ⁻¹ᵁ (N.U (J ⟨⟩) ⊓ N.U (J' ⟨⟩)) :=
    ⟨LB.wchart_le N _ J ⟨⟩ h, LB.wchart_le N _ J' ⟨⟩ h'⟩
  rw [tr_linComb N ψ 1 1 rfl J J' h h' h'', pow_one]
  exact (ffMap_gen ψ hψ _ _ _ _).symm
end GlobalTheory.VolFin
