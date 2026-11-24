-- Prove2me | solution 1 for GlobalTheory.ZV.vAmp_iff_veryAmpleBy_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:41:28.243311+00:00
-- url     : https://prove2.me/submissions/825ee743-fa1a-4441-8c84-9090d07e27ec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Theorems.Thm_GlobalTheory_ZV_vAmp_iff_veryAmpleBy
import Theorems.Thm_GlobalTheory_ZV_vAmp_comp_equiv

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
open GlobalTheory GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}
namespace GlobalTheory.ZV
theorem _root_.solution (p : X ⟶ Sp K) (M : LB X) {σ : Type} (th : σ → M.Sec) {m : ℕ}
    (e : Fin (m + 1) ≃ σ) : VAmp p M th ↔ AbLaw.VeryAmpleBy p M (fun i => th (e i)) :=
  (vAmp_comp_equiv p M th e).symm.trans (vAmp_iff_veryAmpleBy p M _)
end GlobalTheory.ZV
