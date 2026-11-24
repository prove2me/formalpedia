-- Prove2me | solution 1 for GlobalTheory.ZV.vAmp_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:46.737677+00:00
-- url     : https://prove2.me/submissions/2be4b3e4-4fb6-4bb6-8031-577b913e38b5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Theorems.Thm_GlobalTheory_ZV_VAmp_comp_surjective

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
theorem _root_.solution (p : X ⟶ Sp K) (M : LB X) {σ τ : Type} (th : σ → M.Sec) (e : τ ≃ σ) :
    VAmp p M (fun i => th (e i)) ↔ VAmp p M th :=
  ⟨fun h => by simpa only [Equiv.apply_symm_apply] using h.comp_surjective e.symm.surjective,
    fun h => h.comp_surjective e.surjective⟩
end GlobalTheory.ZV
