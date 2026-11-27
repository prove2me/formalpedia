-- Prove2me | solution 1 for GlobalTheory.ZM.cutBy_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:36:58.018473+00:00
-- url     : https://prove2.me/submissions/e275b67f-9583-47b8-9127-81d386f2826f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_ExistsArBaseAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Theorems.Thm_GlobalTheory_ZM_dimDeg_eq_zero_iff

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
open GlobalTheory GlobalTheory.ZM
variable {o : Type} [CommRing o] {S : Scheme.{0}} {g : ℕ} {J : Type}
namespace GlobalTheory.ZM
theorem _root_.solution (K : Type) [Field K] (d : ℕ) :
    CutBy (⊥ : Ideal (MvPolynomial Unit K)) 0 d (fun (_ : Unit) (_ : Unit) => (1 : K)) := by
  intro e _
  refine ⟨?_, fun F _ => by rw [vanIdeal_unit_one]⟩
  rw [(dimDeg_eq_zero_iff _ e).2 (fun F hF _ => Ideal.mem_bot.1 hF)]
  simp
end GlobalTheory.ZM
