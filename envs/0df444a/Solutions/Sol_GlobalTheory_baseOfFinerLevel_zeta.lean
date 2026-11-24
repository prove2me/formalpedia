-- Prove2me | solution 1 for GlobalTheory.baseOfFinerLevel_zeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:23:24.517816+00:00
-- url     : https://prove2.me/submissions/cb5c6b60-6557-41aa-92d5-ef9b9d91a787

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSabMapOfBaseEq
import Theorems.Thm_GlobalTheory_coe_levelFieldIncl
import Theorems.Thm_GlobalTheory_levelFieldIncl_zeta

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : (baseOfFinerLevel h).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, ← levelFieldIncl_zeta, coe_levelFieldIncl]
  exact zeta_eq_pow_div_of_dvd l₂.A_pos h
end GlobalTheory
