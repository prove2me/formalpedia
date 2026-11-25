-- Prove2me | solution 1 for GlobalTheory.ZJ.charUnit_zero_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:32:10.079186+00:00
-- url     : https://prove2.me/submissions/8a263267-e9f6-40e1-9534-65d00787161a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Theorems.Thm_GlobalTheory_charUnit_val_eq_appTop


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZJ
attribute [instance] Charts.fin Charts.finC
variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
namespace GlobalTheory.ZJ
theorem _root_.solution (S : Scheme.{0}) (X : Type) [AddCommGroup X] : (charUnit S X 0).val = 1 := by
  rw [charUnit_val_eq_appTop, ← AddMonoidAlgebra.one_def, map_one]
  exact map_one _
end GlobalTheory.ZJ
