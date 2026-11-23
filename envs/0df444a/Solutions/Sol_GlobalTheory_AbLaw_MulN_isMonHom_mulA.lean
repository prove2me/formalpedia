-- Prove2me | solution 1 for GlobalTheory.AbLaw.MulN.isMonHom_mulA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:26.333119+00:00
-- url     : https://prove2.me/submissions/be06ab79-84b7-42b4-a8bc-38d389d21ed2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.MulN
namespace GlobalTheory.AbLaw.MulN
theorem _root_.solution {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom (mulA A n) := by
  induction n with
  | zero =>
    change IsMonHom (𝟙 A ^ 0)
    rw [pow_zero]
    exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  | succ n ih =>
    change IsMonHom (𝟙 A ^ (n + 1))
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom (lift (mulA A n) (𝟙 A) ≫ μ[A]))
end GlobalTheory.AbLaw.MulN
