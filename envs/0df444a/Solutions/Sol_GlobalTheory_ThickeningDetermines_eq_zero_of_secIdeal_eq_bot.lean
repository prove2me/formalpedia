-- Prove2me | solution 1 for GlobalTheory.ThickeningDetermines.eq_zero_of_secIdeal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:29:29.600902+00:00
-- url     : https://prove2.me/submissions/c46edb51-c985-4919-a7b0-5f416d23ffb7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ThickeningDetermines
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData TopologicalSpace
variable {X Y : Scheme.{0}} {N : LB X}
namespace GlobalTheory.ThickeningDetermines
theorem _root_.solution (hN : N.IsLB) (s : N.Sec) (h : secIdeal hN s = ⊥) (j : N.ι) :
    s.f j = 0 := by
  refine X.IsSheaf.section_ext fun x hx ↦ ?_
  obtain ⟨W, hxW, hW⟩ := exists_affine_le (V := N.U j) hx
  refine ⟨W.1, hW, hxW, ?_⟩
  have h1 := ideal_locIdeal _ _ (exists_mem_chart hN) (associated_germ_sec s) W j hW
  have h2 : (secIdeal hN s).ideal W = ⊥ := by rw [h]; rfl
  have h3 := Ideal.span_singleton_eq_bot.1 (h1.symm.trans h2)
  exact h3.trans (map_zero _).symm
end GlobalTheory.ThickeningDetermines
