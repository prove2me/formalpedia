-- Prove2me | solution 1 for GlobalTheory.ZM.projRep_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:10.976274+00:00
-- url     : https://prove2.me/submissions/e59f54be-7bdf-48af-b855-a279cc92350c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_ExistsArBaseAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf

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
theorem _root_.solution (R : Type) [CommRing R] :
    ProjRep (⊥ : Ideal (MvPolynomial Unit R)) (𝟙 (Sp R)) (Out.Inh.trivLB _) (fun _ => OnePoint.unitSec _) := by
  have key : ∀ {R' : Type} [CommRing R'] (v : Unit → R'), Ideal.span (Set.range v) = ⊤ ↔ IsUnit (v ()) := by
    intro R' _ v
    rw [Set.range_unique, Ideal.span_singleton_eq_top]
  refine ⟨Out.Inh.trivLB_isLB _, fun R' _ β x v _ h => ⟨(key v).2 ((OnePoint.secCoord_one x v).1 h), fun F hF => by
    rw [Ideal.mem_bot.1 hF, MvPolynomial.eval₂_zero]⟩, fun R' _ β v hv _ =>
    ⟨spMap β, ⟨by simp, (OnePoint.secCoord_one _ v).2 ((key v).1 hv)⟩, fun y hy => by simpa using hy.1⟩⟩
end GlobalTheory.ZM
