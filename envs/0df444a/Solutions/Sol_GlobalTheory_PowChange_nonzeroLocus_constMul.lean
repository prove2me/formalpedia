-- Prove2me | solution 1 for GlobalTheory.PowChange.nonzeroLocus_constMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:28:23.698226+00:00
-- url     : https://prove2.me/submissions/81366ccb-be23-4617-a090-b510c4ccbc00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieCombIffProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NonzeroLocusConstMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PowChange
open GlobalTheory.PowLie
variable {R : Type} [CommRing R]
namespace GlobalTheory.PowChange
theorem _root_.solution {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} {a : R} (ha : IsUnit a) (s : L.Sec) :
    Out.nonzeroLocus (constMul q a s) = Out.nonzeroLocus s := by
  refine iSup_congr fun i => ?_
  have h : IsUnit (constFn q (L.U i) a) := (ha.map _).map _
  change X.basicOpen (constFn q _ a * s.f i) = _
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ h]
  exact inf_eq_right.2 (X.basicOpen_le _)
end GlobalTheory.PowChange
