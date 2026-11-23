-- Prove2me | solution 1 for GlobalTheory.MulSplit.pl_pl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:57.733369+00:00
-- url     : https://prove2.me/submissions/314b7b3c-0a55-4fd1-ab30-52ac54adad17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.MulSplit
variable {X Y B : Scheme.{0}} (L : LB X) (p : Y ⟶ B)
variable {L p}
variable {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.MulSplit
theorem _root_.solution {h h' h'' : Y ⟶ Y} (hh : h ≫ p = p) (hh' : h' ≫ p = p) (hh'' : h'' ≫ p = p) (e : h ≫ h' = h'')
    (v : Vals L p) : pl L h hh (pl L h' hh' v) = pl L h'' hh'' v := by
  subst e
  funext i
  have : ∀ (a b : Y ⟶ Y) (ha hb), a = b → v ⟨(i.1.1, i.1.2.1, a), ha⟩ = v ⟨(i.1.1, i.1.2.1, b), hb⟩ := by
    rintro a b ha hb rfl; rfl
  exact this _ _ _ _ (Category.assoc _ _ _)
end GlobalTheory.MulSplit
