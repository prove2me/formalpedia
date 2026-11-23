-- Prove2me | solution 1 for GlobalTheory.MulSplit.translT_translPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:58.453995+00:00
-- url     : https://prove2.me/submissions/f783e1a8-f88f-40f6-8ec5-9971f0fdf074

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights
import Theorems.Thm_GlobalTheory_MulSplit_translPt_eq
import Theorems.Thm_P2M_GlobalTheory_MulSplit_translT_fst__b0e4c9370f2b
import Theorems.Thm_P2M_GlobalTheory_MulSplit_translT_snd__7615715b5518

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
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S}
namespace GlobalTheory.MulSplit
theorem _root_.solution (x y : T ⟶ A) : translT A x ≫ translPt A y = translPt A (y * x) := by
  rw [translPt_eq y, MonObj.comp_mul, ← Category.assoc, translT_fst', translT_snd', translPt_eq, translPt_eq,
    MonObj.comp_mul, _root_.mul_assoc]
end GlobalTheory.MulSplit
