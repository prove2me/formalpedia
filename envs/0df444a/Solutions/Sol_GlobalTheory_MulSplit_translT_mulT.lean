-- Prove2me | solution 1 for GlobalTheory.MulSplit.translT_mulT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:59:22.703693+00:00
-- url     : https://prove2.me/submissions/31bdcc66-c26e-4c4d-b8e7-b0b5d996a58a

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
import Theorems.Thm_GlobalTheory_MulSplit_mulT_fst
import Theorems.Thm_GlobalTheory_MulSplit_mulT_snd

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
theorem _root_.solution [IsCommMonObj A] (x : T ⟶ A) (n : ℕ) :
    translT A x ≫ mulT A T n = mulT A T n ≫ translT A (x ^ n) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, translT_fst', mulT_fst, translT_fst']
  · rw [Category.assoc, Category.assoc, translT_snd', mulT_snd, MonObj.comp_pow, translT_snd', translPt_eq,
      translPt_eq, MonObj.comp_mul, ← Category.assoc, mulT_fst, mulT_snd, MonObj.comp_pow, mul_pow]
end GlobalTheory.MulSplit
