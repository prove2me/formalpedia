-- Prove2me | solution 1 for GlobalTheory.MulSplit.IsG.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:12:58.967263+00:00
-- url     : https://prove2.me/submissions/d28b4221-d5a5-45a3-9f9c-0df77d852f98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights
import Theorems.Thm_GlobalTheory_MulSplit_mul_mem_Sg

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
namespace IsG
theorem _root_.solution (hL : L.IsLB) {D E : (Y ⟶ X) →₀ ℤ} {u w : (Vals L p)ˣ} (h : IsG D u) (h' : IsG E w) :
    IsG (D + E) (u * w) :=
  ⟨mul_mem_Sg hL h.1 h'.1 rfl, by rw [mul_inv]; exact mul_mem_Sg hL h.2 h'.2 (neg_add _ _).symm⟩
end IsG
end GlobalTheory.MulSplit
