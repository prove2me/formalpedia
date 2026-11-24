-- Prove2me | solution 1 for GlobalTheory.MulSplit.IsG.equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:12:58.359254+00:00
-- url     : https://prove2.me/submissions/301e2a8a-aade-4a29-a9f8-189afc03d208

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
theorem _root_.solution (hL : L.IsLB) {D E F : (Y ⟶ X) →₀ ℤ} {u : (Vals L p)ˣ} (hu : IsG D u) (h : E + D = F) :
    Nonempty (Sg L p E ≃ₗ[Γ(B, ⊤)] Sg L p F) :=
  ⟨{ toFun := fun v => ⟨v.1 * u.val, mul_mem_Sg hL v.2 hu.1 h⟩
     invFun := fun v => ⟨v.1 * (u⁻¹).val, mul_mem_Sg hL v.2 hu.2 (by rw [← h]; abel)⟩
     map_add' := fun _ _ => Subtype.ext (add_mul _ _ _)
     map_smul' := fun _ _ => Subtype.ext (smul_mul_assoc _ _ _)
     left_inv := fun _ => Subtype.ext (Units.mul_inv_cancel_right _ _)
     right_inv := fun _ => Subtype.ext (Units.inv_mul_cancel_right _ _) }⟩
end IsG
end GlobalTheory.MulSplit
