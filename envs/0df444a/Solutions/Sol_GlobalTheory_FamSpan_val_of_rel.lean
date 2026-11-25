-- Prove2me | solution 1 for GlobalTheory.FamSpan.val_of_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:31:14.154399+00:00
-- url     : https://prove2.me/submissions/dedc6927-1d58-4c79-a5f8-4b7da6f8fac9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsRepresentativesModNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsBasisOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FamEqOnClassOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIntegralFamiliesSpanPullDegeneration
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


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
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamSpan
variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.FamSpan
theorem _root_.solution {w : LB.Iso L' (L.pull F)} {φ' : K → (X' ⟶ X')} {φ : K → (X ⟶ X)} {ε : K → ℤ}
    (hc : ∀ κ, φ' κ ≫ F = F ≫ φ κ) {s : LB.Sec (LB.LinComb L φ ε)} {a : LB.Sec (LB.LinComb L' φ' ε)}
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ κ, F (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ F) z (LB.wchart L φ p) (s.f p) =
        (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) (a.f q))
    {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    sval s (r ≫ F) z J = (fac w φ' ε r z J J').val * sval a r z J' := by
  rw [sval_of s (r ≫ F) z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc, Category.assoc, hc])]
  exact H Z r z _ _ (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))
end GlobalTheory.FamSpan
