-- Prove2me | solution 1 for GlobalTheory.FamSpan.exists_up_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:57:30.0183+00:00
-- url     : https://prove2.me/submissions/385a95bb-eb64-4263-b3da-bb68304571dd

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
import Theorems.Thm_GlobalTheory_FamSpan_exists_up_sec
import Theorems.Thm_GlobalTheory_TwistLoc_exists_up_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_sval_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_pullSec


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
theorem _root_.solution {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L' φ' ε)) (θ : Y ⟶ Y') (φ : K → (Y ⟶ X))
    (hφ : φ = fun k => (θ ≫ φ' k) ≫ F) :
    ∃ a : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good L' z J' →
      sval a r z J = (fac w φ' ε (r ≫ θ) z J J').val * sval s (r ≫ θ) z J' := by
  subst hφ
  obtain ⟨a, ha⟩ := exists_up_sec hw hL hL' (fun k => θ ≫ φ' k) ε (DVR.pullSec L' φ' ε s θ)
  refine ⟨a, fun Z r z J J' hJ hJ' => ?_⟩
  rw [← sval_pullSec φ' ε s θ r z hJ']
  refine (ha Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
  simp only [pw, fac, Category.assoc]
end GlobalTheory.FamSpan
