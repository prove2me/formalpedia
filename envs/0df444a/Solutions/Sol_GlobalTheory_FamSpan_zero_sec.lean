-- Prove2me | solution 1 for GlobalTheory.FamSpan.zero_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:56:55.462939+00:00
-- url     : https://prove2.me/submissions/94f8d096-3c9f-4113-ba8e-ca0e6c3771ea

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
import Theorems.Thm_P2M_GlobalTheory_FamSpan_exists_good__4ec0b6819754
import Theorems.Thm_P2M_GlobalTheory_DegPull_exists_good__8835be56d0ec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_secScal_sval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sec_ext_val


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
theorem _root_.solution {w : LB.Iso L' (L.pull F)} (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (X' ⟶ X')} {φ : K → (X ⟶ X)} {ε : K → ℤ} (π' : Y' ⟶ X')
    {ψ' : K → (Y' ⟶ X')} (g : LB.Sec (LB.LinComb L φ ε)) (hg : ∀ j, g.f j = 0) (g' : LB.Sec (LB.LinComb L' φ' ε))
    (hg' : ∀ (y : Y') J J', Good L y J → Good L' y J' →
      sval g ((𝟙 Y' ≫ π') ≫ F) y J = (fac w φ' ε (𝟙 Y' ≫ π') y J J').val * sval g' (𝟙 Y' ≫ π') y J')
    (G : LB.Sec (LB.LinComb L' ψ' ε)) (hG : GeneratorPullback.SecScal L' ψ' ε G φ' ε g' π' 1) (j) : G.f j = 0 := by
  refine sec_ext_val hL' (s' := DVR.SecOps.secZero) (fun y J' hJ' => ?_) j
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have e := hg' y J J' hJ hJ'
  have z₁ : sval g ((𝟙 Y' ≫ π') ≫ F) y J = 0 := by
    refine (congrArg (gs _ y _) (hg _)).trans ((gs_eq _ y _ (hJ.mem φ _) _).trans ?_)
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  have z₂ : sval (DVR.SecOps.secZero : LB.Sec (LB.LinComb L' ψ' ε)) (𝟙 Y') y J' = 0 := by
    refine (gs_eq _ y _ (hJ'.mem ψ' _) _).trans ?_
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  rw [z₁, secScal_sval hG (𝟙 Y') y hJ'] at e
  rw [z₂]
  exact (Units.mul_right_eq_zero _).1 e.symm
end GlobalTheory.FamSpan
