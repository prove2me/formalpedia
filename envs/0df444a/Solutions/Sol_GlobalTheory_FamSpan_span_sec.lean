-- Prove2me | solution 1 for GlobalTheory.FamSpan.span_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:12:57.956803+00:00
-- url     : https://prove2.me/submissions/3d95d945-c5aa-4140-a505-99d3ddf9e58e

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
import Theorems.Thm_GlobalTheory_FamSpan_fac_congr
import Theorems.Thm_GlobalTheory_FamSpan_exists_up_val
import Theorems.Thm_P2M_GlobalTheory_FamSpan_exists_good__4ec0b6819754
import Theorems.Thm_GlobalTheory_IntegralCoord_gs_appTop
import Theorems.Thm_GlobalTheory_IntegralCoord_lin_of_sval
import Theorems.Thm_P2M_GlobalTheory_DegPull_exists_good__8835be56d0ec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_secScal_sval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_sval_lin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_sval_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
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
    {φ' : K → (X' ⟶ X')} {φ : K → (X ⟶ X)} {ε : K → ℤ} (hc : ∀ κ, φ' κ ≫ F = F ≫ φ κ)
    (π : Y ⟶ X) (π' : Y' ⟶ X') (θ : Y ⟶ Y') (θ' : Y' ⟶ Y) (hθ : θ' ≫ θ = 𝟙 _) (hπ : θ ≫ π' ≫ F = π)
    {ψ' : K → (Y' ⟶ X')} (hψ : ∀ k, ψ' k = π' ≫ φ' k) {m : ℕ} (b g : Fin m → LB.Sec (LB.LinComb L φ ε))
    {C : Type} (κc : C → Γ(Y, ⊤))
    (hb : ∀ s : LB.Sec (LB.LinComb L (fun i => π ≫ φ i) ε), ∃ c : Fin m → C, ∀ j,
      s.f j = ∑ i, resTop (LB.wchart L (fun i => π ≫ φ i) j) (κc (c i)) *
        (show Γ(Y, LB.wchart L (fun i => π ≫ φ i) j) from (DVR.pullSec L φ ε (b i) π).f j))
    (ρ : Fin m → Γ(X, ⊤)) (hg : ∀ i j, (g i).f j = resTop _ (ρ i) * (b i).f j)
    (g' : Fin m → LB.Sec (LB.LinComb L' φ' ε))
    (hg' : ∀ i (y : Y') J J', Good L y J → Good L' y J' →
      sval (g i) ((𝟙 Y' ≫ π') ≫ F) y J = (fac w φ' ε (𝟙 Y' ≫ π') y J J').val * sval (g' i) (𝟙 Y' ≫ π') y J')
    (G : Fin m → LB.Sec (LB.LinComb L' ψ' ε)) (hG : ∀ i, GeneratorPullback.SecScal L' ψ' ε (G i) φ' ε (g' i) π' 1)
    (u : Fin m → Γ(Y', ⊤)) (hu : ∀ i, u i * (π' ≫ F).appTop.hom (ρ i) = 1)
    (s : LB.Sec (LB.LinComb L' ψ' ε)) :
    ∃ c : Fin m → C, ∀ j, s.f j = ∑ i, resTop (LB.wchart L' ψ' j) (θ'.appTop.hom (κc (c i)) * u i) *
      (show Γ(Y', LB.wchart L' ψ' j) from (G i).f j) := by
  obtain ⟨a, ha⟩ := exists_up_val hw hL hL' ψ' ε s θ (fun i => π ≫ φ i) (funext fun k => by
    rw [hψ, Category.assoc, Category.assoc, hc, ← hπ, Category.assoc, Category.assoc])
  obtain ⟨c, hc'⟩ := hb a
  refine ⟨c, IntegralCoord.lin_of_sval hL' _ G fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have e₁ := ha _ θ' y J J' hJ hJ'
  rw [hθ, sval_lin (fun i => κc (c i)) _ hc' θ' y hJ] at e₁
  have hπ' : θ' ≫ π = (𝟙 Y' ≫ π') ≫ F := by rw [← hπ, ← Category.assoc, hθ, Category.assoc]
  have fc : fac w φ' ε (𝟙 Y' ≫ π') y J J' = fac w ψ' ε (𝟙 Y') y J J' :=
    fac_congr w ε (fun k => by rw [hψ, Category.assoc]) y J J'
  refine (Units.mul_right_inj (fac w ψ' ε (𝟙 Y') y J J')).1 (e₁.symm.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e₂ := hg' i y J J' hJ hJ'
  rw [secScal_sval (hG i) (𝟙 Y') y hJ', fc] at e₂
  have e₃ : sval (g i) ((𝟙 Y' ≫ π') ≫ F) y J =
      gs ((𝟙 Y' ≫ π') ≫ F) y ⊤ (ρ i) * sval (b i) ((𝟙 Y' ≫ π') ≫ F) y J := by
    have hm := hJ.mem φ ((𝟙 Y' ≫ π') ≫ F)
    exact (congrArg (gs _ y _) (hg i _)).trans ((gs_mul _ y _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hm _) rfl))
  have e₄ : gs (𝟙 Y') y ⊤ (u i) * gs ((𝟙 Y' ≫ π') ≫ F) y ⊤ (ρ i) = 1 := by
    rw [Category.assoc, ← IntegralCoord.gs_appTop, ← gs_mul _ y ⊤ (by trivial), hu, gs_eq _ y ⊤ (by trivial), map_one,
      map_one]
  rw [sval_pullSec _ _ _ _ _ y hJ, hπ', gs_mul _ y ⊤ (by trivial), IntegralCoord.gs_appTop, Category.id_comp θ',
    mul_left_comm, ← e₂, e₃, _root_.mul_assoc, ← _root_.mul_assoc (gs (𝟙 Y') y ⊤ (u i)), e₄, _root_.one_mul]
end GlobalTheory.FamSpan
