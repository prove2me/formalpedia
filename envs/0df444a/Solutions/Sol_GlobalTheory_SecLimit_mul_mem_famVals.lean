-- Prove2me | solution 1 for GlobalTheory.SecLimit.mul_mem_famVals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:23:38.849806+00:00
-- url     : https://prove2.me/submissions/871cdeef-8e13-48e9-ba6c-e1b823ca6627

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueLimit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueTwistedSectionOfCompatibleLevels
import Theorems.Thm_GlobalTheory_SecLimit_mul_mem_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_toUnit_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.SecLimit
variable {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (k : ℕ) (α : D.X)
variable {D k α}
namespace GlobalTheory.SecLimit
theorem _root_.solution (u : LB.Gen (LB.LinComb D.P.L (ptφ D α) ![-1, 1])) (hu : u.IsGen)
    (T : Over (Spec (CommRingCat.of V))) {Y : Scheme.{0}} (h : Y ⟶ (T ⊗ D.P.A).left) {π : Y ⟶ D.P.A.left}
    (hπ : h ≫ (snd T D.P.A).left = π) (w : Vals D.P.L Y) :
    w * evU (LB.pullGen D.P.L _ _ u (π ≫ D.P.A.hom)) ∈ famVals D k α π ↔
      w ∈ secVals D.P.L (fun j => h ≫ twφ D α T j) ![(k : ℤ) - 1, 1] := by
  have hZ : h ≫ (T ⊗ D.P.A).hom = π ≫ D.P.A.hom := by
    rw [← Over.w (snd T D.P.A), ← Category.assoc, hπ]
  let Z : Over (Spec (CommRingCat.of V)) := Over.mk (π ≫ D.P.A.hom)
  let hO : Z ⟶ T ⊗ D.P.A := Over.homMk h hZ
  let πO : Z ⟶ D.P.A := Over.homMk π
  have h1 : hO ≫ snd T D.P.A = πO := by
    ext
    simpa [hO, πO] using hπ
  have e1 : hO ≫ translPt D.P.A (toUnit T ≫ D.c α) = πO ≫ padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c α) := by
    unfold translPt padd
    simp only [comp_lift_assoc, comp_toUnit_assoc, h1, Category.comp_id]
    exact mul_comm (toUnit Z ≫ D.c α) πO
  have hmor : h ≫ (translPt D.P.A (toUnit T ≫ D.c α)).left =
      π ≫ (padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c α)).left := by
    have e2 := congrArg Over.Hom.left e1
    simpa [hO, πO] using e2
  refine mul_mem_iff D.P.isLB _ (DVR.pullGen_isGen _ _ _ u hu _) ?_ w
  intro U _ g
  have hπ' : h ≫ pullback.snd T.hom D.P.A.hom = π := hπ
  simp [Fintype.prod_sum_type, Fin.prod_univ_four, twφ, ptφ, DegPre.famφB, DegPre.famε, hmor, hπ',
    Over.toUnit_left]
  exact (mul_assoc _ _ _).symm
end GlobalTheory.SecLimit
