-- Prove2me | solution 1 for GlobalTheory.PointQuot.exists_grpObj_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:27:12.713817+00:00
-- url     : https://prove2.me/submissions/5c560797-d570-4d33-9d69-cfe94e6839ba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientByFiniteGroupOfPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.PointQuot
namespace GlobalTheory.PointQuot
theorem _root_.solution {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] {H A : 𝒞}
    [GrpObj A] (i : H ⟶ A) [Mono i] (e : 𝟙_ 𝒞 ⟶ H) (m : H ⊗ H ⟶ H) (n : H ⟶ H)
    (he : e ≫ i = 1) (hm : m ≫ i = (fst H H ≫ i) * (snd H H ≫ i)) (hn : n ≫ i = i⁻¹) :
    ∃ _ : GrpObj H, IsMonHom i := by
  letI : MonObj H :=
    { one := e
      mul := m
      one_mul := by
        rw [← cancel_mono i, Category.assoc, hm]
        simp [MonObj.comp_mul, he, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono i, Category.assoc, hm]
        simp [MonObj.comp_mul, he, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, hm, _root_.mul_assoc] }
  refine ⟨{ inv := n, left_inv := ?_, right_inv := ?_ }, ⟨?_, ?_⟩⟩
  · change lift n (𝟙 H) ≫ m = toUnit H ≫ e
    rw [← cancel_mono i]
    simp [MonObj.comp_mul, hm, hn, he]
  · change lift (𝟙 H) n ≫ m = toUnit H ≫ e
    rw [← cancel_mono i]
    simp [MonObj.comp_mul, hm, hn, he]
  · change e ≫ i = _
    rw [he, Hom.one_def, toUnit_unit, Category.id_comp]
  · change m ≫ i = _
    rw [hm, Hom.mul_def]
    congr 1
    ext <;> simp
end GlobalTheory.PointQuot
