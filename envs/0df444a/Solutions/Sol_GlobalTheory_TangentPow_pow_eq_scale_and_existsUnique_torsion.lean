-- Prove2me | solution 1 for GlobalTheory.TangentPow.pow_eq_scale_and_existsUnique_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:21:12.397234+00:00
-- url     : https://prove2.me/submissions/a4100224-108d-4c6c-a17c-d9f245cbbed6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Theorems.Thm_GlobalTheory_TangentPow_scale_zero_comp
import Theorems.Thm_GlobalTheory_TangentPow_pow_eq_scale_comp
import Theorems.Thm_GlobalTheory_KernelNoTorsion_torsion_hom_ext
import Theorems.Thm_P2M_GlobalTheory_KernelNoTorsion_torsionLift___104fe53c2c33


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.TangentPow
variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]
variable {G : Over (Spec (CommRingCat.of O))} [GrpObj G] {y : specO O (DualNumber R) ⟶ G}
namespace GlobalTheory.TangentPow
theorem _root_.solution :
    ∀ (O : Type) [CommRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] (R : Type)
      [CommRing R] [Algebra O R] (N : ℕ) (y : specO O (DualNumber R) ⟶ G),
      ptMap (TrivSqZeroExt.fstHom O R R) ≫ y = 1 →
      y ^ N = ptMap ((TrivSqZeroExt.map ((N : R) • (LinearMap.id : R →ₗ[R] R))).restrictScalars O)
          ≫ y ∧
        ((N : R) = 0 → ∃! w : specO O (DualNumber R) ⟶ torsion G N, w ≫ torsion.ι G N = y) := by
  intro O _ G _ R _ _ N y hy
  refine ⟨pow_eq_scale_comp hy N, fun hN => ?_⟩
  have h : y ^ N = 1 := by rw [pow_eq_scale_comp hy, hN, scale_zero_comp hy]
  exact ⟨KernelNoTorsion.torsionLift y h, KernelNoTorsion.torsionLift_ι y h, fun w hw =>
    KernelNoTorsion.torsion_hom_ext (hw.trans (KernelNoTorsion.torsionLift_ι y h).symm)⟩
end GlobalTheory.TangentPow
