-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_isAffineOpen_of_finset_smoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2bc2cc72-0c5e-59f4-a760-bd0ec993ae9f

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_IgusaScheme
import Theorems.Thm_ModularCurve_IgusaScheme_exists_chartFinOpen_inf_chartInfOpen_eq_basicOpen_and_mul_eq_one
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_finset_of_twoCharts
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_isAffineOpen_of_finset_smoothLocus
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian"
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve TensorProduct
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

open ModularCurve.DRModelPackageLevel

theorem solution (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN) :
    ∀ (V : (Spec (CommRingCat.of (R q))).affineOpens) (F : Finset ↥𝔓.smoothLocus),
      (∀ x ∈ F, (𝔓.smoothLocus.ι ≫ toBase N₀ q).base x ∈ (V : (Spec (CommRingCat.of (R q))).Opens)) →
      ∃ W : (𝔓.smoothLocus : Scheme.{0}).Opens, IsAffineOpen W ∧
        W ≤ (𝔓.smoothLocus.ι ≫ toBase N₀ q) ⁻¹ᵁ (V : (Spec (CommRingCat.of (R q))).Opens) ∧ ∀ x ∈ F, x ∈ W := by
  intro V F hF
  obtain ⟨f, g, hf, hg, hfg⟩ := ModularCurve.IgusaScheme.exists_chartFinOpen_inf_chartInfOpen_eq_basicOpen_and_mul_eq_one (N₀ * q) q
  have hAF : ∀ G : Finset ↥(X N₀ q), ∃ W : (X N₀ q).Opens, IsAffineOpen W ∧ ∀ x ∈ G, x ∈ W := fun G =>
    AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_finset_of_twoCharts (toBase N₀ q) (chartFinOpen (N₀ * q) q) (chartInfOpen (N₀ * q) q)
      (isAffineOpen_chartFinOpen (N₀ * q) q) (isAffineOpen_chartInfOpen (N₀ * q) q) (igusaCover (N₀ * q) q) f g hf hg hfg G
  exact AlgebraicGeometry.exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset hAF 𝔓.smoothLocus ((toBase N₀ q) ⁻¹ᵁ (V : (Spec (CommRingCat.of (R q))).Opens)) F hF

end S_ModularCurve_DRModelPackageLevel_exists_isAffineOpen_of_finset_smoothLocus
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_isAffineOpen_of_finset_smoothLocus (solution)
