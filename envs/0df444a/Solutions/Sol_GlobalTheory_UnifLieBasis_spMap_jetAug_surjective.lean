-- Prove2me | solution 1 for GlobalTheory.UnifLieBasis.spMap_jetAug_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:48:20.175825+00:00
-- url     : https://prove2.me/submissions/cb0eac7c-a1d6-490f-8d9f-53dcd748d7ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLieBasisOfHolUnif
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow


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
open GlobalTheory GlobalTheory.UnifLieBasis
open TangentOrigin
open ReciprocityTheory.ChartRestriction.G.Chart (JetR jetAug qD rD scaleD IsTan isTan_iff prodPts isLieComb_iff)
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.UnifLieBasis
theorem _root_.solution :
    Function.Surjective (spMap (jetAug ℂ (Fin 2) 1).toRingHom) := by
  intro q
  have : q ∈ Set.range (PrimeSpectrum.comap (jetAug ℂ (Fin 2) 1).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun a => ⟨algebraMap ℂ _ a, (jetAug ℂ (Fin 2) 1).commutes a⟩)]
    intro b hb
    refine q.2.mem_of_pow_mem (1 + 1) ?_
    have h := Ideal.pow_mem_pow (I := RingHom.ker (jetAug ℂ (Fin 2) 1)) hb (1 + 1)
    rw [Chart.ker_jetAug_pow, Ideal.mem_bot] at h
    rw [h]
    exact zero_mem _
  exact this
end GlobalTheory.UnifLieBasis
