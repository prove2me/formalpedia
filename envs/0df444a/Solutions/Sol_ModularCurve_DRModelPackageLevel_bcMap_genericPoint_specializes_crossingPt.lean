-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.bcMap_genericPoint_specializes_crossingPt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/9245c7da-9716-538e-b9e5-c93d0348cb62

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_crossingPt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] (ρO : DRLevel.R q →+* O)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1))) :
    𝔛.ξinf ρO toκ ⤳ 𝔛.crossingPt ρO toκ n ∧ 𝔛.ξzero ρO toκ ⤳ 𝔛.crossingPt ρO toκ n := by
  haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  have h0 : 𝔛.crossingPt ρO toκ n = (𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base
      ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n) :=
    Scheme.Hom.comp_apply _ _ _
  have h1 : 𝔛.crossingPt ρO toκ n = (𝔛.comp κ (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base
      ((pullback.snd (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n) := by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition_assoc]
  constructor
  · rw [h0]
    exact (genericPoint_specializes _).map (Scheme.Hom.continuous _)
  · rw [h1]
    exact (genericPoint_specializes _).map (Scheme.Hom.continuous _)

end S_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_crossingPt
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_crossingPt (solution)
