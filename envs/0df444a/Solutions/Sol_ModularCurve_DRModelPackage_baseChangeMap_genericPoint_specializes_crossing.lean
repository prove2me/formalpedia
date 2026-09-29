-- Prove2me | solution 1 for ModularCurve.DRModelPackage.baseChangeMap_genericPoint_specializes_crossing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/332fe67e-8ded-5ea8-8a6f-c1c38f775dfb

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_specializes_crossing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ))) :
    (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳
        (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base n ∧
    (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳
        (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base n := by
  constructor
  · exact (genericPoint_specializes ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n)).map
      (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base.hom.continuous
  · have h : (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base n =
        (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n) := by
      change ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ) ≫ DRModel.baseChangeMap toκ).base n =
        ((pullback.snd (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compZero κ) ≫ DRModel.baseChangeMap toκ).base n
      rw [pullback.condition]
    rw [h]
    exact (genericPoint_specializes ((pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n)).map
      (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base.hom.continuous

end S_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_specializes_crossing
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_specializes_crossing (solution)
