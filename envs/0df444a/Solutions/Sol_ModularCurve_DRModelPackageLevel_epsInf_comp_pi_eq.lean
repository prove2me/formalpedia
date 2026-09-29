-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.epsInf_comp_pi_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a3dd17f2-e23a-57b5-9949-132131ec2188

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_epsInf_comp_pi_eq
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

theorem solution (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (φinf : ↥(IgusaScheme.chartAlgInf N₀ q) →ₐ[DRLevel.R q] DRLevel.R q)
    (hφinf : ∀ x : ↥(IgusaScheme.chartAlgInf N₀ q),
      ((φinf x : DRLevel.R q) : ℚ) = ((x : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ).coeff 0)
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (DRLevel.R q)))) (DRLevel.toBase0 N₀ q))
    (hε₀ : ε₀.1 = Spec.map (CommRingCat.ofHom φinf.toRingHom) ≫ IgusaScheme.ιInf N₀ q) :
    𝔓.εinf.1 ≫ 𝔓.π.1 = ε₀.1 := by

  have h2 : 𝔓.rhoInf.toRingHom.comp 𝔓.iotaInf.toRingHom = φinf.toRingHom := by
    refine RingHom.ext fun x => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    apply Subtype.ext
    rw [𝔓.rhoInf_spec (𝔓.iotaInf x), 𝔓.iotaInf_spec x, hφinf x]

  rw [𝔓.εinf_chart, Category.assoc, 𝔓.pi_chartInf, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h2, hε₀]

end S_ModularCurve_DRModelPackageLevel_epsInf_comp_pi_eq
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_epsInf_comp_pi_eq (solution)
