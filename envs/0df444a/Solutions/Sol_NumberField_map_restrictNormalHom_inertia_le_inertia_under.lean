-- Prove2me | solution 1 for NumberField.map_restrictNormalHom_inertia_le_inertia_under
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/62a00f2f-acf2-5633-8b24-1418cf4c800e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_map_restrictNormalHom_inertia_le_inertia_under
set_option autoImplicit false
p2m_open "NumberField P2MW.S_NumberField_map_restrictNormalHom_inertia_le_inertia_under.NumberField IsDedekindDomain"

namespace NumberField
p2m_export "NumberField" "place RingOfIntegers RingOfIntegers.coe_injective"
namespace InertiaRes
p2m_open "NumberField"

theorem algebraMap_ringOfIntegers_smul_restrictNormalHom
    (E L F : Type*) [Field E] [Field L] [Field F]
    [Algebra E L] [Algebra E F] [Algebra L F] [IsScalarTower E L F] [Normal E L]
    (φ : F ≃ₐ[E] F) (x : 𝓞 L) :
    algebraMap (𝓞 L) (𝓞 F) (AlgEquiv.restrictNormalHom L φ • x) = φ • algebraMap (𝓞 L) (𝓞 F) x := by
  apply RingOfIntegers.coe_injective
  change algebraMap L F ((AlgEquiv.restrictNormalHom L φ) (x : L)) = φ (algebraMap L F (x : L))
  exact AlgEquiv.restrictNormal_commutes φ L x

end NumberField.InertiaRes

open NumberField.InertiaRes in

theorem solution
    (E L F : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F] [IsGalois E F] [Normal E L]
    (w : HeightOneSpectrum (𝓞 F)) :
    (w.asIdeal.inertia (F ≃ₐ[E] F)).map (AlgEquiv.restrictNormalHom L)
      ≤ (w.under (𝓞 L)).asIdeal.inertia (L ≃ₐ[E] L) := by
  rintro τ ⟨σ, hσ, rfl⟩ x
  show AlgEquiv.restrictNormalHom L σ • x - x ∈ w.asIdeal.under (𝓞 L)
  rw [Ideal.under_def, Ideal.mem_comap, map_sub, algebraMap_ringOfIntegers_smul_restrictNormalHom E L F]
  exact hσ _

end S_NumberField_map_restrictNormalHom_inertia_le_inertia_under
end P2MW
export P2MW.S_NumberField_map_restrictNormalHom_inertia_le_inertia_under (solution)
