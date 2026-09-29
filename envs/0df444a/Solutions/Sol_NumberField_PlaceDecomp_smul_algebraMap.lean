-- Prove2me | solution 1 for NumberField.PlaceDecomp.smul_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/feecc993-8693-507d-9deb-ddfd622f56cd

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_smul_algebraMap

set_option autoImplicit false
open scoped NumberField.PlaceDecomp

theorem solution (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (σ : NumberField.PlaceDecomp.decomp E K w) (x : K) :
    σ • algebraMap K (w.adicCompletion K) x = algebraMap K (w.adicCompletion K) ((σ : K ≃ₐ[E] K) x) := by
  rw [NumberField.PlaceDecomp.smul_def, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply, WithVal.equiv_symm_apply]
  rw [NumberField.PlaceDecomp.actRingEquiv_coe, WithVal.congr_apply]
  rfl

end S_NumberField_PlaceDecomp_smul_algebraMap
end P2MW
export P2MW.S_NumberField_PlaceDecomp_smul_algebraMap (solution)
