-- Prove2me | solution 1 for GlobalTheory.TopExt.range_pow_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:35:24.828662+00:00
-- url     : https://prove2.me/submissions/e1d158a6-0a94-4ba5-8ba8-eb3cfb135cf7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsDetEquivOfSubsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module Function
open GlobalTheory
open GlobalTheory.TopExt
variable {R F H L : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup L] [Module R L]
namespace GlobalTheory.TopExt
theorem _root_.solution (i : F →ₗ[R] H) (n : ℕ) :
    LinearMap.range (ExteriorAlgebra.ι R ∘ₗ i) ^ n =
      (⋀[R]^n F).map (ExteriorAlgebra.map i).toLinearMap := by
  rw [ExteriorAlgebra.exteriorPower, Submodule.map_pow, ← LinearMap.range_comp,
    ExteriorAlgebra.map_comp_ι]
end GlobalTheory.TopExt
