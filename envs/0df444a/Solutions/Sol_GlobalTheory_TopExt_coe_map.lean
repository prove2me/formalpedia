-- Prove2me | solution 1 for GlobalTheory.TopExt.coe_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:32:51.111341+00:00
-- url     : https://prove2.me/submissions/15b82737-aea3-4a87-9b4a-7ce59a82a717

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsDetEquivOfSubsingleton
import Theorems.Thm_GlobalTheory_SymAlg_baseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SymAlg.baseChangeEquiv_tmul



set_option autoImplicit false
open TensorProduct Module Function
open GlobalTheory
open GlobalTheory.TopExt
variable {R F H L : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup L] [Module R L]
namespace GlobalTheory.TopExt
theorem _root_.solution (n : ℕ) (i : F →ₗ[R] H) (x : ⋀[R]^n F) :
    (exteriorPower.map n i x : ExteriorAlgebra R H) =
      ExteriorAlgebra.map i (x : ExteriorAlgebra R F) := by
  have : (⋀[R]^n H).subtype ∘ₗ exteriorPower.map n i =
      (ExteriorAlgebra.map i).toLinearMap ∘ₗ (⋀[R]^n F).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp
  exact LinearMap.congr_fun this x
end GlobalTheory.TopExt
