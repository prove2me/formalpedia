-- Prove2me | solution 1 for GlobalTheory.fg_int_of_forall_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:49:03.876337+00:00
-- url     : https://prove2.me/submissions/c574f985-e541-4285-961e-6f6dbb9c053d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FgIntOfForallIsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K' : Type) [Field K'] [NumberField K']
    (M : Submodule ℤ K') (hM : ∀ y ∈ M, IsIntegral ℤ y) : M.FG := by
  let f : 𝓞 K' →ₗ[ℤ] K' := (algebraMap (𝓞 K') K').toIntAlgHom.toLinearMap
  have hle : M ≤ LinearMap.range f := fun y hy => ⟨⟨y, hM y hy⟩, rfl⟩
  have hfg : (M.comap f).FG := IsNoetherian.noetherian _
  have hmap := hfg.map f
  rwa [Submodule.map_comap_eq, inf_eq_right.mpr hle] at hmap
end GlobalTheory
