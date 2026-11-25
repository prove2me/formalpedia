-- Prove2me | solution 1 for GlobalTheory.FullFlag.ofBasis_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:45:29.733372+00:00
-- url     : https://prove2.me/submissions/fde2d1c1-cf7b-48ec-91f9-e4e9174313c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub

set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.FullFlag
variable {n : ℕ}
namespace GlobalTheory.FullFlag
theorem _root_.solution {M' : Type*} [AddCommGroup M'] [Module R M'] (b : Basis (Fin n) R M)
    (e : M ≃ₗ[R] M') : ofBasis (b.map e) = (ofBasis b).map e := by
  ext1
  funext k
  simp only [ofBasis_sub, map_sub, Basis.flag, Submodule.map_span, Set.image_image]
  rfl
end GlobalTheory.FullFlag
