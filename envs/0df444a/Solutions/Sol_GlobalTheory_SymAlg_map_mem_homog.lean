-- Prove2me | solution 1 for GlobalTheory.SymAlg.map_mem_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:13:47.73554+00:00
-- url     : https://prove2.me/submissions/41e2e70e-e800-42f7-97d5-a357b40344f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Theorems.Thm_GlobalTheory_SymAlg_algHom_mem_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open scoped DirectSum
open GlobalTheory
open GlobalTheory.SymAlg
variable {R : Type*} [CommRing R] {M M' M'' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
namespace GlobalTheory.SymAlg
theorem _root_.solution (f : M →ₗ[R] M') {d : ℕ} {x : SymmetricAlgebra R M}
    (hx : x ∈ homog R M d) : map f x ∈ homog R M' d :=
  algHom_mem_pow (map f) _ (fun m => by simp) hx
end GlobalTheory.SymAlg
