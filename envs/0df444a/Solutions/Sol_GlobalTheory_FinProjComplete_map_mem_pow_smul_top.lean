-- Prove2me | solution 1 for GlobalTheory.FinProjComplete.map_mem_pow_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:06:25.365508+00:00
-- url     : https://prove2.me/submissions/57b93599-bf6d-4227-ab54-1f9cd8d0a137

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinProjComplete
namespace GlobalTheory.FinProjComplete
theorem _root_.solution {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (f : M →ₗ[R] N) {x y : M} {n : ℕ}
    (h : x ≡ y [SMOD (J ^ n • ⊤ : Submodule R M)]) :
    f x ≡ f y [SMOD (J ^ n • ⊤ : Submodule R N)] := by
  rw [SModEq.sub_mem] at h ⊢
  have := Submodule.mem_map_of_mem (f := f) h
  rw [Submodule.map_smul'', map_sub] at this
  exact Submodule.smul_mono le_rfl le_top this
end GlobalTheory.FinProjComplete
