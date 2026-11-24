-- Prove2me | solution 1 for GlobalTheory.IntertwineAeval.intertwine_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:08:38.52908+00:00
-- url     : https://prove2.me/submissions/1230809f-a049-4a45-aaad-cc31e39b9424

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntertwineAeval
import Theorems.Thm_GlobalTheory_IntertwineAeval_intertwine_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntertwineAeval
namespace GlobalTheory.IntertwineAeval
theorem _root_.solution {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (r : M →ₗ[ℂ] N) {T : Module.End ℂ M} {T' : Module.End ℂ N}
    (h : ∀ v : M, r (T v) = T' (r v)) (p : Polynomial ℂ) (v : M) :
    r (Polynomial.aeval T p v) = Polynomial.aeval T' p (r v) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul, intertwine_pow r h]
end GlobalTheory.IntertwineAeval
