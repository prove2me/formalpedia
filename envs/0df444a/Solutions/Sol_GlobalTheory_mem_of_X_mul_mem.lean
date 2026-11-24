-- Prove2me | solution 1 for GlobalTheory.mem_of_X_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:07.671506+00:00
-- url     : https://prove2.me/submissions/34969254-a5b6-4a66-8bef-ca107a63744a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_mem_map_C_of_X_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {σ : Type*}
namespace GlobalTheory
theorem _root_.solution {S : Set σ} {x : σ} (hx : x ∉ S) (I : Ideal R) {p : MvPolynomial σ R}
    (hp : X x * p ∈ I.map (C : R →+* MvPolynomial σ R) ⊔ Ideal.span (X '' S)) :
    p ∈ I.map (C : R →+* MvPolynomial σ R) ⊔ Ideal.span (X '' S) := by
  rw [← comap_killVars_map_C, Ideal.mem_comap] at hp ⊢
  rw [map_mul, killVars_X_of_notMem hx] at hp
  exact mem_map_C_of_X_mul_mem _ I hp
end GlobalTheory
