-- Prove2me | solution 1 for GlobalTheory.det_pairingMatrix_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:37:58.569352+00:00
-- url     : https://prove2.me/submissions/49829ae2-3eea-4d92-b72e-47d7616b9146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_pairingMatrix_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.pairingMatrix_apply

set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
variable {A : Type*} [CommRing A] [Algebra A R]
namespace GlobalTheory
theorem _root_.solution (ε : ι → Module.Dual R M) (e' : ι → M)
    (he : ∀ a a', ε a (e' a') ∈ (algebraMap A R).range) :
    (pairingMatrix ε e').det ∈ (algebraMap A R).range := by
  choose x hx using he
  have hm : pairingMatrix ε e' = (algebraMap A R).mapMatrix (Matrix.of fun a' a => x a a') := by
    ext a' a; simp [hx]
  exact ⟨(Matrix.of fun a' a => x a a').det, by rw [hm, RingHom.map_det]⟩
end GlobalTheory
