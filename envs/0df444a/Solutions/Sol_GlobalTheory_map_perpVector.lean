-- Prove2me | solution 1 for GlobalTheory.map_perpVector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:39:58.166413+00:00
-- url     : https://prove2.me/submissions/2649f825-3801-4334-90d1-5cfcd27e7499

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
namespace GlobalTheory
theorem _root_.solution {S N : Type*} [CommRing S] [AddCommGroup N] [Module S N] {ρ : R →+* S}
    (ψ : M →ₛₗ[ρ] N) (ε : ι → Module.Dual R M) (η : ι → Module.Dual S N) (e' : ι → M) (g : M)
    (he : ∀ a a', η a (ψ (e' a')) = ρ (ε a (e' a'))) (hg : ∀ a, η a (ψ g) = ρ (ε a g)) :
    ψ (perpVector ε e' g) = perpVector η (fun a => ψ (e' a)) (ψ g) := by
  have hm : pairingMatrix η (fun a => ψ (e' a)) = ρ.mapMatrix (pairingMatrix ε e') := by
    ext a' a; simp [he]
  simp only [perpVector, map_sub, map_sum, LinearMap.map_smulₛₗ, hm, ← RingHom.map_det,
    ← RingHom.map_adjugate, hg, map_mul]
  simp
end GlobalTheory
