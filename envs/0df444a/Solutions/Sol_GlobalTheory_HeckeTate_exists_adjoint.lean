-- Prove2me | solution 1 for GlobalTheory.HeckeTate.exists_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:19:09.142854+00:00
-- url     : https://prove2.me/submissions/75152ecd-3c6d-4c55-b61b-6ab91c1c9672

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_skew
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_adj
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_bij
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HeckeTate
variable {R : Type} [CommRing R] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
variable {σ : R ≃+* R} {B : M →+ M →+ ℤ} {B' : M' →+ M' →+ ℤ}
namespace GlobalTheory.HeckeTate
theorem _root_.solution (h : IsUnimod σ B) (h' : IsUnimod σ B') (hσ : ∀ a, σ (σ a) = a) (u : M →ₗ[R] M') :
    ∃ v : M' →ₗ[R] M, ∀ a y, B' (u a) y = B a (v y) := by
  choose v hv using fun y => h.bij.2 ((B' y).comp u.toAddMonoidHom)
  have hv' : ∀ a y, B' (u a) y = B a (v y) := fun a y => by
    rw [h.skew a, hv, h'.skew]; rfl
  refine ⟨⟨⟨v, fun x y => h.ext fun a => ?_⟩, fun r y => h.ext fun a => ?_⟩, hv'⟩
  · rw [map_add, ← hv', ← hv', ← hv', map_add]
  · simp only [RingHom.id_apply]
    rw [← hv', ← hσ r, ← h'.adj, ← h.adj, ← hv', map_smul u]
end GlobalTheory.HeckeTate
