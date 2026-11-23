-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.induction_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:53.82982+00:00
-- url     : https://prove2.me/submissions/c1f9aebf-be5a-46aa-997d-63a03bffd2ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L V M G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
  [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M] {f : V →ₗ[K] M}
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (hf : IsBaseChange L f) {p : M → Prop} (x : M) (h0 : p 0)
    (hs : ∀ (a : L) (v : V), p (a • f v)) (ha : ∀ x y, p x → p y → p (x + y)) : p x := by
  obtain ⟨t, rfl⟩ := hf.equiv.surjective x
  induction t with
  | zero => rwa [map_zero]
  | tmul a v => rw [hf.equiv_tmul]; exact hs a v
  | add x y hx hy => rw [map_add]; exact ha _ _ hx hy
end GlobalTheory.GaloisDescent
