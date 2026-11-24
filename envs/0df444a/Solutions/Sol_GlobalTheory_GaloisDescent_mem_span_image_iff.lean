-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.mem_span_image_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:14:29.05117+00:00
-- url     : https://prove2.me/submissions/f6d0dec5-a956-4afc-a408-0ce2f8d0eb73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul
import Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul_left
import Theorems.Thm_GlobalTheory_GaloisDescent_exists_finsupp_contract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GaloisDescent.contract_smul

set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L V M G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
  [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M] {f : V →ₗ[K] M}
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (hf : IsBaseChange L f) (N : Submodule K V) (x : M) :
    x ∈ Submodule.span L (f '' N) ↔ ∀ l : L →ₗ[K] K, contract hf l x ∈ N := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      intro l
      rw [← one_smul L (f v), contract_smul]
      exact N.smul_mem _ hv
    | zero => simp
    | add x y _ _ hx hy => intro l; rw [map_add]; exact N.add_mem (hx l) (hy l)
    | smul a x _ hx => intro l; rw [contract_smul_left]; exact hx _
  · intro hx
    obtain ⟨c, hc, h⟩ := exists_finsupp_contract hf (Basis.ofVectorSpace K L) x
    rw [h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, by rw [hc]; exact hx _, rfl⟩)
end GlobalTheory.GaloisDescent
