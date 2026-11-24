-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.span_image_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:25:01.986299+00:00
-- url     : https://prove2.me/submissions/03bb8c8f-747e-4ef4-9e51-ffa7766f3e03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Theorems.Thm_GlobalTheory_GaloisDescent_span_rational_eq
import Theorems.Thm_GlobalTheory_GaloisDescent_mem_range_of_repr_mem_range

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
theorem _root_.solution (hf : IsBaseChange L f) (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (φ : G → M →+ M) (hφ : ∀ g a v, φ g (a • f v) = s g a • f v)
    (W : Submodule L M) (hW : ∀ g, ∀ w ∈ W, φ g w ∈ W) :
    Submodule.span L (f '' (W.restrictScalars K).comap f) = W := by
  let b := Basis.ofVectorSpace K V
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact hv
  · conv_lhs => rw [← span_rational_eq s hs (hf.basis b) φ
      (fun g a i => by rw [hf.basis_apply, hφ]) W hW]
    refine Submodule.span_mono fun u hu => ?_
    obtain ⟨v, rfl⟩ := mem_range_of_repr_mem_range hf b u hu.2
    exact ⟨v, hu.1, rfl⟩
end GlobalTheory.GaloisDescent
