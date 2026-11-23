-- Prove2me | solution 1 for GlobalTheory.exists_algEquiv_points
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:12.860715+00:00
-- url     : https://prove2.me/submissions/4847a31b-20a0-48ec-b43b-801428e3fefb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
import Theorems.Thm_GlobalTheory_exists_algEquiv_fin_points

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open Module Algebra
open GlobalTheory
variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field E]
  [Algebra R E] [IsFiniteSplit E (E ⊗[R] S)]
variable {E}
namespace GlobalTheory
theorem _root_.solution {ι : Type*} (P : ι ≃ (S →ₐ[R] E)) :
    ∃ e : E ⊗[R] S ≃ₐ[E] (ι → E), ∀ x j, e (1 ⊗ₜ x) j = P j x := by
  obtain ⟨n, Q, e, he⟩ := exists_algEquiv_fin_points R S E
  refine ⟨e.trans (AlgEquiv.piCongrLeft' E (fun _ ↦ E) (Q.trans P.symm)), fun x j ↦ ?_⟩
  simp [he]
end GlobalTheory
