-- Prove2me | solution 1 for GlobalTheory.LocalQuad.isotropic_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:14.079274+00:00
-- url     : https://prove2.me/submissions/e3ab80a7-ead7-4f44-9ed3-1e8c34b261a4

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuaternaryOfCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
variable {k : Type*} [Field k]
namespace GlobalTheory.LocalQuad
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ → ι)
    (he : Function.Injective e) {a : ι → k}
    (h : ∃ x : κ → k, x ≠ 0 ∧ ∑ j, a (e j) * x j ^ 2 = 0) :
    ∃ x : ι → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  classical
  obtain ⟨x, hx, h⟩ := h
  refine ⟨Function.extend e x 0, fun hc => hx (funext fun j => ?_), ?_⟩
  · simpa [he.extend_apply] using congrFun hc (e j)
  · rw [← h]
    symm
    refine Finset.sum_of_injOn e he.injOn (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_
    · intro i _ hi
      rw [Function.extend_apply' _ _ _ (by simpa using hi)]
      simp
    · intro j _
      rw [he.extend_apply]
end GlobalTheory.LocalQuad
