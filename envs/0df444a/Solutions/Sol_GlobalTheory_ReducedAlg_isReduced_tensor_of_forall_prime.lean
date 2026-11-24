-- Prove2me | solution 1 for GlobalTheory.ReducedAlg.isReduced_tensor_of_forall_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:16:46.981314+00:00
-- url     : https://prove2.me/submissions/23919a4e-77db-450a-9f1c-84c7d4ff161a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Theorems.Thm_GlobalTheory_ReducedAlg_eq_zero_of_forall_lTensor_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.ReducedAlg
namespace GlobalTheory.ReducedAlg
theorem _root_.solution {k : Type*} [Field k] (C A : Type*) [CommRing C]
    [Algebra k C] [CommRing A] [Algebra k A] [IsReduced A]
    (h : ∀ (p : Ideal A) [p.IsPrime], IsReduced (C ⊗[k] (A ⧸ p))) : IsReduced (C ⊗[k] A) := by
  classical
  refine ⟨fun x hx => ?_⟩
  refine eq_zero_of_forall_lTensor_eq_zero
    (fun p : {p : Ideal A // p.IsPrime} => (Ideal.Quotient.mkₐ k p.1).toLinearMap) ?_ x ?_
  · intro a ha
    have hmem : a ∈ nilradical A := by
      rw [nilradical_eq_sInf, Submodule.mem_sInf]
      intro J hJ
      have h1 := ha ⟨J, hJ⟩
      simpa [Ideal.Quotient.eq_zero_iff_mem] using h1
    exact IsReduced.eq_zero a (mem_nilradical.1 hmem)
  · intro p
    have := p.2
    have := h p.1
    have hF : ∀ w : C ⊗[k] A,
        Algebra.TensorProduct.map (AlgHom.id k C) (Ideal.Quotient.mkₐ k p.1) w =
          (Ideal.Quotient.mkₐ k p.1).toLinearMap.lTensor C w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul c a => simp
      | add u v hu hv => rw [map_add, map_add, hu, hv]
    rw [← hF]
    exact IsReduced.eq_zero _
      (hx.map (Algebra.TensorProduct.map (AlgHom.id k C) (Ideal.Quotient.mkₐ k p.1)))
end GlobalTheory.ReducedAlg
