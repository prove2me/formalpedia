-- Prove2me | solution 1 for GlobalTheory.exists_algEquiv_fin_points
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:31.937718+00:00
-- url     : https://prove2.me/submissions/73842088-7a5c-4bf7-8b6b-caa0a750c372

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe

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
variable (R S)
namespace GlobalTheory
theorem _root_.solution :
    ∃ (n : ℕ) (P : Fin n ≃ (S →ₐ[R] E)) (e : E ⊗[R] S ≃ₐ[E] (Fin n → E)),
      ∀ x j, e (1 ⊗ₜ x) j = P j x := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := IsFiniteSplit.nonempty_algEquiv_fun E (E ⊗[R] S)
  let f : Fin n → (E ⊗[R] S →ₐ[E] E) := fun j ↦
    (Pi.evalAlgHom E (fun _ ↦ E) j).comp e.toAlgHom
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      by_contra h
      have := AlgHom.congr_fun hij (e.symm (Pi.single i 1))
      simp [f, Ne.symm h] at this
    · intro g
      obtain ⟨j, hj⟩ := AlgHom.eq_piEvalAlgHom (g.comp e.symm.toAlgHom)
      refine ⟨j, AlgHom.ext fun x ↦ ?_⟩
      simpa [f] using (AlgHom.congr_fun hj (e x)).symm
  exact ⟨n, (Equiv.ofBijective f hf).trans (AlgHom.liftEquiv R E S E).symm, e, fun x j ↦ rfl⟩
end GlobalTheory
