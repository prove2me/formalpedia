-- Prove2me | solution 1 for GlobalTheory.tensor_quot_maximalIdeal_finite_formallyUnramified
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:15.045892+00:00
-- url     : https://prove2.me/submissions/64bf5690-c03a-4411-b6d4-17aa5fdbfb0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TensorResidueUnramifiedFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [IsLocalRing R] [Algebra A B]
      [Algebra A R], ((IsLocalRing.residue R).comp (algebraMap A R)).Finite →
      ((IsLocalRing.residue R).comp (algebraMap A R)).FormallyUnramified →
      Algebra.FormallyUnramified B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map
        (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) ∧
      Module.Finite B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map
        (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) := by
  intro A B R _ _ _ _ _ _ hfin hfu
  have hf : Module.Finite A (R ⧸ maximalIdeal R) := by
    rw [← RingHom.finite_algebraMap]; exact hfin
  have hu : Algebra.FormallyUnramified A (R ⧸ maximalIdeal R) := by
    rw [← RingHom.formallyUnramified_algebraMap]; exact hfu
  let e := Algebra.TensorProduct.tensorQuotientEquiv (R := A) B R B (maximalIdeal R)
  haveI : Algebra.FormallyUnramified B (B ⊗[A] (R ⧸ maximalIdeal R)) :=
    Algebra.FormallyUnramified.base_change B
  haveI : Module.Finite B (B ⊗[A] (R ⧸ maximalIdeal R)) := Module.Finite.base_change A B _
  exact ⟨Algebra.FormallyUnramified.of_equiv e, Module.Finite.equiv e.toLinearEquiv⟩
end GlobalTheory
