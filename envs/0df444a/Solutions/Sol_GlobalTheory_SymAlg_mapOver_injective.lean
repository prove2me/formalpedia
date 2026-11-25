-- Prove2me | solution 1 for GlobalTheory.SymAlg.mapOver_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:20:45.861318+00:00
-- url     : https://prove2.me/submissions/02fa855e-449a-4471-a1e6-06548bacb06b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Theorems.Thm_GlobalTheory_SymAlg_baseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SymAlg.baseChangeEquiv_tmul

set_option autoImplicit false
open TensorProduct Module
open scoped DirectSum
open GlobalTheory
open GlobalTheory.SymAlg
variable {R : Type*} [CommRing R] {M M' M'' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
variable {S : Type*} [CommRing S] [Algebra R S] {W : Type*} [AddCommGroup W] [Module R W]
  [Module S W] [IsScalarTower R S W]
namespace GlobalTheory.SymAlg
theorem _root_.solution [Module.Projective R M] {j : M →ₗ[R] W} (h : IsBaseChange S j)
    (hS : Function.Injective (algebraMap R S)) : Function.Injective (mapOver S j) := by
  have h1 : Function.Injective (Algebra.TensorProduct.includeRight :
      SymmetricAlgebra R M →ₐ[R] S ⊗[R] SymmetricAlgebra R M) :=
    Algebra.TensorProduct.includeRight_injective hS
  intro x y hxy
  apply h1
  apply (baseChangeEquiv h).injective
  simpa using hxy
end GlobalTheory.SymAlg
