-- Prove2me | solution 1 for GlobalTheory.SymAlg.baseChangeEquiv_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:37.6518+00:00
-- url     : https://prove2.me/submissions/af6bc691-b6c8-4728-90d7-717541843095

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {j : M →ₗ[R] W} (h : IsBaseChange S j) (s : S)
    (x : SymmetricAlgebra R M) : baseChangeEquiv h (s ⊗ₜ x) = s • mapOver S j x :=
  baseChangeHom_tmul j s x
end GlobalTheory.SymAlg
