-- Prove2me | solution 1 for GlobalTheory.nontrivial_tensor_of_mem_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:25:44.911238+00:00
-- url     : https://prove2.me/submissions/ddecd41a-e9c7-4a33-86f8-f7e5bfd2dd03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AlgebraMapSurjectiveOfUnramifiedOfUniquePoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R C K : Type) [CommRing R] [AddCommGroup C] [Module R C]
    [Module.Finite R C] [Field K] [Algebra R K] (p : PrimeSpectrum R)
    (hp : RingHom.ker (algebraMap R K) = p.asIdeal) (h : p ∈ Module.support R C) :
    Nontrivial (K ⊗[R] C) := by
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at h
  let g : p.asIdeal.ResidueField →+* K := Ideal.ResidueField.lift p.asIdeal (algebraMap R K)
    hp.ge (by
      intro r hr
      have : algebraMap R K r ≠ 0 := fun h0 => hr (hp.le h0)
      exact (isUnit_iff_ne_zero.mpr this))
  letI : Algebra p.asIdeal.ResidueField K := g.toAlgebra
  haveI : IsScalarTower R p.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq (by
    intro r
    exact (Ideal.ResidueField.lift_algebraMap ..).symm)
  haveI : Nontrivial (K ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[R] C)) :=
    inferInstance
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField K K
    C).symm.toEquiv.nontrivial
end GlobalTheory
