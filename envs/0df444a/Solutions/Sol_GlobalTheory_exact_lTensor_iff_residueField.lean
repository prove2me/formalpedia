-- Prove2me | solution 1 for GlobalTheory.exact_lTensor_iff_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:47:00.079379+00:00
-- url     : https://prove2.me/submissions/760e2576-be0f-48e1-870b-7d76627cb438

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Theorems.Thm_GlobalTheory_exact_lTensor_iff_of_faithfullyFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Function
open GlobalTheory
variable {R : Type*} [CommRing R] {A B C : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
namespace GlobalTheory
theorem _root_.solution (p : Ideal R) [p.IsPrime] (L : Type*) [Field L]
    [Algebra R L] (hL : RingHom.ker (algebraMap R L) = p) (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    Exact (f.lTensor L) (g.lTensor L) ↔
      Exact (f.lTensor p.ResidueField) (g.lTensor p.ResidueField) := by
  let φ : p.ResidueField →ₐ[R] L := Ideal.ResidueField.liftₐ p (Algebra.ofId R L) hL.ge (by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hx (hL ▸ h0))
  letI : Algebra p.ResidueField L := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R p.ResidueField L :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  exact exact_lTensor_iff_of_faithfullyFlat p.ResidueField L f g
end GlobalTheory
