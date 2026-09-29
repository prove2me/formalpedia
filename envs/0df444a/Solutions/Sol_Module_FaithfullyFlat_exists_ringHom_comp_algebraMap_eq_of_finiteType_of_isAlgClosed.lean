-- Prove2me | solution 1 for Module.FaithfullyFlat.exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/efd46eb1-f5d7-5ff6-94a3-af2e1ce686e6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_FaithfullyFlat_exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

universe u

open TensorProduct

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    [Module.FaithfullyFlat S S'] [Algebra.FiniteType S S']
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) :
    ∃ σ : S' →+* k, σ.comp (algebraMap S S') = sk := by
  classical
  letI : Algebra S k := sk.toAlgebra
  have hsk : algebraMap S k = sk := rfl
  let B := k ⊗[S] S'
  haveI : Nontrivial B := Module.FaithfullyFlat.rTensor_nontrivial S S' k
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal B
  letI : Field (B ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Algebra.FiniteType k B := inferInstance
  haveI : Algebra.FiniteType k (B ⧸ 𝔪) := inferInstance
  haveI : Module.Finite k (B ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ 𝔪)
  haveI : Algebra.IsAlgebraic k (B ⧸ 𝔪) := inferInstance
  haveI : Module.Free k (B ⧸ 𝔪) := Module.Free.of_divisionRing k (B ⧸ 𝔪)
  haveI : Module.Flat k (B ⧸ 𝔪) := inferInstance
  haveI : Module.IsTorsionFree k (B ⧸ 𝔪) := inferInstance
  let ψ : (B ⧸ 𝔪) →ₐ[k] k := IsAlgClosed.lift
  let σ : S' →+* k :=
    ψ.toRingHom.comp ((Ideal.Quotient.mk 𝔪).comp (Algebra.TensorProduct.includeRight (R := S) (A := k) (B := S')).toRingHom)
  refine ⟨σ, ?_⟩
  ext s
  have h1 : (Algebra.TensorProduct.includeRight (R := S) (A := k) (B := S')) (algebraMap S S' s) =
      algebraMap k B (sk s) := by
    show (1 : k) ⊗ₜ[S] (algebraMap S S' s) = algebraMap k (k ⊗[S] S') (sk s)
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.algebraMap_eq_smul_one (A := S') s, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
      mul_one, hsk]
  show ψ (Ideal.Quotient.mk 𝔪 ((Algebra.TensorProduct.includeRight (R := S) (A := k) (B := S')) (algebraMap S S' s))) = sk s
  rw [h1]
  exact ψ.commutes (sk s)

end S_Module_FaithfullyFlat_exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed
end P2MW
export P2MW.S_Module_FaithfullyFlat_exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed (solution)
