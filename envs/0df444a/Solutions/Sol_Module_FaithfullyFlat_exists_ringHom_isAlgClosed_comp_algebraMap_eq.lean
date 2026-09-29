-- Prove2me | solution 1 for Module.FaithfullyFlat.exists_ringHom_isAlgClosed_comp_algebraMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/cbf86d7b-ea8f-562f-9f3b-94edda284b30

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_FaithfullyFlat_exists_ringHom_isAlgClosed_comp_algebraMap_eq

set_option autoImplicit false

universe u

open scoped TensorProduct

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (k : Type u) [Field k] (sk : S →+* k) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (j : k →+* K) (sK : S' →+* K),
      sK.comp (algebraMap S S') = j.comp sk := by
  classical
  letI : Algebra S k := sk.toAlgebra

  let R : Type u := k ⊗[S] S'
  haveI : Nontrivial R := Module.FaithfullyFlat.rTensor_nontrivial S S' k
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  let K : Type u := AlgebraicClosure (R ⧸ m)
  let π : R →+* K := (algebraMap (R ⧸ m) K).comp (Ideal.Quotient.mk m)
  refine ⟨K, inferInstance, inferInstance, π.comp (algebraMap k R),
    π.comp (Algebra.TensorProduct.includeRight : S' →ₐ[S] R).toRingHom, ?_⟩
  ext s
  change π (Algebra.TensorProduct.includeRight (R := S) (A := k) (B := S') (algebraMap S S' s)) =
    π (algebraMap k R (sk s))
  congr 1
  rw [AlgHom.commutes]
  change algebraMap S R s = algebraMap k R (algebraMap S k s)
  exact (IsScalarTower.algebraMap_apply S k R s)

end S_Module_FaithfullyFlat_exists_ringHom_isAlgClosed_comp_algebraMap_eq
end P2MW
export P2MW.S_Module_FaithfullyFlat_exists_ringHom_isAlgClosed_comp_algebraMap_eq (solution)
