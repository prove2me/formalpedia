-- Prove2me | solution 1 for Module.Basis.tensorProduct_tensorProduct_linearIndependent_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/fe6c2a3a-3c16-5b84-8c12-dc6d68531a75

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.Algebra.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Basis_tensorProduct_tensorProduct_linearIndependent_restrictScalars

open scoped TensorProduct

theorem solution
    (R : Type) (K : Type) (A : Type) [CommRing R] [CommRing K] [Algebra R K] [CommRing A]
    [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (hinj : Function.Injective (algebraMap R K))
    {n : ℕ} (b : Module.Basis (Fin n) K A) :
    LinearIndependent R ((b.tensorProduct (b.tensorProduct b)) :
      Fin n × Fin n × Fin n → A ⊗[K] (A ⊗[K] A)) :=
  (b.tensorProduct (b.tensorProduct b)).linearIndependent.restrict_scalars
    (Algebra.algebraMap_eq_smul_one' (R := R) (A := K) ▸ hinj)

end S_Module_Basis_tensorProduct_tensorProduct_linearIndependent_restrictScalars
end P2MW
export P2MW.S_Module_Basis_tensorProduct_tensorProduct_linearIndependent_restrictScalars (solution)
