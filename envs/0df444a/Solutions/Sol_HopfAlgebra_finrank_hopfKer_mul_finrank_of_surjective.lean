-- Prove2me | solution 1 for HopfAlgebra.finrank_hopfKer_mul_finrank_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0e91e202-75f7-54de-9776-4f81c3f2393e

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_mul_of_surjective
import Theorems.Thm_HopfAlgebra_finite_free_hopfKer_of_isPrincipalIdealRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_finrank_hopfKer_mul_finrank_of_surjective

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open HopfAlgebra
open scoped TensorProduct

universe u v w

namespace S17E2

theorem isCocomm_of_surjective {R : Type*} [CommRing R] {A B : Type*} [CommRing A] [Bialgebra R A]
    [CommRing B] [Bialgebra R B] [Coalgebra.IsCocomm R A] (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    Coalgebra.IsCocomm R B := by
  refine ⟨LinearMap.ext fun b => ?_⟩
  obtain ⟨a, rfl⟩ := hπ b
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← CoalgHomClass.map_comp_comul_apply]
  conv_rhs => rw [← Coalgebra.comm_comul R a]
  induction Coalgebra.comul (R := R) a with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

end S17E2

theorem solution {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]
    {A : Type v} [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    Module.finrank R ↥(HopfAlgebra.hopfKer π) * Module.finrank R B = Module.finrank R A := by
  let K := AlgebraicClosure (FractionRing R)
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := inferInstance
  haveI : Coalgebra.IsCocomm R B := S17E2.isCocomm_of_surjective π hπ
  obtain ⟨hfin, hfree⟩ := HopfAlgebra.finite_free_hopfKer_of_isPrincipalIdealRing π
  haveI := hfin
  haveI := hfree
  have hA := HopfAlgebra.natCard_algHom_eq_finrank_of_charZero R A K
  have hB := HopfAlgebra.natCard_algHom_eq_finrank_of_charZero R B K
  have hS := HopfAlgebra.natCard_algHom_eq_finrank_of_charZero R ↥(HopfAlgebra.hopfKer π) K
  have hmul := HopfAlgebra.natCard_algHom_eq_mul_of_surjective π hπ K
  rw [← hA, ← hB, ← hS, hmul, mul_comm]

end S_HopfAlgebra_finrank_hopfKer_mul_finrank_of_surjective
end P2MW
export P2MW.S_HopfAlgebra_finrank_hopfKer_mul_finrank_of_surjective (solution)
