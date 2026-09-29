-- Prove2me | solution 1 for HopfAlgebra.isReduced_of_finiteType_of_isAlgClosed_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e6b09f8a-596a-5a75-926d-9189dd46aee1

import Mathlib
import Theorems.Thm_HopfAlgebra_isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero

set_option maxHeartbeats 6400000
noncomputable section

theorem solution
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    IsReduced A := by

  refine isReduced_ofLocalizationMaximal A ?_
  intro J hJ

  obtain ⟨χ, hχ⟩ : ∃ χ : A →ₐ[K] K, J = RingHom.ker χ.toRingHom := by
    haveI := hJ
    letI : Field (A ⧸ J) := Ideal.Quotient.field J
    haveI : Algebra.FiniteType K (A ⧸ J) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K J) Ideal.Quotient.mk_surjective

    haveI : Module.Finite K (A ⧸ J) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ J)

    have hbij : Function.Bijective (algebraMap K (A ⧸ J)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : K ≃ₐ[K] (A ⧸ J) := AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ J)) hbij

    refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K J), ?_⟩
    ext a
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply]
    rw [show ∀ x, e.symm.toAlgHom x = e.symm x from fun _ => rfl,
      map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
  subst hχ

  haveI : (RingHom.ker χ.toRingHom).IsPrime := RingHom.ker_isPrime χ.toRingHom
  haveI : IsDomain (Localization.AtPrime (RingHom.ker χ.toRingHom)) :=
    HopfAlgebra.isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero K A χ
  infer_instance

end

end S_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero
end P2MW
export P2MW.S_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero (solution)
