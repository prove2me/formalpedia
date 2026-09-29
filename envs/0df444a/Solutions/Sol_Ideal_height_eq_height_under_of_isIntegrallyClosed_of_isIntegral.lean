-- Prove2me | solution 1 for Ideal.height_eq_height_under_of_isIntegrallyClosed_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4e872abc-4dc9-5aed-82a5-27107ab71874

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral

set_option autoImplicit false

universe u

namespace HeightAux

theorem eq_of_le_of_under_eq {P B : Type*} [CommRing P] [CommRing B] [Algebra P B]
    [Algebra.IsIntegral P B] {Q q : Ideal B} [Q.IsPrime] [q.IsPrime] (hle : Q ≤ q)
    (hu : q.under P ≤ Q.under P) : Q = q := by
  by_contra hne
  have hlt : Q < q := lt_of_le_of_ne hle hne
  obtain ⟨x, hxq, hxQ⟩ := Set.exists_of_ssubset hlt
  have := Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxq, hxQ⟩
    (Algebra.IsIntegral.isIntegral (R := P) x)
  exact absurd (lt_of_lt_of_le this hu) (lt_irrefl _)

theorem height_eq_height_under (P B : Type*) [CommRing P] [IsDomain P] [IsNoetherianRing P]
    [IsIntegrallyClosed P] [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra P B]
    [FaithfulSMul P B] [Algebra.IsIntegral P B] (q : Ideal B) [q.IsPrime] :
    q.height = (q.under P).height := by
  set p := q.under P with hp
  set I := Ideal.map (algebraMap P B) p with hI
  have hIq : I ≤ q := Ideal.map_comap_le
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ q := by rw [Ideal.mk_ker]; exact hIq
  haveI hQbar : (Ideal.map (Ideal.Quotient.mk I) q).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have key := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q
  suffices h0 : (Ideal.map (Ideal.Quotient.mk I) q).height = 0 by
    rw [key, ← hI, h0, add_zero]
  refine nonpos_iff_eq_zero.mp ?_
  rw [← ENat.coe_zero, Ideal.height_le_iff]
  intro Q' hQ' hQ'lt
  exfalso

  set Q := Ideal.comap (Ideal.Quotient.mk I) Q' with hQ
  have hIQ : I ≤ Q := (Ideal.mk_ker (I := I)).symm.trans_le (Ideal.ker_le_comap _)
  have hQq : Q ≤ q := by
    refine (Ideal.comap_mono hQ'lt.le).trans ?_
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    refine sup_le le_rfl ?_
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]; exact hIq
  have hunder : q.under P ≤ Q.under P := by
    change p ≤ Ideal.comap (algebraMap P B) Q
    exact Ideal.le_comap_of_map_le hIQ
  have hQeq : Q = q := eq_of_le_of_under_eq hQq hunder
  have hQ'eq : Ideal.map (Ideal.Quotient.mk I) Q = Q' :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  rw [hQeq] at hQ'eq
  exact absurd (hQ'eq ▸ hQ'lt) (lt_irrefl _)

end HeightAux
theorem solution
    (P B : Type u) [CommRing P] [IsDomain P] [IsNoetherianRing P] [IsIntegrallyClosed P]
    [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra P B] [FaithfulSMul P B]
    [Algebra.IsIntegral P B] (q : Ideal B) [q.IsPrime] :
    q.height = (q.under P).height :=
  HeightAux.height_eq_height_under P B q

end S_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral
end P2MW
export P2MW.S_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral (solution)
