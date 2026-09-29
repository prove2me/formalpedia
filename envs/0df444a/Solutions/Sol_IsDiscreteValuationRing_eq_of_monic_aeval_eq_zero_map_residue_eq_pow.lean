-- Prove2me | solution 1 for IsDiscreteValuationRing.eq_of_monic_aeval_eq_zero_map_residue_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/9842cc3b-fc49-59e1-8cf3-73a1a49ae808

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_eq_of_monic_aeval_eq_zero_map_residue_eq_pow

set_option autoImplicit false

open Polynomial IsLocalRing

namespace Ws50RT

theorem eq_of_monic_aeval_eq_zero_map_residue_eq_pow
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {F : Type} [Field F] [Algebra 𝒪 F] (hinj : Function.Injective (algebraMap 𝒪 F))
    (x : F) (c c' : ResidueField 𝒪)
    (R : Polynomial 𝒪) (hR : R.Monic) (hRx : aeval x R = 0)
    (hRc : R.map (residue 𝒪) = (X - C c) ^ R.natDegree)
    (R' : Polynomial 𝒪) (hR' : R'.Monic) (hR'x : aeval x R' = 0)
    (hR'c : R'.map (residue 𝒪) = (X - C c') ^ R'.natDegree) :
    c = c' := by
  haveI : Module.IsTorsionFree 𝒪 F := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have hint : IsIntegral 𝒪 x := ⟨R, hR, by rwa [← aeval_def]⟩
  set m := minpoly 𝒪 x with hm
  have hmR : m ∣ R := (minpoly.isIntegrallyClosed_dvd_iff hint R).mp hRx
  have hmR' : m ∣ R' := (minpoly.isIntegrallyClosed_dvd_iff hint R').mp hR'x
  have hmmonic : m.Monic := minpoly.monic hint
  have hdeg : 0 < m.natDegree := minpoly.natDegree_pos hint

  set mb := m.map (residue 𝒪) with hmb
  have hmb1 : mb ∣ (X - C c) ^ R.natDegree := hRc ▸ Polynomial.map_dvd (residue 𝒪) hmR
  have hmb2 : mb ∣ (X - C c') ^ R'.natDegree := hR'c ▸ Polynomial.map_dvd (residue 𝒪) hmR'
  have hmbdeg : mb.natDegree = m.natDegree := hmmonic.natDegree_map (residue 𝒪)
  by_contra hcc
  have hcop : IsCoprime ((X - C c) ^ R.natDegree) ((X - C c') ^ R'.natDegree) := by
    apply IsCoprime.pow
    have := Polynomial.pairwise_coprime_X_sub_C (K := ResidueField 𝒪) (s := id) Function.injective_id hcc
    exact this
  have hunit : IsUnit mb := hcop.isUnit_of_dvd' hmb1 hmb2
  have : mb.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
  omega

end Ws50RT

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {F : Type} [Field F] [Algebra 𝒪 F] (hinj : Function.Injective (algebraMap 𝒪 F))
    (x : F) (c c' : IsLocalRing.ResidueField 𝒪)
    (R : Polynomial 𝒪) (hR : R.Monic) (hRx : Polynomial.aeval x R = 0)
    (hRc : R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C c) ^ R.natDegree)
    (R' : Polynomial 𝒪) (hR' : R'.Monic) (hR'x : Polynomial.aeval x R' = 0)
    (hR'c : R'.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C c') ^ R'.natDegree) :
    c = c' :=
  Ws50RT.eq_of_monic_aeval_eq_zero_map_residue_eq_pow hinj x c c' R hR hRx hRc R' hR' hR'x hR'c

end S_IsDiscreteValuationRing_eq_of_monic_aeval_eq_zero_map_residue_eq_pow
end P2MW
export P2MW.S_IsDiscreteValuationRing_eq_of_monic_aeval_eq_zero_map_residue_eq_pow (solution)
