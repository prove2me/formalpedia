-- Prove2me | solution 1 for IntermediateField.exists_le_isUnramifiedOutside_dvd_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ca739178-7fed-5472-ad6b-859eb71de264

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Theorems.Thm_IntermediateField_adjoin_isUnramifiedOutside_of_isPrimitiveRoot_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_exists_le_isUnramifiedOutside_dvd_finrank
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand ExtCitation
open scoped Classical

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L'] (hL' : L'.IsUnramifiedOutside S) :
    ∃ (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : L' ≤ M),
      M.IsUnramifiedOutside S ∧ p ∣ Module.finrank ↥L' ↥(IntermediateField.extendScalars h) := by
  have hp : p.Prime := Fact.out
  set d : ℕ := Module.finrank ℚ ↥L' with hd
  have hd0 : 0 < d := Module.finrank_pos
  have hn : 0 < p ^ (d + 1) := pow_pos hp.pos _

  obtain ⟨ξ, hξ⟩ : ∃ ξ : AlgebraicClosure ℚ, IsPrimitiveRoot ξ (p ^ (d + 1)) := by
    haveI : NeZero (p ^ (d + 1)) := ⟨hn.ne'⟩
    obtain ⟨ξ, hroot⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (p ^ (d + 1)) (AlgebraicClosure ℚ)) (by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast (Nat.totient_pos.mpr hn).ne')
    exact ⟨ξ, Polynomial.isRoot_cyclotomic_iff.mp hroot⟩
  let C : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {ξ}
  have hCS : C.IsUnramifiedOutside S :=
    IntermediateField.adjoin_isUnramifiedOutside_of_isPrimitiveRoot_pow S hpS d ξ hξ
  have hMS : (L' ⊔ C).IsUnramifiedOutside S := hL'.sup hCS
  haveI : FiniteDimensional ℚ ↥(L' ⊔ C) := hMS.1
  refine ⟨L' ⊔ C, le_sup_left, hMS, ?_⟩

  have hξint : IsIntegral ℚ ξ := (hξ.isIntegral hn).tower_top
  have hC : Module.finrank ℚ ↥C = p ^ d * (p - 1) := by
    show Module.finrank ℚ ↥(IntermediateField.adjoin ℚ {ξ}) = _
    rw [IntermediateField.adjoin.finrank hξint, ← Polynomial.cyclotomic_eq_minpoly_rat hξ hn,
      Polynomial.natDegree_cyclotomic, Nat.totient_prime_pow_succ hp]
  have htower : d * Module.finrank ↥L' ↥(IntermediateField.extendScalars (le_sup_left : L' ≤ L' ⊔ C)) =
      Module.finrank ℚ ↥(L' ⊔ C) := by
    rw [← IntermediateField.relfinrank_eq_finrank_of_le]
    exact IntermediateField.finrank_bot_mul_relfinrank le_sup_left
  have hdvdC : Module.finrank ℚ ↥C ∣ Module.finrank ℚ ↥(L' ⊔ C) :=
    IntermediateField.finrank_dvd_of_le_right le_sup_right
  set m := Module.finrank ↥L' ↥(IntermediateField.extendScalars (le_sup_left : L' ≤ L' ⊔ C)) with hm
  have h1 : p ^ d ∣ d * m := by
    rw [htower]
    exact (Dvd.intro _ rfl : p ^ d ∣ p ^ d * (p - 1)).trans (hC ▸ hdvdC)
  by_contra hpm
  have hcop : Nat.Coprime (p ^ d) m := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
  have h2 : p ^ d ∣ d := hcop.dvd_of_dvd_mul_right h1
  exact absurd (Nat.le_of_dvd hd0 h2) (not_le.mpr (Nat.lt_pow_self hp.one_lt))

end S_IntermediateField_exists_le_isUnramifiedOutside_dvd_finrank
end P2MW
export P2MW.S_IntermediateField_exists_le_isUnramifiedOutside_dvd_finrank (solution)
