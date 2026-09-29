-- Prove2me | solution 1 for NumberField.AdeleRing.principalIdeles_sup_unitIdelesOutside_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/619620ec-ffc0-5293-bedd-b3bfcb8d81bf

import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_unitIdelesOutside_sup_range_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_principalIdeles_sup_unitIdelesOutside_eq_top

set_option autoImplicit false
open scoped nonZeroDivisors

theorem solution
    (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum R))
    (hS : ∀ c : ClassGroup R, ∃ I : (Ideal R)⁰, ClassGroup.mk0 I = c ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum R, v.asIdeal ∣ (I : Ideal R) → v ∈ S) :
    M4aHerbrand.principalIdeles R K ⊔ NumberField.AdeleRing.unitIdelesOutside R K S = ⊤ := by
  rw [eq_top_iff]
  rintro x -

  set π : (NumberField.AdeleRing R K)ˣ →* (IsDedekindDomain.FiniteAdeleRing R K)ˣ :=
    Units.map (RingHom.snd (NumberField.InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing R K)).toMonoidHom
    with hπ
  have hx : π x ∈ IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K S ⊔
      (Units.map (algebraMap K (IsDedekindDomain.FiniteAdeleRing R K) :
        K →* IsDedekindDomain.FiniteAdeleRing R K)).range := by
    rw [IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside_sup_range_eq_top R K S hS]
    exact Subgroup.mem_top _
  obtain ⟨u, hu, _, ⟨a, rfl⟩, hua⟩ := Subgroup.mem_sup.1 hx

  set P : (NumberField.AdeleRing R K)ˣ :=
    Units.map (algebraMap K (NumberField.AdeleRing R K) : K →* NumberField.AdeleRing R K) a with hP
  have hPπ : π P = Units.map (algebraMap K (IsDedekindDomain.FiniteAdeleRing R K) :
      K →* IsDedekindDomain.FiniteAdeleRing R K) a := Units.ext rfl
  have hmem : P⁻¹ * x ∈ NumberField.AdeleRing.unitIdelesOutside R K S := by
    show π (P⁻¹ * x) ∈ IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K S
    rw [map_mul, map_inv, hPπ, ← hua, mul_comm u, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hu
  rw [← mul_inv_cancel_left P x]
  exact Subgroup.mul_mem_sup ⟨a, rfl⟩ hmem

end S_NumberField_AdeleRing_principalIdeles_sup_unitIdelesOutside_eq_top
end P2MW
export P2MW.S_NumberField_AdeleRing_principalIdeles_sup_unitIdelesOutside_eq_top (solution)
