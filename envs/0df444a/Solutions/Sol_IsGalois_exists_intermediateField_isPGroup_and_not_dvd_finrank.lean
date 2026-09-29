-- Prove2me | solution 1 for IsGalois.exists_intermediateField_isPGroup_and_not_dvd_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/38372735-9cf9-54bb-952c-a273f591d37e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsGalois_exists_intermediateField_isPGroup_and_not_dvd_finrank

set_option autoImplicit false

theorem solution
    (k K : Type*) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (p : ℕ) [Fact p.Prime] :
    ∃ E : IntermediateField k K, IsPGroup p (K ≃ₐ[↥E] K) ∧ ¬ p ∣ Module.finrank k ↥E := by

  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p (K ≃ₐ[k] K)))
  refine ⟨IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K)), ?_, ?_⟩
  ·
    have hfix : (IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))).fixingSubgroup = (P : Subgroup (K ≃ₐ[k] K)) :=
      IntermediateField.fixingSubgroup_fixedField (P : Subgroup (K ≃ₐ[k] K))
    let e : ↥(P : Subgroup (K ≃ₐ[k] K)) ≃* (K ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K)))] K) :=
      (MulEquiv.subgroupCongr hfix.symm).trans
        (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))))
    exact IsPGroup.of_surjective P.isPGroup' e.toMonoidHom e.surjective
  ·
    have hEK : Module.finrank ↥(IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))) K = Nat.card ↥(P : Subgroup (K ≃ₐ[k] K)) :=
      IntermediateField.finrank_fixedField_eq_card (P : Subgroup (K ≃ₐ[k] K))
    have htower := Module.finrank_mul_finrank k ↥(IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))) K
    have hG : Nat.card (K ≃ₐ[k] K) = Module.finrank k K := IsGalois.card_aut_eq_finrank k K
    have hPi := (P : Subgroup (K ≃ₐ[k] K)).card_mul_index
    have hcard : 0 < Nat.card ↥(P : Subgroup (K ≃ₐ[k] K)) := Nat.card_pos
    have hidx : Module.finrank k ↥(IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))) = (P : Subgroup (K ≃ₐ[k] K)).index := by
      apply Nat.eq_of_mul_eq_mul_left hcard
      calc Nat.card ↥(P : Subgroup (K ≃ₐ[k] K)) * Module.finrank k ↥(IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K)))
          = Module.finrank k ↥(IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))) *
              Module.finrank ↥(IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))) K := by rw [mul_comm, hEK]
        _ = Module.finrank k K := htower
        _ = Nat.card (K ≃ₐ[k] K) := hG.symm
        _ = Nat.card ↥(P : Subgroup (K ≃ₐ[k] K)) * (P : Subgroup (K ≃ₐ[k] K)).index := hPi.symm
    rw [hidx]
    exact P.not_dvd_index

end S_IsGalois_exists_intermediateField_isPGroup_and_not_dvd_finrank
end P2MW
export P2MW.S_IsGalois_exists_intermediateField_isPGroup_and_not_dvd_finrank (solution)
