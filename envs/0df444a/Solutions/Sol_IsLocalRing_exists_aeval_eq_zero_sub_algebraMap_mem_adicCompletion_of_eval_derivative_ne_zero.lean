-- Prove2me | solution 1 for IsLocalRing.exists_aeval_eq_zero_sub_algebraMap_mem_adicCompletion_of_eval_derivative_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d1cc965a-72f0-5a8c-8c66-333a13199dfb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_aeval_eq_zero_sub_algebraMap_mem_adicCompletion_of_eval_derivative_ne_zero

set_option autoImplicit false

open IsLocalRing Polynomial

theorem solution
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (P : Polynomial A) (hP : P.Monic) (r : ResidueField A)
    (hr : (P.map (residue A)).eval r = 0) (hr' : (P.map (residue A)).derivative.eval r ≠ 0) :
    ∃ (t : AdicCompletion (IsLocalRing.maximalIdeal A) A) (a : A), aeval t P = 0 ∧ residue A a = r ∧
      t - algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a ∈
        (IsLocalRing.maximalIdeal A).map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
  classical
  haveI : IsNoetherianRing A := inferInstance
  have h𝔪fg : (maximalIdeal A).FG := IsNoetherian.noetherian _
  let ι : A →+* AdicCompletion (maximalIdeal A) A := algebraMap A (AdicCompletion (maximalIdeal A) A)
  let I : Ideal (AdicCompletion (maximalIdeal A) A) := (maximalIdeal A).map ι
  haveI hI : IsAdicComplete I (AdicCompletion (maximalIdeal A) A) :=
    (IsAdicComplete.map_algebraMap_iff (maximalIdeal A) (AdicCompletion (maximalIdeal A) A)).mpr
      (AdicCompletion.isAdicComplete h𝔪fg)

  obtain ⟨a₀, ha₀⟩ := residue_surjective r

  have hres_eval : ∀ Q : Polynomial A, residue A (Q.eval a₀) = (Q.map (residue A)).eval r := by
    intro Q; rw [eval_map, ← ha₀, eval₂_at_apply]
  have h1 : P.eval a₀ ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, hres_eval, hr]
  have h2 : IsUnit (P.derivative.eval a₀) := by
    by_contra h
    apply hr'
    rw [derivative_map, ← hres_eval, residue_eq_zero_iff]
    exact (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)

  have hmonic : (P.map ι).Monic := hP.map ι
  have heval : (P.map ι).eval (ι a₀) ∈ I := by
    rw [eval_map, eval₂_at_apply]; exact Ideal.mem_map_of_mem ι h1
  have hunit : IsUnit (Ideal.Quotient.mk I ((P.map ι).derivative.eval (ι a₀))) := by
    rw [derivative_map, eval_map, eval₂_at_apply]
    exact (h2.map ι).map _
  obtain ⟨t, ht, hta⟩ := HenselianRing.is_henselian (I := I) (P.map ι) hmonic (ι a₀) heval hunit
  refine ⟨t, a₀, ?_, ha₀, hta⟩
  rw [aeval_def, ← eval_map]; exact ht

end S_IsLocalRing_exists_aeval_eq_zero_sub_algebraMap_mem_adicCompletion_of_eval_derivative_ne_zero
end P2MW
export P2MW.S_IsLocalRing_exists_aeval_eq_zero_sub_algebraMap_mem_adicCompletion_of_eval_derivative_ne_zero (solution)
