-- Prove2me | solution 1 for GlobalTheory.UnitaryCayley.exists_isCayleyU_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:24:33.211081+00:00
-- url     : https://prove2.me/submissions/4ee76dab-0d7b-4aaf-97f7-ed769ea57f94

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsIsCayleyUIff
import Theorems.Thm_GlobalTheory_UnitaryCayley_trace_Jm
import Theorems.Thm_GlobalTheory_UnitaryCayley_exists_unitary
import Theorems.Thm_GlobalTheory_UnitaryCayley_trace_Hpk
import Theorems.Thm_Formalism_QuantumDeterminants_hermitian_pos_facts_hold


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset PI.UpqRep
noncomputable section
open GlobalTheory GlobalTheory.UnitaryCayley
namespace GlobalTheory.UnitaryCayley
theorem _root_.solution (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) :
    (∃ P, IsCayleyU k r ε P) ↔ (univ.filter fun i => ε i = true).card = k + r := by
  constructor
  · rintro ⟨P, ⟨-, hP⟩, hu⟩
    have h1 : (Hpk k r).trace = (Jm ε).trace := by
      rw [← hP, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
        Unitary.mul_star_self_of_mem hu, Matrix.one_mul]
    rw [trace_Hpk, trace_Jm] at h1
    have : ((univ.filter fun i => ε i = true).card : ℂ) = ((k + r : ℕ) : ℂ) := by
      push_cast at h1 ⊢; linear_combination -h1 / 2
    exact_mod_cast this
  · intro h
    obtain ⟨h1, h2, -⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
    obtain ⟨P, hu, hP⟩ := exists_unitary (Hpk k r) h1 h2 ε (by
      rw [trace_Hpk, trace_Jm, h]; push_cast; ring)
    exact ⟨P, ⟨⟨⟨P, star P, Unitary.mul_star_self_of_mem hu, Unitary.star_mul_self_of_mem hu⟩, rfl⟩, hP⟩, hu⟩
end GlobalTheory.UnitaryCayley
