-- Prove2me | solution 1 for GlobalTheory.exists_complete_isAlgClosed_padic_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:41:24.152232+00:00
-- url     : https://prove2.me/submissions/cdcf24b9-e26f-4c4e-8f5f-7c72eca51d7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Theorems.Thm_GlobalTheory_exists_complete_isAlgClosed_of_isDiscreteValuationRing
import Theorems.Thm_GlobalTheory_exists_padic_isometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution (V : Type*) (K : Type u)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] [CharZero K] (p : ℕ) [hp : Fact p.Prime]
    (hV : (p : V) ∈ IsLocalRing.maximalIdeal V) :
    ∃ (C : Type u) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C)
      (_ : IsAlgClosed C) (_ : NormedAlgebra ℚ_[p] C) (_ : Algebra K C),
      ∀ x : K, ‖algebraMap K C x‖ ≤ 1 ↔ x ∈ (algebraMap V K).range := by
  have hp0 : (p : V) ≠ 0 := fun h => by
    have := congrArg (algebraMap V K) h
    rw [map_natCast, map_zero] at this
    exact hp.out.ne_zero (by exact_mod_cast this)
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
    exists_complete_isAlgClosed_of_isDiscreteValuationRing V K hp0 hV
      (inv_pos.2 (zero_lt_one.trans h1)) (inv_lt_one_of_one_lt₀ h1)
  rw [map_natCast, map_natCast] at hCp
  haveI : CharZero C := charZero_of_injective_ringHom (algebraMap K C).injective
  obtain ⟨j, hj⟩ := exists_padic_isometry p hCp
  letI : Algebra ℚ_[p] C := j.toAlgebra
  letI : NormedAlgebra ℚ_[p] C :=
    { (inferInstance : Algebra ℚ_[p] C) with
      norm_smul_le := fun r x => by
        rw [Algebra.smul_def, norm_mul]
        exact le_of_eq (congrArg (· * ‖x‖) (hj r)) }
  exact ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hC⟩
end GlobalTheory
