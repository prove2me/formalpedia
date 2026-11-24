-- Prove2me | solution 1 for GlobalTheory.SimMult.exists_norm_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:48:11.459694+00:00
-- url     : https://prove2.me/submissions/9f1904c0-e34f-48a1-9b24-e3ad1df0fa63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSimTrivialOfMult
import Theorems.Thm_GlobalTheory_SimMult_norm_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimMult
variable {O : Type*} [CommRing O] (σ : O →+* O)
namespace GlobalTheory.SimMult
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (ν : ℤ) (S : Set (Ideal O)) (hS : S.Finite)
    (hmax : ∀ P ∈ S, P.IsMaximal) (hloc : ∀ P ∈ S, ∃ c, c * σ c - ν ∈ P) :
    ∃ c, ∀ P ∈ S, c * σ c - ν ∈ P := by
  have hsurj : Function.Surjective σ := fun x => ⟨σ x, hσ x⟩
  have hbij : Function.Bijective σ := ⟨Function.LeftInverse.injective hσ, hsurj⟩
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert P S hP hS ih =>
    obtain ⟨c, hc⟩ := ih (fun Q hQ => hmax Q (Set.mem_insert_of_mem _ hQ))
      (fun Q hQ => hloc Q (Set.mem_insert_of_mem _ hQ))
    by_cases hcP : c * σ c - ν ∈ P
    · exact ⟨c, fun Q hQ => by rcases hQ with rfl | hQ; exacts [hcP, hc Q hQ]⟩
    have hfix : σ (c * σ c - ν) = c * σ c - ν := by
      rw [map_sub, map_mul, hσ, map_intCast, mul_comm]
    obtain ⟨d, hd⟩ := hloc P (Set.mem_insert _ _)
    have hPm := hmax P (Set.mem_insert _ _)
    obtain ⟨y, e, he, hy⟩ := hPm.exists_inv hcP
    set δ := c * σ c - ν
    have hy' := congrArg σ hy
    rw [map_add, map_mul, hfix, map_one] at hy'

    refine ⟨d + (c - d) * (e * σ e), fun Q hQ => ?_⟩
    rcases hQ with rfl | hQ
    · refine norm_congr σ Q ?_ ?_ hd
      · rw [add_sub_cancel_left]
        exact Q.mul_mem_left _ (Q.mul_mem_right _ he)
      · rw [add_sub_cancel_left, map_mul, map_mul, hσ]
        exact Q.mul_mem_left _ (Q.mul_mem_left _ he)
    · have h1 : d + (c - d) * (e * σ e) - c = ((c - d) * (-y * σ e - σ y)) * δ := by
        linear_combination (c - d) * σ e * hy + (c - d) * hy'
      refine norm_congr σ Q ?_ ?_ (hc Q hQ)
      · rw [h1]; exact Q.mul_mem_left _ (hc Q hQ)
      · rw [h1, map_mul, hfix]; exact Q.mul_mem_left _ (hc Q hQ)
end GlobalTheory.SimMult
