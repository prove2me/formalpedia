-- Prove2me | solution 1 for GlobalTheory.JR.Hyp.exists_idempotent_of_not_isField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:59:43.600389+00:00
-- url     : https://prove2.me/submissions/11326cff-de12-4e11-ac1a-fce21b2c4b65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIdempotentStarEqOneSubOfNotIsField
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Hyp
namespace GlobalTheory.JR.Hyp
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → ¬ IsField A.L → ∃ e : A.L, e * e = e ∧ star e = 1 - e := by
  intro F E _ _ _ _ _ A hK hL
  obtain ⟨-, hinj, hN, hT, hnd⟩ := Et.quadratic_structure F E A
  have hnt : ∃ x y : A.L, x ≠ y := by
    obtain ⟨x, y, hxy⟩ := hK.exists_pair_ne
    exact ⟨_, _, hinj.ne hxy⟩
  have hy : ∃ y : A.L, y ≠ 0 ∧ ∀ b, y * b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hL ⟨hnt, mul_comm, fun {a} ha => hcon a ha⟩
  obtain ⟨y, hy0, hyu⟩ := hy
  have hz : ∃ z, Algebra.trace A.K A.L (star y * z) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy0 (hnd y hcon)
  obtain ⟨z, hz⟩ := hz
  obtain ⟨s, hs⟩ := hK.mul_inv_cancel hz
  have hn : y * star y = 0 := by
    by_contra hne
    have h1 : A.NL y ≠ 0 := by
      intro h0
      apply hne
      rw [← hN, h0, map_zero]
    obtain ⟨n, hn⟩ := hK.mul_inv_cancel h1
    apply hyu (star y * algebraMap A.K A.L n)
    rw [← mul_assoc, ← hN, ← map_mul, hn, map_one]
  have hs' := congrArg (algebraMap A.K A.L) hs
  rw [map_mul, hT, map_one, star_mul', star_star] at hs'
  have hst : star (star y * z * algebraMap A.K A.L s) = y * star z * algebraMap A.K A.L s := by
    rw [star_mul', star_mul', star_star, A.star_K]
  refine ⟨star y * z * algebraMap A.K A.L s, ?_, ?_⟩
  · linear_combination (star y * z * algebraMap A.K A.L s) * hs'
      - (z * star z * algebraMap A.K A.L s ^ 2) * hn
  · rw [hst]
    linear_combination hs'
end GlobalTheory.JR.Hyp
