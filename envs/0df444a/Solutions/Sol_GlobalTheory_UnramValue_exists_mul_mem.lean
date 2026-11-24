-- Prove2me | solution 1 for GlobalTheory.UnramValue.exists_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:19:19.686418+00:00
-- url     : https://prove2.me/submissions/306cb010-fe75-4851-a49c-edd3f061db5f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield
import Theorems.Thm_GlobalTheory_UnramValue_rootRing_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.UnramValue
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.UnramValue
theorem _root_.solution {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) :
    ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ∃ c : ℤ_[l], c ≠ 0 ∧ algebraMap ℤ_[l] (Om l) c * x ∈ rootRing l m := by
  have hp : l.Prime := Fact.out
  unfold MaximalUnramifiedExtension at hx
  rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun y _ => Algebra.IsAlgebraic.isAlgebraic y)] at hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨m, hm, hlm, hym⟩ := hy
    refine ⟨m, hm, hlm, 1, one_ne_zero, ?_⟩
    rw [map_one, one_mul]
    exact Algebra.subset_adjoin hym
  | algebraMap q =>
    refine ⟨1, one_pos, hp.not_dvd_one, ?_⟩
    by_cases hq : ‖q‖ ≤ 1
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [map_one, one_mul]
      obtain ⟨a, ha⟩ : ∃ a : ℤ_[l], (a : ℚ_[l]) = q := ⟨⟨q, hq⟩, rfl⟩
      have e : algebraMap ℚ_[l] (Om l) q = algebraMap ℤ_[l] (Om l) a := by
        rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l), ← ha]
        rfl
      rw [e]
      exact Subalgebra.algebraMap_mem _ _
    · have hq0 : q ≠ 0 := by rintro rfl; simp at hq
      have hinv : ‖q⁻¹‖ ≤ 1 := by
        rw [norm_inv]
        exact inv_le_one_of_one_le₀ (le_of_not_ge hq)
      obtain ⟨a, ha⟩ : ∃ a : ℤ_[l], (a : ℚ_[l]) = q⁻¹ := ⟨⟨q⁻¹, hinv⟩, rfl⟩
      refine ⟨a, ?_, ?_⟩
      · rintro rfl
        apply hq0
        rw [PadicInt.coe_zero] at ha
        exact inv_eq_zero.1 ha.symm
      · have e : algebraMap ℤ_[l] ℚ_[l] a * q = 1 := by
          rw [show algebraMap ℤ_[l] ℚ_[l] a = (a : ℚ_[l]) from rfl, ha, inv_mul_cancel₀ hq0]
        rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l), ← map_mul, e, map_one]
        exact one_mem _
  | add x y _ _ hx hy =>
    obtain ⟨m1, hm1, hl1, c1, hc1, h1⟩ := hx
    obtain ⟨m2, hm2, hl2, c2, hc2, h2⟩ := hy
    refine ⟨m1 * m2, Nat.mul_pos hm1 hm2, fun h => (hp.dvd_mul.1 h).elim hl1 hl2, c1 * c2,
      mul_ne_zero hc1 hc2, ?_⟩
    have e : algebraMap ℤ_[l] (Om l) (c1 * c2) * (x + y) =
        algebraMap ℤ_[l] (Om l) c2 * (algebraMap ℤ_[l] (Om l) c1 * x) +
          algebraMap ℤ_[l] (Om l) c1 * (algebraMap ℤ_[l] (Om l) c2 * y) := by
      rw [map_mul]
      ring
    rw [e]
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (rootRing_mono (dvd_mul_right m1 m2) h1))
      (mul_mem (Subalgebra.algebraMap_mem _ _) (rootRing_mono (dvd_mul_left m2 m1) h2))
  | mul x y _ _ hx hy =>
    obtain ⟨m1, hm1, hl1, c1, hc1, h1⟩ := hx
    obtain ⟨m2, hm2, hl2, c2, hc2, h2⟩ := hy
    refine ⟨m1 * m2, Nat.mul_pos hm1 hm2, fun h => (hp.dvd_mul.1 h).elim hl1 hl2, c1 * c2,
      mul_ne_zero hc1 hc2, ?_⟩
    have e : algebraMap ℤ_[l] (Om l) (c1 * c2) * (x * y) =
        (algebraMap ℤ_[l] (Om l) c1 * x) * (algebraMap ℤ_[l] (Om l) c2 * y) := by
      rw [map_mul]
      ring
    rw [e]
    exact mul_mem (rootRing_mono (dvd_mul_right m1 m2) h1) (rootRing_mono (dvd_mul_left m2 m1) h2)
end GlobalTheory.UnramValue
