-- Prove2me | solution 1 for GlobalTheory.UTrans.Model.not_mem_tvGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:34.276493+00:00
-- url     : https://prove2.me/submissions/7a9c6e34-d23f-4213-aef2-051572c1b547

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_NontrivialTransvection
import Theorems.Thm_GlobalTheory_UTrans_Model_det_of_mem_tvGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.Model
open GlobalTheory.UTrans
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.UTrans.Model
theorem _root_.solution :
    IsU (starRingEnd ℂ) !![0, 1; 1, 0] !![Complex.I, 0; 0, Complex.I] ∧
    !![Complex.I, 0; 0, Complex.I] ∉ TvGen (starRingEnd ℂ) !![0, 1; 1, 0] := by
  have hI : ∀ v : Fin 2 → ℂ, (!![Complex.I, 0; 0, Complex.I]).mulVec v = Complex.I • v := by
    intro v
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨fun v w => ?_, fun hm => ?_⟩
  · simp only [hf, hI, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    linear_combination (-(v a * !![(0 : ℂ), 1; 1, 0] a b * (starRingEnd ℂ) (w b))) * Complex.I_sq
  · have hd := det_of_mem_tvGen _ _ hm
    rw [Matrix.det_fin_two_of] at hd
    norm_num [Complex.ext_iff] at hd
end GlobalTheory.UTrans.Model
