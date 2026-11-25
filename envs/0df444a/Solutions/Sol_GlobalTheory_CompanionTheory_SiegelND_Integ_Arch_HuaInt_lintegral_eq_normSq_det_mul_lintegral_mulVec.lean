-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_eq_normSq_det_mul_lintegral_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:38:16.222617+00:00
-- url     : https://prove2.me/submissions/0876b7ed-8360-4786-a0be-aa3f13370518

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralLinearChangeVariablesComplex
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_det_restrictScalars_toLin__6aa316170093

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
theorem _root_.solution (n : ℕ) (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : Matrix.det D ≠ 0) (g : (Fin n → ℂ) → ENNReal) (hg : Measurable g) :
    ∫⁻ u, g u = ENNReal.ofReal (Complex.normSq (Matrix.det D)) * ∫⁻ v, g (D *ᵥ v) := by
  set f : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' D).restrictScalars ℝ with hf
  have hdet : LinearMap.det f = Complex.normSq (Matrix.det D) := det_restrictScalars_toLin' D
  have hpos : 0 < Complex.normSq (Matrix.det D) := Complex.normSq_pos.mpr hD
  have hne : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact hpos.ne'
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Fin n → ℂ)) hne
  have hfm : Measurable f := f.continuous_of_finiteDimensional.measurable
  have key : ∫⁻ v, g (D *ᵥ v) = ENNReal.ofReal (Complex.normSq (Matrix.det D))⁻¹ * ∫⁻ u, g u := by
    have e : ∀ v, D *ᵥ v = f v := fun v => by simp [hf, Matrix.toLin'_apply]
    simp_rw [e]
    rw [← lintegral_map hg hfm, hmap, lintegral_smul_measure, hdet, abs_of_pos (inv_pos.mpr hpos), smul_eq_mul]
  rw [key, ← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one,
    one_mul]
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
