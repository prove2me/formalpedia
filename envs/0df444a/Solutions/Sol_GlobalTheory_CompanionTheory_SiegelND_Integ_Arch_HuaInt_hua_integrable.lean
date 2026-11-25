-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.hua_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:09.42397+00:00
-- url     : https://prove2.me/submissions/3f430c07-620f-4cc8-b3ae-a9dc42419f31

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DetWEqNormSqDetOneAddIStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_OneLeDetWStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DetWBlockMatrixFormulaStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralPowerLineScalingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralLinearChangeVariablesComplexStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralComplexPowerFiniteStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianHaarBlockDecompositionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HuaDeterminantIntegrableOfLt
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_continuous_detW
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_measurable_term
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_inner_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_mem_hermC
import Theorems.Thm_GlobalTheory_T_hermitian_haar_block_decomposition
import Theorems.Thm_GlobalTheory_T_one_le_detW_of_isHermitian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
theorem _root_.solution : ∀ (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s → ∀ ν : Measure (hermC n), ν.IsAddHaarMeasure →
    Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  intro n
  induction n with
  | zero =>
    intro s _ ν hν
    have : IsFiniteMeasure ν := by
      haveI : Finite (hermC 0) := by
        haveI : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ) := inferInstance
        exact Finite.of_subsingleton
      haveI : CompactSpace (hermC 0) := Finite.compactSpace
      exact ⟨isCompact_univ.measure_lt_top⟩
    have h1 : ∀ b : hermC 0, detW (b : Matrix (Fin 0) (Fin 0) ℂ) ^ (-s) = 1 := by
      intro b
      simp [detW]
    simp only [h1]
    exact integrable_const _
  | succ n ih =>
    intro s hs ν hν
    have hs' : (n : ℝ) + 1 / 2 < s := by push_cast at hs; linarith
    have hpos : ∀ b : hermC (n + 1), 0 ≤ detW (b : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s) := fun b =>
      Real.rpow_nonneg (by linarith [GlobalTheory.T.one_le_detW_of_isHermitian _ _ (mem_hermC.1 b.2)]) _
    have hmeas := measurable_term (n + 1) s
    have hm2 : Measurable (fun b : hermC (n + 1) => detW (b : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)) :=
      (((continuous_detW (n + 1)).comp continuous_subtype_val).measurable.pow_const _)
    refine ⟨hm2.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hpos)]
    obtain ⟨c, hc, hF⟩ := GlobalTheory.T.hermitian_haar_block_decomposition n ν (Measure.addHaar) hν inferInstance
    obtain ⟨K, hK, hI⟩ := inner_eq n s hs'
    rw [hF _ hmeas]
    simp only [hI]
    rw [lintegral_const_mul _ (measurable_term n (s - 1))]
    have h3 := ih (s - 1) (by linarith) Measure.addHaar inferInstance
    have hp3 : ∀ b : hermC n, 0 ≤ detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1)) := fun b =>
      Real.rpow_nonneg (by linarith [GlobalTheory.T.one_le_detW_of_isHermitian _ _ (mem_hermC.1 b.2)]) _
    have h4 := (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hp3)).1 h3.2
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc)
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hK) h4)
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
