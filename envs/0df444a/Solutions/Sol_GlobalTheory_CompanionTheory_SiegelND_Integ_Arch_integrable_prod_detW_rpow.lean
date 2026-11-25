-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:01:15.746801+00:00
-- url     : https://prove2.me/submissions/2452b340-e9c9-440c-ae09-fd5949ee2239

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HuaDeterminantIntegrableOfLtStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductHuaDeterminantIntegrable
import Theorems.Thm_GlobalTheory_T_hua_determinant_integrable_of_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
theorem _root_.solution : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
    ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
    Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  intro W _ n s hs ν hν
  let μ₀ : Measure (hermC n) := Measure.addHaar
  have hf : ∀ _w : W, Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) μ₀ :=
    fun _ => GlobalTheory.T.hua_determinant_integrable_of_lt n s hs μ₀ inferInstance
  have hpi := Integrable.fintype_prod (μ := fun _ : W => μ₀)
    (f := fun _ : W => fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) hf
  rw [Measure.isAddLeftInvariant_eq_smul ν (Measure.pi fun _ : W => μ₀)]
  exact hpi.smul_measure_nnreal
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
