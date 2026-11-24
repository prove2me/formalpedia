-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.haar_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:00:04.396147+00:00
-- url     : https://prove2.me/submissions/0f847d53-aac5-4aaa-89f8-61ef857cf944

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianHaarBlockDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_continuous_blkEquiv
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_continuous_blkEquiv_symm

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
theorem _root_.solution (n : ℕ) (ν : Measure (hermC (n + 1))) (ν' : Measure (hermC n))
    (hν : ν.IsAddHaarMeasure) (hν' : ν'.IsAddHaarMeasure) :
    ∃ c : ENNReal, c ≠ ⊤ ∧ ∀ F : hermC (n + 1) → ENNReal, Measurable F →
      ∫⁻ b, F b ∂ν = c * ∫⁻ b', ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ, F (blk b' u d) ∂volume ∂volume ∂ν' := by
  haveI := hν
  haveI := hν'
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hp : (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hm : (Measure.map (blkEquiv n)
      (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ)))).IsAddHaarMeasure :=
    (blkEquiv n).isAddHaarMeasure_map _ (continuous_blkEquiv n) (continuous_blkEquiv_symm n)
  have he : Measurable (blkEquiv n) := (continuous_blkEquiv n).measurable
  refine ⟨(Measure.addHaarScalarFactor ν (Measure.map (blkEquiv n)
      (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ)))) : ENNReal),
    ENNReal.coe_ne_top, fun F hF => ?_⟩
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul ν (Measure.map (blkEquiv n)
      (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ))))]
  rw [lintegral_smul_measure, lintegral_map hF he, lintegral_prod (fun a => F (blkEquiv n a)) (hF.comp he).aemeasurable]
  simp only [ENNReal.smul_def, smul_eq_mul]
  congr 1
  refine lintegral_congr fun b' => ?_
  rw [lintegral_prod]
  · rfl
  · exact ((hF.comp he).comp measurable_prodMk_left).aemeasurable
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
