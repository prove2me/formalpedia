-- Prove2me | solution 1 for GlobalTheory.KSp.hasGauss_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:26:00.144013+00:00
-- url     : https://prove2.me/submissions/4028c421-fdfb-4b4e-978f-e4ad60378065

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasGaussIntegralCompAddEquivRescale
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory GlobalTheory.KSp
namespace GlobalTheory.KSp
theorem _root_.solution (X Y : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (μ : Measure X) (μ' : Measure Y)
    (T : X ≃ₜ+ Y) (r : NNReal) (f : Y → ℂ) (γ : ℂ) (hμ : μ.map T = r • μ') (h : HasGauss μ' f γ) :
    HasGauss μ (fun x => f (T x)) ((r : ℝ) * γ) := by
  intro K hK
  obtain ⟨L, hLc, hLo, hKL, hint⟩ := h (T '' K) (hK.image T.continuous)
  have hme : MeasurableEmbedding (T : X → Y) := T.toHomeomorph.measurableEmbedding
  have hset : ((L.comap (T.toAddEquiv.toAddMonoidHom) : AddSubgroup X) : Set X) = (T : X → Y) ⁻¹' (L : Set Y) := rfl
  refine ⟨L.comap T.toAddEquiv.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [hset]
    exact T.toHomeomorph.isCompact_preimage.2 hLc
  · rw [hset]
    exact hLo.preimage T.continuous
  · rw [hset]
    intro x hx
    exact hKL ⟨x, hx, rfl⟩
  · rw [hset, ← hme.setIntegral_map f (L : Set Y), hμ, Measure.restrict_smul, integral_smul_nnreal_measure, hint]
    simp [NNReal.smul_def]
end GlobalTheory.KSp
