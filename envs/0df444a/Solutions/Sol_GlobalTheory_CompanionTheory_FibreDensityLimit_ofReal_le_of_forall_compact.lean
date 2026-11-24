-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FibreDensityLimit.ofReal_le_of_forall_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:30:06.182905+00:00
-- url     : https://prove2.me/submissions/62ed6f23-fea3-4924-9120-161144bb10fa

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DisintegrationInjectiveOpenMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FibreDensityLimit
open Set
namespace GlobalTheory.CompanionTheory.FibreDensityLimit
theorem _root_.solution {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    {a b : X → ℝ} (ha : Continuous a) (hb : Continuous b) (c : ℝ)
    (h : ∀ A : Set X, IsCompact A → ∫⁻ s in A, ENNReal.ofReal (a s) ∂ν ≤
      ∫⁻ s in A, ENNReal.ofReal (b s) ∂ν + ENNReal.ofReal c * ν A) (s₀ : X) :
    ENNReal.ofReal (a s₀) ≤ ENNReal.ofReal (b s₀) + ENNReal.ofReal c := by
  by_contra hlt
  rw [not_le] at hlt
  have hFc : Continuous fun s => ENNReal.ofReal (a s) := ENNReal.continuous_ofReal.comp ha
  have hGc : Continuous fun s => ENNReal.ofReal (b s) + ENNReal.ofReal c :=
    (ENNReal.continuous_ofReal.comp hb).add continuous_const
  have hopen : IsOpen {s | ENNReal.ofReal (b s) + ENNReal.ofReal c < ENNReal.ofReal (a s)} :=
    isOpen_lt hGc hFc
  obtain ⟨A, hAn, hAW, hAc⟩ := local_compact_nhds (hopen.mem_nhds hlt)
  have hAm : MeasurableSet A := hAc.measurableSet
  have hpos : ν A ≠ 0 := (MeasureTheory.Measure.measure_pos_of_mem_nhds ν hAn).ne'
  have hsplit : ∫⁻ s in A, (ENNReal.ofReal (b s) + ENNReal.ofReal c) ∂ν =
      ∫⁻ s in A, ENNReal.ofReal (b s) ∂ν + ENNReal.ofReal c * ν A := by
    rw [lintegral_add_right _ measurable_const, setLIntegral_const]
  have hfin : ∫⁻ s in A, (ENNReal.ofReal (b s) + ENNReal.ofReal c) ∂ν ≠ ∞ := by
    have hbi : IntegrableOn b A ν := hb.continuousOn.integrableOn_compact hAc
    rw [hsplit]
    exact ENNReal.add_ne_top.mpr ⟨hbi.lintegral_lt_top.ne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAc.measure_lt_top.ne⟩
  have hstrict := setLIntegral_strict_mono hAm hpos hFc.measurable hfin
    (Filter.Eventually.of_forall fun s hs => hAW hs)
  rw [hsplit] at hstrict
  exact absurd (h A hAc) (not_le.mpr hstrict)
end GlobalTheory.CompanionTheory.FibreDensityLimit
