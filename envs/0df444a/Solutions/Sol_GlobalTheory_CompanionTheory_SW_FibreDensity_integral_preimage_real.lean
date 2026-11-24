-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreDensity.integral_preimage_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:30:23.595924+00:00
-- url     : https://prove2.me/submissions/eedb7a10-337d-40f6-85e1-f8ff99e274f5

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuousStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_integral_preimage_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreDensity
variable {V X Y : Type}
  [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y} {B : Set X}
  {fib : X → Measure V}
namespace GlobalTheory.CompanionTheory.SW.FibreDensity
theorem _root_.solution [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ]
    (hfin : ∀ b, IsLocallyFiniteMeasure (fib b))
    (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v)) (hg : Continuous g)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    {S : Set X} (hS : IsCompact S) (hSB : S ⊆ B) {u : V → ℝ} (hc : Continuous u)
    (hs : HasCompactSupport u) (hsupp : tsupport u ⊆ g ⁻¹' B) :
    ∫ v in g ⁻¹' S, u v ∂μ = ∫ b in S, ∫ v, u v ∂(fib b) ∂ν := by
  set p : V → ℝ := fun v => max (u v) 0 with hp
  set q : V → ℝ := fun v => max (-u v) 0 with hq
  have hpc : Continuous p := hc.max continuous_const
  have hqc : Continuous q := hc.neg.max continuous_const
  have hps : Function.support p ⊆ Function.support u := by
    intro v hv hv0
    exact hv (by simp [hp, show u v = 0 from hv0])
  have hqs : Function.support q ⊆ Function.support u := by
    intro v hv hv0
    exact hv (by simp [hq, show u v = 0 from hv0])
  have hpK : HasCompactSupport p := hs.mono hps
  have hqK : HasCompactSupport q := hs.mono hqs
  have hpt : tsupport p ⊆ g ⁻¹' B := (closure_mono hps).trans hsupp
  have hqt : tsupport q ⊆ g ⁻¹' B := (closure_mono hqs).trans hsupp
  have hsplit : ∀ v, u v = p v - q v := fun v => by
    simp only [hp, hq]
    rcases le_total (u v) 0 with h1 | h1
    · rw [max_eq_right h1, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h1, max_eq_right (by linarith)]; ring
  have hP := integral_preimage_nonneg hfin hι hf hg h hS hSB hpc hpK hpt
    (fun v => le_max_right _ _)
  have hQ := integral_preimage_nonneg hfin hι hf hg h hS hSB hqc hqK hqt
    (fun v => le_max_right _ _)
  have hIp : Integrable p μ := hpc.integrable_of_hasCompactSupport hpK
  have hIq : Integrable q μ := hqc.integrable_of_hasCompactSupport hqK
  have hGp : IntegrableOn (fun b => ∫ v, p v ∂(fib b)) S ν :=
    ((h.2.2 p hpc hpK hpt).2.mono hSB).integrableOn_compact hS
  have hGq : IntegrableOn (fun b => ∫ v, q v ∂(fib b)) S ν :=
    ((h.2.2 q hqc hqK hqt).2.mono hSB).integrableOn_compact hS
  have hb : ∀ b, ∫ v, u v ∂(fib b) = ∫ v, p v ∂(fib b) - ∫ v, q v ∂(fib b) := fun b => by
    haveI := hfin b
    simp_rw [hsplit]
    exact integral_sub (hpc.integrable_of_hasCompactSupport hpK)
      (hqc.integrable_of_hasCompactSupport hqK)
  simp_rw [hb]
  rw [integral_sub hGp hGq, ← hP, ← hQ, ← integral_sub hIp.integrableOn hIq.integrableOn]
  simp_rw [hsplit]
end GlobalTheory.CompanionTheory.SW.FibreDensity
