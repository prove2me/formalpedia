-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreDensity.continuousOn_fib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:34.139824+00:00
-- url     : https://prove2.me/submissions/66d647bd-1149-4758-8b35-ff32d365fd70

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuousStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_integral_fib_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_re_facts
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_im_facts

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
theorem _root_.solution (hfin : ∀ b, IsLocallyFiniteMeasure (fib b))
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    {ψ : V → ℂ} (hc : Continuous ψ) (hs : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ g ⁻¹' B) :
    ContinuousOn (fun b => ∫ v, ψ v ∂(fib b)) B := by
  obtain ⟨r1, r2, r3⟩ := re_facts hc hs hsupp
  obtain ⟨i1, i2, i3⟩ := im_facts hc hs hsupp
  have hre := (h.2.2 _ r1 r2 r3).2
  have him := (h.2.2 _ i1 i2 i3).2
  simp_rw [integral_fib_eq hfin hc hs]
  exact (Complex.continuous_ofReal.comp_continuousOn hre).add
    ((Complex.continuous_ofReal.comp_continuousOn him).mul continuousOn_const)
end GlobalTheory.CompanionTheory.SW.FibreDensity
