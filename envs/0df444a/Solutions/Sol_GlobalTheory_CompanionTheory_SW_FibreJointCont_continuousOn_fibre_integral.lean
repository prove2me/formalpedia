-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreJointCont.continuousOn_fibre_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:22:26.578163+00:00
-- url     : https://prove2.me/submissions/0c0d15b5-c232-4c22-a0a4-9a1e47c4d792

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUniqueStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuousStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GermFormPulledBackCombinationsExpandMonomials
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreJointCont_continuousOn_integral_of_bounded
import Theorems.Thm_GlobalTheory_T_fibre_family_integral_isContDensityOn
import Theorems.Thm_GlobalTheory_T_fibre_family_locallyFinite_measurable_bdd_on_compact


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreJointCont
namespace GlobalTheory.CompanionTheory.SW.FibreJointCont
theorem _root_.solution : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib → ∀ (P : Type) [TopologicalSpace P] (W : Set P) (Φ : P → V → ℝ), ContinuousOn (fun p : P × V => Φ p.1 p.2) (W ×ˢ Set.univ) → IsOpen W → ∀ C : Set V, IsCompact C → (∀ p ∈ W, ∀ v, v ∉ C → Φ p v = 0) → ContinuousOn (fun q : P × X => ∫ v, Φ q.1 v ∂(fib q.2)) (W ×ˢ B) := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hfg B hB fib hF P _ W Φ hΦ hW C hC hsupp
  obtain ⟨hloc, -, -, hbd⟩ := GlobalTheory.T.fibre_family_locallyFinite_measurable_bdd_on_compact V X Y μ ν f g ι hι hg hfg B hB fib hF
  refine continuousOn_integral_of_bounded fib B hB hloc hbd ?_ W Φ hΦ hW C hC hsupp
  intro φ hφ hφc
  have h := (GlobalTheory.T.fibre_family_integral_isContDensityOn V X Y μ ν f g ι hι hg hfg B hB fib hF (fun v => (φ v : ℂ))
    (Complex.continuous_ofReal.comp hφ) (hφc.comp_left Complex.ofReal_zero)).1.1
  have h2 : ContinuousOn (fun b => Complex.re (∫ v, ((φ v : ℝ) : ℂ) ∂(fib b))) B :=
    Complex.continuous_re.comp_continuousOn h
  refine h2.congr fun b _ => ?_
  have := integral_ofReal (μ := fib b) (𝕜 := ℂ) (f := φ)
  simp only [Complex.coe_algebraMap] at this
  show ∫ v, φ v ∂(fib b) = (∫ v, ((φ v : ℝ) : ℂ) ∂(fib b)).re
  rw [this]
  simp
end GlobalTheory.CompanionTheory.SW.FibreJointCont
