-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Density.setIntegral_dens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:12:47.598129+00:00
-- url     : https://prove2.me/submissions/85f99654-3d28-4acf-9a67-11a829b9e6ed

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierInversionSchwartzBruhatStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PositiveDefiniteDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_coset_isOpen
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_coset_sb
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_integral_mul_dens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Density
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
variable [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [BorelSpace V]
namespace GlobalTheory.CompanionTheory.SW.Core.Density
theorem _root_.solution {χ : V → V → ℂ} {μ m : Measure V} [μ.IsAddHaarMeasure] [IsFiniteMeasure m]
    (h : NADual V χ μ) (hc : Continuous (fun p : V × V => χ p.1 p.2)) (hs : ∀ x y, χ x y = χ y x)
    (hn : ∀ x y, ‖χ x y‖ = 1) (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y)
    (hint : Integrable (mhat χ m) μ) {L : AddSubgroup V} (hK : IsCompact (L : Set V))
    (hO : IsOpen (L : Set V)) (a : V) :
    ∫ x in coset L a, dens χ μ m x ∂μ = ((m (coset L a)).toReal : ℂ) := by
  have hm : MeasurableSet (coset L a) := (coset_isOpen hO a).measurableSet
  have key := integral_mul_dens h hc hs hn ha hint (coset_sb hK hO a)
  have e : ∀ x, Set.indicator (coset L a) (fun _ => (1 : ℂ)) x * dens χ μ m x =
      Set.indicator (coset L a) (dens χ μ m) x := fun x => by
    by_cases hx : x ∈ coset L a <;> simp [hx]
  simp only [e] at key
  rw [integral_indicator hm, integral_indicator_const _ hm] at key
  rw [key]
  simp [Measure.real]
end GlobalTheory.CompanionTheory.SW.Core.Density
