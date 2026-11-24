-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramNear.fibre_on_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:22:27.226612+00:00
-- url     : https://prove2.me/submissions/17128df9-3ca5-4bbe-9c91-61863bc0f2e0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentitiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOrbitLocalSectionSubgroupStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarModularCharacterOfContinuousActionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureDisintegrationFormula
import Theorems.Thm_GlobalTheory_T_exists_fibre_family_on_open_orbit
import Theorems.Thm_GlobalTheory_T_haar_modular_character_of_continuous_action


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramNear
namespace GlobalTheory.CompanionTheory.SW.GramNear
theorem _root_.solution (V X Y : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [IsTopologicalAddGroup V]
    [AddCommGroup X] [TopologicalSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] [IsTopologicalAddGroup X]
    (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v))
    (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
    [SecondCountableTopology Q] [T2Space Q] [DistribMulAction Q V] [ContinuousSMul Q V]
    [DistribMulAction Q X] [ContinuousSMul Q X]
    (heq : ∀ (q : Q) (v : V), g (q • v) = q • g v) (b₀ : X)
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) :
    ∃ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' (Set.range fun q : Q => q • b₀)) ν
      (Set.range fun q : Q => q • b₀) fib := by
  obtain ⟨χ, hχ, hμ⟩ := GlobalTheory.T.haar_modular_character_of_continuous_action V μ Q
  obtain ⟨χ', hχ', hν⟩ := GlobalTheory.T.haar_modular_character_of_continuous_action X ν Q
  exact GlobalTheory.T.exists_fibre_family_on_open_orbit V X Y μ ν f g ι hι hg hf Q heq χ χ' hχ hχ' hμ hν b₀ ho
end GlobalTheory.CompanionTheory.SW.GramNear
