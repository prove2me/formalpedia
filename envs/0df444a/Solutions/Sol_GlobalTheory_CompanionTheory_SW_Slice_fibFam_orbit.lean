-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Slice.fibFam_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:18.779613+00:00
-- url     : https://prove2.me/submissions/c9299f48-5d87-4c78-86d7-ed1f9aa8d026

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormula

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Slice
variable {V X Q : Type} [TopologicalSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
  [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
  [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X]
namespace GlobalTheory.CompanionTheory.SW.Slice
theorem _root_.solution {g : V → X} {b₀ : X} (w : Q → ℝ≥0) (m : Measure (g ⁻¹' {b₀}))
    (ho : Function.Injective (fun q : Q => q • b₀)) (q : Q) :
    fibFam g b₀ w m (q • b₀) = (w q : ℝ≥0∞) • m.map (fun z : (g ⁻¹' {b₀}) => q • (z : V)) := by
  have h : Function.invFun (fun q : Q => q • b₀) (q • b₀) = q :=
    Function.leftInverse_invFun ho q
  rw [fibFam, if_pos ⟨q, rfl⟩, h]
end GlobalTheory.CompanionTheory.SW.Slice
