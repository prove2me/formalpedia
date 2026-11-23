-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.DualLattice.ratBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:53.073927+00:00
-- url     : https://prove2.me/submissions/0a869831-f554-4d3c-95b7-dc66e96ffb0d

import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DualLatticeParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW GlobalTheory.CompanionTheory.SW.ThW.DualLattice
namespace GlobalTheory.CompanionTheory.SW.ThW.DualLattice
theorem _root_.solution {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (b : Module.Basis κ ℤ (𝓞 F)) (v : κ) : ratBasis b v = (b v : F) := by
  simp [ratBasis, Module.Basis.localizationLocalization_apply]
end GlobalTheory.CompanionTheory.SW.ThW.DualLattice
