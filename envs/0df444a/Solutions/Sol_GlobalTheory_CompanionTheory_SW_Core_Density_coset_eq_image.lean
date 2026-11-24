-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Density.coset_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:14:02.946829+00:00
-- url     : https://prove2.me/submissions/bbbb02eb-9d06-4da8-b7a5-1b90035f69c5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierInversionSchwartzBruhatStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PositiveDefiniteDensity

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
variable [IsTopologicalAddGroup V]
namespace GlobalTheory.CompanionTheory.SW.Core.Density
theorem _root_.solution (L : AddSubgroup V) (a : V) : coset L a = (fun x => x + a) '' (L : Set V) := by
  ext x
  constructor
  · intro h
    exact ⟨x - a, h, by simp⟩
  · rintro ⟨l, hl, rfl⟩
    simpa [coset] using hl
end GlobalTheory.CompanionTheory.SW.Core.Density
