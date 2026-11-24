-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisPar.isCh_of_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:08:26.632737+00:00
-- url     : https://prove2.me/submissions/fb6cde19-03a5-4a2e-b91d-954e731ac924

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicLawOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisPar
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]
namespace GlobalTheory.CompanionTheory.RgEisPar
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] {Γ P : Subgroup G} {c : G → ℂ} (h : IsCh Γ ⊤ c) : IsCh Γ P c where
  mul := fun p _ q _ => h.mul p trivial q trivial
  norm := fun p _ => h.norm p trivial
  rat := fun γ hγ _ => h.rat γ hγ trivial
  cont := (h.cont.mono (Set.subset_univ _ |>.trans (by simp)))
end GlobalTheory.CompanionTheory.RgEisPar
