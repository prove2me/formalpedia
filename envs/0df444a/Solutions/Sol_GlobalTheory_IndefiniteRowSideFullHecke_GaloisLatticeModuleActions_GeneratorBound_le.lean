-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.GeneratorBound.le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:52:12.769878+00:00
-- url     : https://prove2.me/submissions/f9596135-64fb-45c1-85b2-1ebf2dc73fc2

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BlochKatoGeneratorBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
namespace GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions
namespace GeneratorBound
theorem _root_.solution {PD : PeriodData G Qp K₀ K B BdR} {T : LocLat G Qp LL O} {ϖ : O}
    (h : GeneratorBound PD T ϖ) :
    GeneratedByAtMost (latticeFiniteCohomology PD T.L) ((Module.finrank Qp K + 1) * Module.finrank O ↥T.L.T) := by
  obtain ⟨⟨s, hs, hc⟩, h2⟩ := h
  exact ⟨s, hs, hc.trans h2⟩
end GeneratorBound
end GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions
