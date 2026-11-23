-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.finite_latMod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:57.845841+00:00
-- url     : https://prove2.me/submissions/8871a5d5-6609-4e37-9753-7ea04e46a496

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
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}
omit [Algebra O LL] [IsScalarTower O LL V]
namespace GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions
theorem _root_.solution (L : _root_.Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (I : Ideal O) :
    Module.Finite (O ⧸ I) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.LatMod L I) := by
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.mpr L.fg
  exact Module.Finite.of_restrictScalars_finite O (O ⧸ I) _
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions
end GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions
