-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.coe_latAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:17.414465+00:00
-- url     : https://prove2.me/submissions/96f138b6-71c4-41ed-b6b7-cb4a9a95d768

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions
theorem _root_.solution (L : Lattice (O := O) ρ) (g : G) (x : ↥L.T) :
    (latAct L g x : V) = ρ g (x : V) := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions
