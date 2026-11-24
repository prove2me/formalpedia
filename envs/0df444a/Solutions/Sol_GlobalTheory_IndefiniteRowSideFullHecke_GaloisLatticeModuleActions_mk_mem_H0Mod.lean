-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.mk_mem_H0Mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:38:42.938424+00:00
-- url     : https://prove2.me/submissions/a0f6879f-3a16-4864-9258-d1ef34adb3fd

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BlochKatoGeneratorBound
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GaloisLatticeModuleActions_coe_latAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.coe_latAct

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions
theorem _root_.solution (L : _root_.Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (I : Ideal O)
    (x : ↥L.T) :
    (Submodule.Quotient.mk x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.LatMod L I) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.galoisLatticeModIdealInvariants L I ↔
      ∀ g : G, _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.latAct L g x - x ∈ I • (⊤ : Submodule O ↥L.T) := by
  change (∀ g : G, _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.latModAct L I g (Submodule.Quotient.mk x) =
    Submodule.Quotient.mk x) ↔ _
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.latModAct, Submodule.mapQ_apply, Submodule.Quotient.eq]
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions
end GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions
