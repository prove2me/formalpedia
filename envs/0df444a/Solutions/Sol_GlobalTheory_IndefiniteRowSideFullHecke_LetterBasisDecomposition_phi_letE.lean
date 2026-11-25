-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.phi_letE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:07:08.564804+00:00
-- url     : https://prove2.me/submissions/1590a33e-d0de-491c-a8ab-3ff3fa060b77

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_LettersFreeOfRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
attribute [local instance] letterModule
variable {W T}
variable (W T)
namespace GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition
theorem _root_.solution (i : ZMod n) : W.φA (letE (i - 1)) = letE i := by
  funext j
  by_cases h : j = i
  · subst h; simp [LocWach.φA, letφ, letE]
  · have h' : j - 1 ≠ i - 1 := fun e => h (sub_left_injective e)
    simp [LocWach.φA, letφ, letE, h, h']
end GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition
