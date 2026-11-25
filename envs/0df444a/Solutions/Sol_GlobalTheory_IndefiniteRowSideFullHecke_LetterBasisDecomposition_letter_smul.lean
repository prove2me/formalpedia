-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letter_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:59:29.544858+00:00
-- url     : https://prove2.me/submissions/263db14d-5bd6-45f4-a99d-09c0b4c921e5

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
open Module
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O)
attribute [local instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letterModule
namespace GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition
theorem _root_.solution (i : ZMod n) (c : PowerSeries O)
    (x : ↥(W.Nl T i)) :
    ((c • x : ↥(W.Nl T i)) : W.DD T) = (Pi.single i c : _root_.Formalism.BasicNotions.LetA O n) • (x : W.DD T) := by
  obtain ⟨x, hx⟩ := x
  have hx' : x ∈ Submodule.map (_root_.Formalism.BasicNotions.letE i • LinearMap.id) (W.N T) := hx
  obtain ⟨y, -, rfl⟩ := Submodule.mem_map.mp hx'
  change (Pi.constRingHom (ZMod n) (PowerSeries O) c : _root_.Formalism.BasicNotions.LetA O n) • ((_root_.Formalism.BasicNotions.letE i : _root_.Formalism.BasicNotions.LetA O n) • y) =
    (Pi.single i c : _root_.Formalism.BasicNotions.LetA O n) • ((_root_.Formalism.BasicNotions.letE i : _root_.Formalism.BasicNotions.LetA O n) • y)
  rw [smul_smul, smul_smul]
  congr 1
  unfold _root_.Formalism.BasicNotions.letE
  ext j : 1
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_apply, h]
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition
end GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition
