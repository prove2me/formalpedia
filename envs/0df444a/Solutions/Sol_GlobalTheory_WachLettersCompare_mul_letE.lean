-- Prove2me | solution 1 for GlobalTheory.WachLettersCompare.mul_letE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:05.5161+00:00
-- url     : https://prove2.me/submissions/e4fb863c-eee3-481d-9ea5-62c6f6b07351

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_LettersFreeOfRank
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_WachLettersFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LetterSandwichOfFrobMatrices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.WachLettersCompare
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
attribute [local instance] letterModule
namespace GlobalTheory.WachLettersCompare
theorem _root_.solution (i : ZMod n) (a : LetA O n) : a * letE i = Pi.single i (a i) := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]
end GlobalTheory.WachLettersCompare
