-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.levN_mem_Nlev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:48:35.568909+00:00
-- url     : https://prove2.me/submissions/b1630b1d-5897-40d6-9703-41592eaf1bc4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_GradedSeries
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GradedSeries_serMul_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
open TensorProduct
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O)
namespace GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
theorem _root_.solution (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) :
    W.levN T i ζ x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.Nlev W T i ζ := by
  refine Submodule.subset_span ⟨1, W.levN T i ζ x, ⟨x, rfl⟩, ?_,
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul_one _).symm⟩
  obtain ⟨m, hm⟩ := W.levN_supp T i ζ x
  exact ⟨m, hm⟩
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
end GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
