-- Prove2me | solution 1 for GlobalTheory.Survey.CrystallineCyclotomic.exists_crys
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:20:53.73555+00:00
-- url     : https://prove2.me/submissions/48f3c942-1520-4bb7-9e10-1992c76fa4b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_NonGaloisSurvey_CrystallineCyclotomic
import Theorems.Thm_GlobalTheory_Survey_CrystallineCyclotomic_isCrys_trivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Survey GlobalTheory.Survey.CrystallineCyclotomic
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
namespace GlobalTheory.Survey.CrystallineCyclotomic
theorem _root_.solution (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) :
    IsCrys (P.PD K) (Representation.trivial ↥LL.1 ↥(GK K) ↥LL.1) :=
  haveI := LL.2
  isCrys_trivial (P.PD K) ↥LL.1
end GlobalTheory.Survey.CrystallineCyclotomic
