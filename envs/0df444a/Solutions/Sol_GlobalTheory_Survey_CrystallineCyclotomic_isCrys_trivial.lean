-- Prove2me | solution 1 for GlobalTheory.Survey.CrystallineCyclotomic.isCrys_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:13:42.054298+00:00
-- url     : https://prove2.me/submissions/736731ff-d1c9-4820-b8ff-fdb8b83a8a1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_NonGaloisSurvey_CrystallineCyclotomic
import Theorems.Thm_GlobalTheory_Survey_CrystallineCyclotomic_nontrivial_B
import Theorems.Thm_GlobalTheory_Survey_CrystallineCyclotomic_dcris_trivial

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
theorem _root_.solution [FiniteDimensional Qp LL] : IsCrys PD (Representation.trivial LL G LL) := by
  haveI := nontrivial_B PD
  haveI := PD.finK₀
  unfold IsCrys
  rw [dcris_trivial, LinearMap.finrank_range_of_inj]
  · simp
  · exact Module.Flat.lTensor_preserves_injective_linearMap (M := LL)
      (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap (algebraMap K₀ B).injective
end GlobalTheory.Survey.CrystallineCyclotomic
