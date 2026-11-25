-- Prove2me | solution 1 for GlobalTheory.FontCmp.dcrisTensor_of_comparison
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:12:21.085216+00:00
-- url     : https://prove2.me/submissions/11bc2b47-c844-478a-8a20-d632a4f43248

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv
import Theorems.Thm_GlobalTheory_FontCmp_range_eq
import Theorems.Thm_GlobalTheory_FontCmp_ker_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FontCmp
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
variable (LL : Type) [Field LL] [Algebra Qp LL]
namespace GlobalTheory.FontCmp
theorem _root_.solution (hc : CrystallineSubrepresentation.ComparisonBij PD LL) (ht : CrystallineSubrepresentation.TensorCrys PD LL) :
    TensorMultiplication.DcrisTensor PD LL := fun V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' h h' =>
  ⟨range_eq PD (hc V ρ h) (hc V' ρ' h') (hc _ _ (ht V ρ V' ρ' h h')),
    ker_eq PD (hc V ρ h) (hc V' ρ' h')⟩
end GlobalTheory.FontCmp
