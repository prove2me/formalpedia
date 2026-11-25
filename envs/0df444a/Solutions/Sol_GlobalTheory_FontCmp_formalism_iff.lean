-- Prove2me | solution 1 for GlobalTheory.FontCmp.formalism_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:26:22.41892+00:00
-- url     : https://prove2.me/submissions/f118ef4b-f73c-4cf9-8bbe-776b7e696ba7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv
import Theorems.Thm_GlobalTheory_FontCmp_inv_iff
import Theorems.Thm_GlobalTheory_FontCmp_dimLe_iff
import Theorems.Thm_GlobalTheory_FontCmp_comparison_iff
import Theorems.Thm_GlobalTheory_FontCmp_sub_iff
import Theorems.Thm_GlobalTheory_FontCmp_quot_iff
import Theorems.Thm_GlobalTheory_FontCmp_sum_iff
import Theorems.Thm_GlobalTheory_FontCmp_tensor_iff
import Theorems.Thm_GlobalTheory_FontCmp_dual_iff
import Theorems.Thm_GlobalTheory_FontCmp_exact_iff
import Theorems.Thm_GlobalTheory_FontCmp_letter_iff
import Theorems.Thm_GlobalTheory_FontCmp_dcrisTensor_of_comparison

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
theorem _root_.solution : CrystallineSubrepresentation.FormalismFor PD LL ↔ TensorMultiplication.FormalismAt PD LL :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i, j⟩ => ⟨(inv_iff PD).1 a, (dimLe_iff PD LL).1 b,
      (comparison_iff PD LL).1 c, (sub_iff PD LL).1 d, (quot_iff PD LL).1 e, (sum_iff PD LL).1 f,
      (tensor_iff PD LL).1 g, (dual_iff PD LL).1 h, (exact_iff PD LL).1 i,
      dcrisTensor_of_comparison PD LL c g, (letter_iff PD LL).1 j⟩,
    fun ⟨a, b, c, d, e, f, g, h, i, _, j⟩ => ⟨(inv_iff PD).2 a, (dimLe_iff PD LL).2 b,
      (comparison_iff PD LL).2 c, (sub_iff PD LL).2 d, (quot_iff PD LL).2 e, (sum_iff PD LL).2 f,
      (tensor_iff PD LL).2 g, (dual_iff PD LL).2 h, (exact_iff PD LL).2 i, (letter_iff PD LL).2 j⟩⟩
end GlobalTheory.FontCmp
