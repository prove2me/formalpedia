-- Prove2me | solution 1 for GlobalTheory.FontCmp.fontaineFormalismTensor_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:56:44.261254+00:00
-- url     : https://prove2.me/submissions/9070d00a-86c2-4bdc-93e7-65688be06959

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv
import Theorems.Thm_GlobalTheory_FontCmp_dcrisTensor_letters
import Theorems.Thm_GlobalTheory_FontCmp_fontaineFormalism_equiv

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
variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)
namespace GlobalTheory.FontCmp
theorem _root_.solution :
    CrystallineSubrepresentation.FontaineFormalismTensor l P ↔ TensorMultiplication.FontaineFormalism l P :=
  ⟨fun h => (fontaineFormalism_equiv l P).1 h.1, fun h => ⟨(fontaineFormalism_equiv l P).2 h,
    fun K LL => by
      haveI := (P.PD K).finK₀
      exact dcrisTensor_letters (P.PD K) ↥LL.1 (h K LL).2.2.2.2.2.2.2.2.2.1⟩⟩
end GlobalTheory.FontCmp
