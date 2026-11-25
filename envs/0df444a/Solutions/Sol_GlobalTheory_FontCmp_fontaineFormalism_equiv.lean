-- Prove2me | solution 1 for GlobalTheory.FontCmp.fontaineFormalism_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:42:03.770898+00:00
-- url     : https://prove2.me/submissions/bc18442e-6d63-405d-864c-06bc2e69689d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv
import Theorems.Thm_GlobalTheory_FontCmp_formalism_iff
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CrystallineSubrepresentation_fontaineFormalism_iff


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
theorem _root_.solution : CrystallineSubrepresentation.FontaineFormalism l P ↔ TensorMultiplication.FontaineFormalism l P :=
  (CrystallineSubrepresentation.fontaineFormalism_iff l P).trans
    (forall₂_congr fun K LL => formalism_iff (P.PD K) ↥LL.1)
end GlobalTheory.FontCmp
