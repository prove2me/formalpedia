-- Prove2me | solution 1 for GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:14.420708+00:00
-- url     : https://prove2.me/submissions/415316b3-9e14-4c89-abfc-c1c55cdaf966

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Theorems.Thm_GlobalTheory_SmGL_isIrreducible_ofChar
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_ofChar_iff
import Theorems.Thm_GlobalTheory_SmGL_isUnitarisable_ofChar_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.BernsteinUnitaryProductIrreducible
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.Published.BernsteinUnitaryProductIrreducible
theorem _root_.solution (t : ℕ) {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    IsSmooth (detRep (Fin t) χ) ∧ (detRep (Fin t) χ).IsIrreducible ∧
      IsUnitarisable (detRep (Fin t) χ) :=
  ⟨(isSmooth_ofChar_iff _).2 hs.detChar, isIrreducible_ofChar _,
    (isUnitarisable_ofChar_iff _).2 fun _ => hu _⟩
end GlobalTheory.Published.BernsteinUnitaryProductIrreducible
