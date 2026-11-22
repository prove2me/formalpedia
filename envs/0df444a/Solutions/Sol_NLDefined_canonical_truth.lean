-- Prove2me | solution 1 for NLDefined.canonical_truth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:18:49.016818+00:00
-- url     : https://prove2.me/submissions/07747777-3d29-4cf9-91cd-d918da584744

import Std
import Definitions.Def_NLDefined
import Theorems.Thm_NLDefined_eval_formulaOps

set_option autoImplicit true
set_option autoImplicit false
open NLDefined
namespace NLDefined
theorem _root_.solution (Γ : Formula → Prop) (a : Formula) :
    (canonical Γ).D (eval (canonical Γ).op Formula.var a) ↔ Derives Γ a := by
  change Derives Γ (eval formulaOps Formula.var a) ↔ Derives Γ a
  rw [eval_formulaOps]
end NLDefined
