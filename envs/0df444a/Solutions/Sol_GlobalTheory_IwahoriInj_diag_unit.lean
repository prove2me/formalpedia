-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.diag_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:31.946311+00:00
-- url     : https://prove2.me/submissions/81cf23c2-7ed9-4903-9770-640696aa1e5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_GlobalTheory_IwahoriInj_deep_one_iff
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.IwahoriInj
theorem _root_.solution {f : n → n → ℤ} (hf : Chamber f) {p : GL n k} {i : n}
    (h1 : ∀ l, Deep (f i l) (p.val i l)) (h2 : ∀ l, Deep (f l i) ((p⁻¹).val l i)) :
    ¬ Deep 1 (p.val i i) := by
  intro h
  have h3 : Deep 1 ((p.val * (p⁻¹).val) i i) := by
    rw [mul_apply]
    refine Deep.sum fun l _ => ?_
    by_cases c : l = i
    · subst c
      exact (h.mul (h2 l)).mono (by rw [hf.1.1]; omega)
    · exact ((h1 l).mul (h2 l)).mono (hf.2 i l (Ne.symm c)).ge
  simp [deep_one_iff] at h3
end GlobalTheory.IwahoriInj
