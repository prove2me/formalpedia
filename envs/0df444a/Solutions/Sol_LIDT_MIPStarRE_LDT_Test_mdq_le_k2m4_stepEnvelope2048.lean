-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.mdq_le_k2m4_stepEnvelope2048
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:40:46.077897+00:00
-- url     : https://prove2.me/submissions/a0f75cf1-fd8d-4deb-a089-4eb9c91ac4d9

-- Generated proof for MIPStarRE.LDT.Test.mdq_le_k2m4_stepEnvelope2048.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
import Mathlib

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean. -/
/-!
# Error cascade — core definitions

This module defines the central error quantities `mainFormalError`,
`mainFormalEnvelope`, the cascade variables `σ`, `ζ₁`, `ζ₂`, `ζ₃`, `ζ₄`,
and the `CascadeHypotheses` numeric regime used throughout the error-cascade
bookkeeping for Step 8 of `mainFormal`.

Note: this module contributes declarations to the comparator statement closure
of `mainFormal`, which must elaborate in the same environment as the
Mathlib-only `Challenge.lean`.  Keep the full `import Mathlib`; do not narrow
it.  See `docs/comparator.md`, "Environment alignment".

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test



























namespace CascadeHypotheses

variable {params : Parameters} {k : ℕ} {eps : Error}
variable (h : CascadeHypotheses params k eps)

include h

/-- Non-negativity of `d/q` under the standing hypotheses. -/
theorem dqNN : 0 ≤ (params.d : Error) / (params.q : Error) :=
  div_nonneg (Nat.cast_nonneg _) h.hqPos.le

/-- `d/q ≤ 1` under the standing hypotheses. -/
theorem dqLeOne : (params.d : Error) / (params.q : Error) ≤ 1 :=
  (div_le_one h.hqPos).mpr h.hdq





/-- `1 ≤ k²`. -/
theorem k2_ge_one : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
  simpa using one_le_pow₀ (n := (2 : ℕ)) h.hk



/-- `m² ≤ m⁴`. -/
theorem m2_le_m4 : ((params.m : Error) ^ (2 : ℕ)) ≤ ((params.m : Error) ^ (4 : ℕ)) := by
  apply pow_le_pow_right₀ h.hm
  norm_num



/-- `m ≤ m⁴`. -/
theorem m_le_m4 : (params.m : Error) ≤ ((params.m : Error) ^ (4 : ℕ)) := by
  have hm2_ge : (params.m : Error) ≤ ((params.m : Error) ^ (2 : ℕ)) := by
    have hm_nn : 0 ≤ (params.m : Error) := by linarith [h.hm]
    have : (params.m : Error) * 1 ≤ (params.m : Error) * (params.m : Error) :=
      mul_le_mul_of_nonneg_left h.hm hm_nn
    simpa [sq] using this
  exact hm2_ge.trans h.m2_le_m4





end CascadeHypotheses

end Test

end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean. -/
/-!
# Error cascade — envelope and root bounding machinery

Internal helper lemmas for the error-cascade bookkeeping of Step 8.
These provide the step-envelope interpolation (`stepEnvelope`),
monotonicity under denominator enlargement, square-root scaling, and
explicit numeric bounds on various `rpow` and `sqrt` expressions.
All lemmas are technical and should not be part of downstream API.

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test









theorem stepEnvelope_nonneg {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n N : Error} :
    0 ≤ stepEnvelope params k eps n N := by
  unfold stepEnvelope
  refine add_nonneg (add_nonneg (Real.rpow_nonneg h.hepsNN _) ?_) (Real.exp_nonneg _)
  exact Real.rpow_nonneg h.dqNN _













theorem self_le_rpow_one_div {x : Error} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {n : Error} (hn : 1 ≤ n) :
    x ≤ Real.rpow x (1 / n) := by
  have hnPos : 0 < n := by linarith
  have hdiv : 1 / n ≤ (1 : Error) := by
    field_simp [hnPos.ne']
    linarith
  simpa [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_ge' hx hx1 (show 0 ≤ 1 / n by positivity) hdiv)

theorem m_le_k2m4_aux {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    (params.m : Error) ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
  calc
    (params.m : Error) ≤ ((params.m : Error) ^ (4 : ℕ)) := h.m_le_m4
    _ = 1 * ((params.m : Error) ^ (4 : ℕ)) := by ring
    _ ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
      exact mul_le_mul_of_nonneg_right h.k2_ge_one (by positivity)

theorem dq_le_rpow2048 {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    (params.d : Error) / (params.q : Error) ≤
      Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2048 : Error)) :=
  self_le_rpow_one_div h.dqNN h.dqLeOne (by norm_num)

theorem dq_rpow2048_le_stepEnvelope2048 {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2048 : Error)) ≤
      stepEnvelope params k eps (2048 : Error) (160000 : Error) := by
  unfold stepEnvelope
  have hepsNN' : 0 ≤ Real.rpow eps (1 / (2048 : Error)) := Real.rpow_nonneg h.hepsNN _
  have hExpNN' :
      0 ≤ Real.exp (-((k : Error) / ((160000 : Error) * ((params.m : Error) ^ (2 : ℕ))))) :=
    Real.exp_nonneg _
  exact (le_add_of_nonneg_left hepsNN').trans (le_add_of_nonneg_right hExpNN')









































end Test

end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Error cascade — envelope and root bounding machinery

Internal helper lemmas for the error-cascade bookkeeping of Step 8.
These provide the step-envelope interpolation (`stepEnvelope`),
monotonicity under denominator enlargement, square-root scaling, and
explicit numeric bounds on various `rpow` and `sqrt` expressions.
All lemmas are technical and should not be part of downstream API.

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

@[expose] public section

open scoped BigOperators

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem solution {params : _root_.LIDT.MIPStarRE.LDT.Parameters} {k : ℕ} {eps : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps) :
    (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
      ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) *
        _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error) := by
  have hTNN : 0 ≤ _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error) :=
    _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_nonneg (h := h) (n := (2048 : _root_.LIDT.MIPStarRE.LDT.Error)) (N := (160000 : _root_.LIDT.MIPStarRE.LDT.Error))
  have hdq_to_T :
      (params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) ≤
        _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error) :=
    (_root_.LIDT.MIPStarRE.LDT.Test.dq_le_rpow2048 h).trans (_root_.LIDT.MIPStarRE.LDT.Test.dq_rpow2048_le_stepEnvelope2048 h)
  have hmdq_to_mT : (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
      (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error) :=
    mul_le_mul_of_nonneg_left hdq_to_T (Nat.cast_nonneg params.m)
  have hmT : (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error) ≤
      (((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ))) *
        _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error) :=
    mul_le_mul_of_nonneg_right (_root_.LIDT.MIPStarRE.LDT.Test.m_le_k2m4_aux (h := h)) hTNN
  exact hmdq_to_mT.trans hmT
