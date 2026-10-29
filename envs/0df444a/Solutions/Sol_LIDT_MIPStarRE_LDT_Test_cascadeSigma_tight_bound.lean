-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.cascadeSigma_tight_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:30:45.324749+00:00
-- url     : https://prove2.me/submissions/119f2d5e-b275-499d-8e42-923a6de2bb1f

-- Generated proof for MIPStarRE.LDT.Test.cascadeSigma_tight_bound.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Test
end LIDT.MIPStarRE.LDT.Test

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









/-- `1 ≤ k²`. -/
theorem k2_ge_one : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
  simpa using one_le_pow₀ (n := (2 : ℕ)) h.hk



/-- `m² ≤ m⁴`. -/
theorem m2_le_m4 : ((params.m : Error) ^ (2 : ℕ)) ≤ ((params.m : Error) ^ (4 : ℕ)) := by
  apply pow_le_pow_right₀ h.hm
  norm_num









end CascadeHypotheses

end Test

end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Error cascade — bounds for `σ` and `ζ₁`

This module proves the tight and absorbing bounds for the first two cascade
variables, `σ` and `ζ₁`.  The later variables `ζ₂`, `ζ₃`, and `ζ₄`, together
with the top-level consolidator `errorCascade_le_mainFormalError`, are in the
subsequent leaves of `Test.MainTheorem.ScalarBounds.CascadeBounds`.

The first cascade steps have three components:

* The **tight cascade bound** (`cascadeSigma_tight_bound`, `cascadeZeta1_bound`, …),
  deriving the native estimate directly from the cascade definition.
* The **absorbing bound** (`sigma_bound`, `zeta1_bound`, …), coarsening the
  tight estimate to the final `mainFormalEnvelope` envelope.
* The corresponding nonnegativity lemmas (`cascadeSigma_nonneg`,
  `cascadeZeta1_nonneg`), used by the later cascade estimates.

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

@[expose] public section


open scoped BigOperators

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem solution {params : _root_.LIDT.MIPStarRE.LDT.Parameters} {k : ℕ} {eps : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps) {ν : _root_.LIDT.MIPStarRE.LDT.Error}
    (hν : ν ≤ 10000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
        Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)))) :
    _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν ≤
      10000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) *
        _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (1024 : _root_.LIDT.MIPStarRE.LDT.Error) (80000 : _root_.LIDT.MIPStarRE.LDT.Error) := by
  unfold _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope
  set m2 : _root_.LIDT.MIPStarRE.LDT.Error := (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ) with hm2_def
  set m4 : _root_.LIDT.MIPStarRE.LDT.Error := (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ) with hm4_def
  set k2 : _root_.LIDT.MIPStarRE.LDT.Error := (k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)
  have hm2NN : 0 ≤ m2 := by positivity
  have hk2_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ k2 := h.k2_ge_one
  have hm2_le_m4 : m2 ≤ m4 := h.m2_le_m4
  have hm2_sq_m4 : m2 * m2 = m4 := by
    simp only [hm2_def, hm4_def]
    ring
  have hStep1 :
      m2 * ν ≤ 10000 * k2 * m4 *
        (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
          Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
    have hreorder :
        m2 * (10000 * k2 * m2 *
            (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)))) =
          10000 * k2 * (m2 * m2) *
            (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
      ring
    calc
      m2 * ν
          ≤ m2 * (10000 * k2 * m2 *
              (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
                Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)))) :=
            mul_le_mul_of_nonneg_left hν hm2NN
      _ = 10000 * k2 * (m2 * m2) *
            (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))) := hreorder
      _ = 10000 * k2 * m4 *
            (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))
                (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
            rw [hm2_sq_m4]
  have hScaleGeOne : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 10000 * k2 := by
    nlinarith [hk2_ge_one]
  have hm2_le_10k2m4 : m2 ≤ 10000 * k2 * m4 := by
    calc
      m2 ≤ m4 := hm2_le_m4
      _ ≤ (10000 * k2) * m4 := by
        nlinarith [hScaleGeOne, show 0 ≤ m4 by positivity]
      _ = 10000 * k2 * m4 := by ring
  have hStep2 :
      m2 * Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * m2))) ≤
        10000 * k2 * m4 * Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * m2))) := by
    have hExpNN : 0 ≤ Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * m2))) := Real.exp_nonneg _
    exact mul_le_mul_of_nonneg_right hm2_le_10k2m4 hExpNN
  have hExpand : m2 * (ν + Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * m2)))) =
      m2 * ν + m2 * Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * m2))) := by ring
  rw [hExpand]
  calc
    m2 * ν + m2 * Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * m2)))
        ≤ 10000 * k2 * m4 *
              (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
                Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))) +
            10000 * k2 * m4 * Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * m2))) := by
          nlinarith [hStep1, hStep2]
    _ = 10000 * k2 * m4 *
          (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
            Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
            Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * m2)))) := by ring
