-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.cascadeZeta4_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:12:25.43158+00:00
-- url     : https://prove2.me/submissions/125d5855-bbe8-4fef-90d1-c44b4d466fb5

-- Generated proof for MIPStarRE.LDT.Test.cascadeZeta4_bound.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_cascadeSigma_tight_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_cascadeZeta1_bound_general
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_cascadeZeta1_bound_special
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_cascadeZeta3_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_sqrt_scaled_stepEnvelope_le

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

/-- Non-negativity of `d/q` under the standing hypotheses. -/
theorem dqNN : 0 ≤ (params.d : Error) / (params.q : Error) :=
  div_nonneg (Nat.cast_nonneg _) h.hqPos.le

/-- `d/q ≤ 1` under the standing hypotheses. -/
theorem dqLeOne : (params.d : Error) / (params.q : Error) ≤ 1 :=
  (div_le_one h.hqPos).mpr h.hdq









/-- `m² ≤ m⁴`. -/
theorem m2_le_m4 : ((params.m : Error) ^ (2 : ℕ)) ≤ ((params.m : Error) ^ (4 : ℕ)) := by
  apply pow_le_pow_right₀ h.hm
  norm_num

/-- `k ≤ k²`. -/
theorem k_le_k2 : (k : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
  have hk_nn : 0 ≤ (k : Error) := by linarith [h.hk]
  have : (k : Error) * 1 ≤ (k : Error) * (k : Error) :=
    mul_le_mul_of_nonneg_left h.hk hk_nn
  simpa [sq] using this



/-- `k m² ≤ k² m⁴`. -/
theorem km2_le_k2m4 : (k : Error) * ((params.m : Error) ^ (2 : ℕ)) ≤
    ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) :=
  mul_le_mul h.k_le_k2 h.m2_le_m4 (by positivity) (by positivity)



end CascadeHypotheses

end Test

end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/SigmaZeta1.lean. -/
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

namespace MIPStarRE.LDT

namespace Test





theorem cascadeSigma_nonneg {params : Parameters} {k : ℕ} {ν : Error}
    (hνNN : 0 ≤ ν) :
    0 ≤ cascadeSigma params k ν := by
  unfold cascadeSigma
  positivity

theorem cascadeZeta1_nonneg {params : Parameters} {k : ℕ} {eps ν : Error}
    (h : CascadeHypotheses params k eps) (hνNN : 0 ≤ ν) :
    0 ≤ cascadeZeta1 params eps (cascadeSigma params k ν) := by
  have hσNN := cascadeSigma_nonneg (params := params) (k := k) (ν := ν) hνNN
  unfold cascadeZeta1
  positivity [hσNN, h.hepsNN, h.dqNN]





theorem cascadeZeta1_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeZeta1 params eps (cascadeSigma params k ν) ≤
      20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (2048 : Error) (160000 : Error) := by
  by_cases hkm1 : k = 1 ∧ params.m = 1
  · exact cascadeZeta1_bound_special (h := h) (ν := ν) hν hkm1
  · exact cascadeZeta1_bound_general (h := h) (ν := ν) hν hkm1



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





/-- For `x ∈ [0, 1]`, enlarging the denominator in `x^(1/n)` makes the
exponent smaller and therefore the value larger. -/
theorem rpow_le_of_denom_le {x : Error} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {n₁ n₂ : Error} (hn₁Pos : 0 < n₁) (hn : n₁ ≤ n₂) :
    Real.rpow x (1 / n₁) ≤ Real.rpow x (1 / n₂) := by
  have hn₂Pos : 0 < n₂ := lt_of_lt_of_le hn₁Pos hn
  have hdiv : 1 / n₂ ≤ 1 / n₁ := one_div_le_one_div_of_le hn₁Pos hn
  exact Real.rpow_le_rpow_of_exponent_ge' hx hx1 (show 0 ≤ 1 / n₂ by positivity) hdiv

/-- For `k ≥ 0`, `m > 0`, and `N₁ ≤ N₂`, the larger decay denominator gives
the weaker exponential bound `exp(-k/(N₁ m²)) ≤ exp(-k/(N₂ m²))`. -/
theorem exp_neg_le_of_denom_ge (k : ℕ) (m : Error) (hm : 0 < m)
    {N₁ N₂ : Error} (h₁ : 0 < N₁) (h₁₂ : N₁ ≤ N₂) :
    Real.exp (-((k : Error) / (N₁ * m ^ (2 : ℕ)))) ≤
      Real.exp (-((k : Error) / (N₂ * m ^ (2 : ℕ)))) := by
  have hm2 : 0 < m ^ (2 : ℕ) := by positivity
  have hN₁m : 0 < N₁ * m ^ 2 := mul_pos h₁ hm2
  have hknn : (0 : Error) ≤ (k : Error) := Nat.cast_nonneg _
  have hratio : (k : Error) / (N₂ * m ^ 2) ≤ (k : Error) / (N₁ * m ^ 2) := by
    apply div_le_div_of_nonneg_left hknn hN₁m
    exact mul_le_mul_of_nonneg_right h₁₂ hm2.le
  exact Real.exp_le_exp.mpr (neg_le_neg hratio)

theorem stepEnvelope_nonneg {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n N : Error} :
    0 ≤ stepEnvelope params k eps n N := by
  unfold stepEnvelope
  refine add_nonneg (add_nonneg (Real.rpow_nonneg h.hepsNN _) ?_) (Real.exp_nonneg _)
  exact Real.rpow_nonneg h.dqNN _

theorem stepEnvelope_le_stepEnvelope {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n₁ n₂ N₁ N₂ : Error}
    (hn₁Pos : 0 < n₁) (hn : n₁ ≤ n₂) (hN₁Pos : 0 < N₁) (hN : N₁ ≤ N₂) :
    stepEnvelope params k eps n₁ N₁ ≤ stepEnvelope params k eps n₂ N₂ := by
  unfold stepEnvelope
  have hEps := rpow_le_of_denom_le h.hepsNN h.hepsOne hn₁Pos hn
  have hDq := rpow_le_of_denom_le h.dqNN h.dqLeOne hn₁Pos hn
  have hmPos : 0 < (params.m : Error) := by linarith [h.hm]
  have hExp := exp_neg_le_of_denom_ge k (params.m : Error) hmPos hN₁Pos hN
  linarith



























theorem sqrt20204_le_143 : Real.sqrt (20204 : Error) ≤ 143 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num

theorem sqrt150000_le_388 : Real.sqrt (150000 : Error) ≤ 388 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num





























end Test

end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Error cascade — bound for `ζ₄`

This module contains the `ζ₄` cascade estimate used in Step 8 of the main
inductive step and its absorption into `mainFormalError`.

## References

* `references/ldt-paper/inductive_step.tex`, lines 220--228.
-/

@[expose] public section

open scoped BigOperators

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem solution {params : _root_.LIDT.MIPStarRE.LDT.Parameters} {k : ℕ} {eps : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps) {ν : _root_.LIDT.MIPStarRE.LDT.Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
        Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)))) :
    _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta4 (_root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν)
        (_root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps (_root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν))
        (_root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta3
          (_root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps (_root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν))
          (_root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta2 (_root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps (_root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν)))) ≤
      40000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) *
        _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (32768 : _root_.LIDT.MIPStarRE.LDT.Error) (2560000 : _root_.LIDT.MIPStarRE.LDT.Error) := by
  set σ : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν
  set Z1 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps σ
  set Z2 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta2 Z1
  set Z3 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta3 Z1 Z2
  set k2 : _root_.LIDT.MIPStarRE.LDT.Error := (k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)
  set m2 : _root_.LIDT.MIPStarRE.LDT.Error := (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)
  set m4 : _root_.LIDT.MIPStarRE.LDT.Error := (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)
  set E1024 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (1024 : _root_.LIDT.MIPStarRE.LDT.Error) (80000 : _root_.LIDT.MIPStarRE.LDT.Error)
  set E2048 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error)
  set E4096 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (4096 : _root_.LIDT.MIPStarRE.LDT.Error) (320000 : _root_.LIDT.MIPStarRE.LDT.Error)
  set E16384 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (16384 : _root_.LIDT.MIPStarRE.LDT.Error) (1280000 : _root_.LIDT.MIPStarRE.LDT.Error)
  set E32768 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (32768 : _root_.LIDT.MIPStarRE.LDT.Error) (2560000 : _root_.LIDT.MIPStarRE.LDT.Error)
  have hE2048NN : 0 ≤ E2048 := by
    simpa [E2048] using _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_nonneg (h := h) (n := (2048 : _root_.LIDT.MIPStarRE.LDT.Error)) (N := (160000 : _root_.LIDT.MIPStarRE.LDT.Error))
  have hE4096NN : 0 ≤ E4096 := by
    simpa [E4096] using _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_nonneg (h := h) (n := (4096 : _root_.LIDT.MIPStarRE.LDT.Error)) (N := (320000 : _root_.LIDT.MIPStarRE.LDT.Error))
  have hE16384NN : 0 ≤ E16384 := by
    simpa [E16384] using
      _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_nonneg (h := h) (n := (16384 : _root_.LIDT.MIPStarRE.LDT.Error)) (N := (1280000 : _root_.LIDT.MIPStarRE.LDT.Error))
  have hE32768NN : 0 ≤ E32768 := by
    simpa [E32768] using
      _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_nonneg (h := h) (n := (32768 : _root_.LIDT.MIPStarRE.LDT.Error)) (N := (2560000 : _root_.LIDT.MIPStarRE.LDT.Error))
  have hσ : σ ≤ 10000 * k2 * m4 * E1024 := by
    simpa [σ, k2, m4, E1024] using _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma_tight_bound (h := h) (ν := ν) hν
  have hσ' : σ ≤ 10000 * k2 * m4 * E32768 := by
    calc
      σ ≤ 10000 * k2 * m4 * E1024 := hσ
      _ ≤ 10000 * k2 * m4 * E32768 := by
        have hMono : E1024 ≤ E32768 := by
          simpa [E1024, E32768] using _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_le_stepEnvelope (h := h)
            (n₁ := (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) (n₂ := (32768 : _root_.LIDT.MIPStarRE.LDT.Error)) (N₁ := (80000 : _root_.LIDT.MIPStarRE.LDT.Error))
            (N₂ := (2560000 : _root_.LIDT.MIPStarRE.LDT.Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
            (hN₁Pos := by norm_num) (hN := by norm_num)
        exact mul_le_mul_of_nonneg_left hMono (by positivity)
  have hZ1_raw := _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1_bound (h := h) (ν := ν) hν
  have hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048 := by
    simpa [σ, Z1, k2, m4, E2048] using hZ1_raw
  have hZ3_raw := _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta3_bound (h := h) (ν := ν) hνNN hν
  have hZ3 : Z3 ≤ 150000 * k2 * m4 * E16384 := by
    simpa [σ, Z1, Z2, Z3, k2, m4, E16384] using hZ3_raw
  have hZ1NN : 0 ≤ Z1 := by
    simpa [σ, Z1] using _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1_nonneg (h := h) (ν := ν) hνNN
  have hZ2NN : 0 ≤ Z2 := by
    unfold Z2 _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta2
    refine add_nonneg ?_ ?_
    · exact mul_nonneg (by norm_num) (Real.rpow_nonneg hZ1NN _)
    · exact mul_nonneg (by norm_num) (Real.rpow_nonneg hZ1NN _)
  have hZ3NN : 0 ≤ Z3 := by
    unfold Z3 _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta3
    exact add_nonneg (mul_nonneg (by norm_num) hZ1NN) (mul_nonneg (by norm_num) hZ2NN)
  have hX1NN : 0 ≤ 20204 * k2 * m4 * E2048 := by
    positivity [hE2048NN]
  have hsqrtZ1 : Real.sqrt (20204 * k2 * m4 * E2048) ≤ 143 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E4096 := by
    calc
      Real.sqrt (20204 * k2 * m4 * E2048)
        ≤ Real.sqrt (20204 : _root_.LIDT.MIPStarRE.LDT.Error) * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E4096 := by
          simpa [k2, m2, m4, E2048, E4096,
            show (2 : _root_.LIDT.MIPStarRE.LDT.Error) * 2048 = 4096 by norm_num,
            show (2 : _root_.LIDT.MIPStarRE.LDT.Error) * 160000 = 320000 by norm_num] using
            _root_.LIDT.MIPStarRE.LDT.Test.sqrt_scaled_stepEnvelope_le (h := h)
              (x := 20204 * k2 * m4 * E2048) (C := (20204 : _root_.LIDT.MIPStarRE.LDT.Error))
              (hC := by norm_num) (hx := le_rfl) (hn := by norm_num) (hN := by norm_num)
      _ ≤ 143 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E4096 := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_right _root_.LIDT.MIPStarRE.LDT.Test.sqrt20204_le_143
              (show 0 ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E4096 by positivity [hE4096NN])
  have hE4096 : E4096 ≤ E32768 := by
    simpa [E4096, E32768] using _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_le_stepEnvelope (h := h)
      (n₁ := (4096 : _root_.LIDT.MIPStarRE.LDT.Error)) (n₂ := (32768 : _root_.LIDT.MIPStarRE.LDT.Error)) (N₁ := (320000 : _root_.LIDT.MIPStarRE.LDT.Error))
      (N₂ := (2560000 : _root_.LIDT.MIPStarRE.LDT.Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
      (hN₁Pos := by norm_num) (hN := by norm_num)
  have hsqrtZ1' : Real.sqrt (20204 * k2 * m4 * E2048) ≤ 143 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E32768 := by
    calc
      Real.sqrt (20204 * k2 * m4 * E2048) ≤ 143 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E4096 := hsqrtZ1
      _ ≤ 143 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E32768 :=
        mul_le_mul_of_nonneg_left hE4096 (by positivity)
  have hX3NN : 0 ≤ 150000 * k2 * m4 * E16384 := by
    positivity [hE16384NN]
  have hsqrtZ3 : Real.sqrt (150000 * k2 * m4 * E16384) ≤ 388 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E32768 := by
    calc
      Real.sqrt (150000 * k2 * m4 * E16384)
        ≤ Real.sqrt (150000 : _root_.LIDT.MIPStarRE.LDT.Error) * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E32768 := by
          simpa [k2, m2, m4, E16384, E32768,
            show (2 : _root_.LIDT.MIPStarRE.LDT.Error) * 16384 = 32768 by norm_num,
            show (2 : _root_.LIDT.MIPStarRE.LDT.Error) * 1280000 = 2560000 by norm_num] using
            _root_.LIDT.MIPStarRE.LDT.Test.sqrt_scaled_stepEnvelope_le (h := h)
              (x := 150000 * k2 * m4 * E16384) (C := (150000 : _root_.LIDT.MIPStarRE.LDT.Error))
              (hC := by norm_num) (hx := le_rfl) (hn := by norm_num) (hN := by norm_num)
      _ ≤ 388 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E32768 := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_right _root_.LIDT.MIPStarRE.LDT.Test.sqrt150000_le_388
              (show 0 ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E32768 by positivity [hE32768NN])
  have hsqrtTerm : 2 * Real.sqrt (Z1 + Z3 / 2) ≤ 1062 * k2 * m4 * E32768 := by
    have hZ3half : Z3 / 2 ≤ 150000 * k2 * m4 * E16384 := by
      nlinarith [hZ3, hZ3NN]
    have hinside : Z1 + Z3 / 2 ≤ 20204 * k2 * m4 * E2048 + 150000 * k2 * m4 * E16384 := by
      linarith [hZ1, hZ3half]
    have hsqrtSplit : Real.sqrt (Z1 + Z3 / 2) ≤
        Real.sqrt (20204 * k2 * m4 * E2048) + Real.sqrt (150000 * k2 * m4 * E16384) := by
      calc
        Real.sqrt (Z1 + Z3 / 2)
          ≤ Real.sqrt (20204 * k2 * m4 * E2048 + 150000 * k2 * m4 * E16384) :=
            Real.sqrt_le_sqrt hinside
        _ ≤ Real.sqrt (20204 * k2 * m4 * E2048) + Real.sqrt (150000 * k2 * m4 * E16384) :=
            _root_.LIDT.MIPStarRE.LDT.sqrt_add_le_add_sqrt (by positivity [hE2048NN]) (by positivity [hE16384NN])
    have hkm2 : (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 ≤ k2 * m4 := by simpa [k2, m2, m4] using h.km2_le_k2m4
    have hkm2z1 : 143 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E32768 ≤ 143 * k2 * m4 * E32768 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hkm2 (show 0 ≤ 143 * E32768 by positivity [hE32768NN])
    have hkm2z3 : 388 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E32768 ≤ 388 * k2 * m4 * E32768 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hkm2 (show 0 ≤ 388 * E32768 by positivity [hE32768NN])
    nlinarith [hsqrtSplit, hsqrtZ1', hsqrtZ3, hkm2z1, hkm2z3]
  unfold _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta4
  calc
    2 * σ + 2 * Real.sqrt (Z1 + Z3 / 2)
      ≤ 20000 * k2 * m4 * E32768 + 1062 * k2 * m4 * E32768 := by
        nlinarith [hσ', hsqrtTerm]
    _ ≤ 40000 * k2 * m4 * E32768 := by
        nlinarith [show 0 ≤ k2 * m4 * E32768 by positivity]
