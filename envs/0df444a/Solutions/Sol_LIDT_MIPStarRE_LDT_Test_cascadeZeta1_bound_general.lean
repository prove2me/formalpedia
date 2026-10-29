-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.cascadeZeta1_bound_general
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:52:16.325409+00:00
-- url     : https://prove2.me/submissions/55a46695-8490-405d-bd11-e23efc1d50a0

-- Generated proof for MIPStarRE.LDT.Test.cascadeZeta1_bound_general.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_cascadeSigma_tight_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_mdq_le_k2m4_stepEnvelope2048
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



/-- `1 ≤ m²`. -/
theorem m2_ge_one : (1 : Error) ≤ ((params.m : Error) ^ (2 : ℕ)) := by
  simpa using one_le_pow₀ (n := (2 : ℕ)) h.hm

/-- `1 ≤ k²`. -/
theorem k2_ge_one : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
  simpa using one_le_pow₀ (n := (2 : ℕ)) h.hk

/-- `1 ≤ m⁴`. -/
theorem m4_ge_one : (1 : Error) ≤ ((params.m : Error) ^ (4 : ℕ)) := by
  simpa using one_le_pow₀ (n := (4 : ℕ)) h.hm









/-- `k² · m⁴ ≥ 1`. -/
theorem k2_m4_ge_one : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) *
    ((params.m : Error) ^ (4 : ℕ)) := by
  nlinarith [h.k2_ge_one, h.m4_ge_one]

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





















theorem four_mul_le_k2m4_mul {params : Parameters} {k : ℕ} {eps T : Error}
    (h : CascadeHypotheses params k eps) (hT : 0 ≤ T) :
    4 * T ≤ 4 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ))) * T := by
  have hscale : (4 : Error) ≤ 4 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ))) := by
    simpa using mul_le_mul_of_nonneg_left h.k2_m4_ge_one (by norm_num : (0 : Error) ≤ 4)
  exact mul_le_mul_of_nonneg_right hscale hT

theorem sqrt_three_le_two : Real.sqrt (3 : Error) ≤ 2 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num

theorem sqrt20000_le_142 : Real.sqrt (20000 : Error) ≤ 142 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num

































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
        Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))))
    (hkm1 : ¬ (k = 1 ∧ params.m = 1)) :
    _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps (_root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν) ≤
      20204 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) *
        _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error) := by
  set k2 : _root_.LIDT.MIPStarRE.LDT.Error := (k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)
  set m2 : _root_.LIDT.MIPStarRE.LDT.Error := (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)
  set m4 : _root_.LIDT.MIPStarRE.LDT.Error := (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)
  set S : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (1024 : _root_.LIDT.MIPStarRE.LDT.Error) (80000 : _root_.LIDT.MIPStarRE.LDT.Error)
  set T : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error)
  set σ : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν
  have hσtight : σ ≤ 10000 * k2 * m4 * S := by
    simpa [σ, k2, m4, S] using _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma_tight_bound (h := h) (ν := ν) hν
  have hST : S ≤ T := by
    simpa [S, T] using _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_le_stepEnvelope (h := h) (n₁ := (1024 : _root_.LIDT.MIPStarRE.LDT.Error))
      (n₂ := (2048 : _root_.LIDT.MIPStarRE.LDT.Error)) (N₁ := (80000 : _root_.LIDT.MIPStarRE.LDT.Error)) (N₂ := (160000 : _root_.LIDT.MIPStarRE.LDT.Error))
      (hn₁Pos := by norm_num) (hn := by norm_num) (hN₁Pos := by norm_num) (hN := by norm_num)
  have hσtoT : σ ≤ 10000 * k2 * m4 * T := by
    calc
      σ ≤ 10000 * k2 * m4 * S := hσtight
      _ ≤ 10000 * k2 * m4 * T := by
        exact mul_le_mul_of_nonneg_left hST (by positivity)
  have htwoσ : 2 * σ ≤ 20000 * k2 * m4 * T := by
    nlinarith [hσtoT]
  have hTNN : 0 ≤ T := by
    simpa [T] using _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_nonneg (h := h) (n := (2048 : _root_.LIDT.MIPStarRE.LDT.Error)) (N := (160000 : _root_.LIDT.MIPStarRE.LDT.Error))
  have hSNN : 0 ≤ S := by
    simpa [S] using _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_nonneg (h := h) (n := (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) (N := (80000 : _root_.LIDT.MIPStarRE.LDT.Error))
  have hEpsTerm : Real.rpow eps (1 / (2048 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ T := by
    unfold T _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope
    have hdqNN' : 0 ≤ Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (2048 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
      Real.rpow_nonneg h.dqNN _
    have hExpNN' :
        0 ≤ Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / ((160000 : _root_.LIDT.MIPStarRE.LDT.Error) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ))))) :=
      Real.exp_nonneg _
    nlinarith
  have hsqrt_eps : Real.sqrt eps ≤ Real.rpow eps (1 / (2048 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    calc
      Real.sqrt eps = Real.rpow eps (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) := by simpa using (Real.sqrt_eq_rpow eps)
      _ ≤ Real.rpow eps (1 / (2048 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
        _root_.LIDT.MIPStarRE.LDT.Test.rpow_le_of_denom_le h.hepsNN h.hepsOne (n₁ := (2 : _root_.LIDT.MIPStarRE.LDT.Error)) (n₂ := (2048 : _root_.LIDT.MIPStarRE.LDT.Error))
          (hn₁Pos := by norm_num) (hn := by norm_num)
  have hsqrt3eps : Real.sqrt (3 * eps) ≤ 2 * T := by
    calc
      Real.sqrt (3 * eps) = Real.sqrt (3 : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt eps := by
        rw [Real.sqrt_mul (by norm_num)]
      _ ≤ 2 * Real.sqrt eps := by
        exact mul_le_mul_of_nonneg_right _root_.LIDT.MIPStarRE.LDT.Test.sqrt_three_le_two (Real.sqrt_nonneg _)
      _ ≤ 2 * Real.rpow eps (1 / (2048 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
        mul_le_mul_of_nonneg_left hsqrt_eps (by norm_num)
      _ ≤ 2 * T := mul_le_mul_of_nonneg_left hEpsTerm (by norm_num)
  have hsqrtScaled : Real.sqrt (20000 * k2 * m4 * S) ≤
      Real.sqrt (20000 : _root_.LIDT.MIPStarRE.LDT.Error) * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * T := by
    simpa [k2, m2, m4, S, T,
      show (2 : _root_.LIDT.MIPStarRE.LDT.Error) * 1024 = 2048 by norm_num,
      show (2 : _root_.LIDT.MIPStarRE.LDT.Error) * 80000 = 160000 by norm_num] using
      _root_.LIDT.MIPStarRE.LDT.Test.sqrt_scaled_stepEnvelope_le (h := h)
        (x := 20000 * k2 * m4 * S) (C := (20000 : _root_.LIDT.MIPStarRE.LDT.Error))
        (hC := by norm_num) (hx := le_rfl) (hn := by norm_num) (hN := by norm_num)
  have hsqrtScaled142 : Real.sqrt (20000 * k2 * m4 * S) ≤ 142 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * T := by
    calc
      Real.sqrt (20000 * k2 * m4 * S)
        ≤ Real.sqrt (20000 : _root_.LIDT.MIPStarRE.LDT.Error) * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * T := hsqrtScaled
      _ ≤ 142 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * T := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_right _root_.LIDT.MIPStarRE.LDT.Test.sqrt20000_le_142
            (show 0 ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * T by positivity [hTNN])
  have hsqrtTmp : Real.sqrt (3 * eps + 2 * σ) ≤
      Real.sqrt (3 * eps) + Real.sqrt (20000 * k2 * m4 * S) := by
    have harg : 3 * eps + 2 * σ ≤ 3 * eps + 20000 * k2 * m4 * S := by
      nlinarith [hσtight, hSNN]
    calc
      Real.sqrt (3 * eps + 2 * σ)
        ≤ Real.sqrt (3 * eps + 20000 * k2 * m4 * S) := Real.sqrt_le_sqrt harg
      _ ≤ Real.sqrt (3 * eps) + Real.sqrt (20000 * k2 * m4 * S) :=
        _root_.LIDT.MIPStarRE.LDT.sqrt_add_le_add_sqrt (by nlinarith [h.hepsNN]) (by positivity [hSNN])
  have hkm2_ge_two : (2 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 := by
    by_cases hk1 : k = 1
    · have hmNe : params.m ≠ 1 := by
        intro hmEq
        exact hkm1 ⟨hk1, hmEq⟩
      have hmNat2 : 2 ≤ params.m := by
        have hmNat1 : 1 ≤ params.m := by exact_mod_cast h.hm
        omega
      have hm_ge_two : (2 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by exact_mod_cast hmNat2
      have hm2_ge_two : (2 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ m2 := by
        dsimp [m2]
        nlinarith [hm_ge_two]
      simpa [hk1] using hm2_ge_two
    · have hkNat2 : 2 ≤ k := by
        have hkNat1 : 1 ≤ k := by exact_mod_cast h.hk
        omega
      have hk_ge_two : (2 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) := by exact_mod_cast hkNat2
      nlinarith [hk_ge_two, h.m2_ge_one]
  have hkm2NN : 0 ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 := by positivity
  have hkm2_sq : (((k : _root_.LIDT.MIPStarRE.LDT.Error) * m2) ^ (2 : ℕ)) = k2 * m4 := by
    dsimp [k2, m2, m4]
    ring
  have hCoeffDirect : (284 : _root_.LIDT.MIPStarRE.LDT.Error) * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * m2) ≤ 199 * k2 * m4 := by
    have h284 : (284 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 199 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * m2) := by
      nlinarith [hkm2_ge_two]
    have hmul := mul_le_mul_of_nonneg_right h284 hkm2NN
    calc
      (284 : _root_.LIDT.MIPStarRE.LDT.Error) * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * m2) ≤ (199 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * m2)) * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * m2) := by
        simpa [mul_assoc] using hmul
      _ = 199 * (((k : _root_.LIDT.MIPStarRE.LDT.Error) * m2) ^ (2 : ℕ)) := by ring
      _ = 199 * k2 * m4 := by rw [hkm2_sq]; ring
  have hsqrtBig : 2 * Real.sqrt (20000 * k2 * m4 * S) ≤ 199 * k2 * m4 * T := by
    have htmp1' : 2 * Real.sqrt (20000 * k2 * m4 * S) ≤ 2 * (142 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * T) :=
      mul_le_mul_of_nonneg_left hsqrtScaled142 (by norm_num : (0 : Error) ≤ 2)
    have htmp1b : 2 * (142 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * T) = (284 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * m2)) * T := by
      ring
    have htmp1 : 2 * Real.sqrt (20000 * k2 * m4 * S) ≤ (284 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * m2)) * T := by
      exact htmp1'.trans_eq htmp1b
    have htmp2 : (284 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * m2)) * T ≤ (199 * k2 * m4) * T :=
      mul_le_mul_of_nonneg_right hCoeffDirect hTNN
    have htmp3 : (199 * k2 * m4) * T = 199 * k2 * m4 * T := by ring
    exact htmp1.trans <| htmp2.trans_eq htmp3
  have hsqrt3Term : 2 * Real.sqrt (3 * eps) ≤ 4 * T := by
    have htmp : 2 * Real.sqrt (3 * eps) ≤ 2 * (2 * T) :=
      mul_le_mul_of_nonneg_left hsqrt3eps (by norm_num : (0 : Error) ≤ 2)
    have hEq : 2 * (2 * T) = 4 * T := by ring
    exact htmp.trans_eq hEq
  have hsqrtTerm : 2 * Real.sqrt (3 * eps + 2 * σ) ≤ 4 * T + 199 * k2 * m4 * T := by
    have hsqrtTmp2' : 2 * Real.sqrt (3 * eps + 2 * σ) ≤ 2 *
        (Real.sqrt (3 * eps) + Real.sqrt (20000 * k2 * m4 * S)) :=
      mul_le_mul_of_nonneg_left hsqrtTmp (by norm_num : (0 : Error) ≤ 2)
    have hEq : 2 *
        (Real.sqrt (3 * eps) + Real.sqrt (20000 * k2 * m4 * S)) =
        2 * Real.sqrt (3 * eps) + 2 * Real.sqrt (20000 * k2 * m4 * S) := by ring
    have hsqrtTmp2 : 2 * Real.sqrt (3 * eps + 2 * σ) ≤
        2 * Real.sqrt (3 * eps) + 2 * Real.sqrt (20000 * k2 * m4 * S) := by
      exact hsqrtTmp2'.trans_eq hEq
    exact hsqrtTmp2.trans (add_le_add hsqrt3Term hsqrtBig)
  have hmdq_to_k2m4T :
      (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ k2 * m4 * T := by
    dsimp [k2, m4, T]
    exact _root_.LIDT.MIPStarRE.LDT.Test.mdq_le_k2m4_stepEnvelope2048 (h := h)
  have hfourT : 4 * T ≤ 4 * (k2 * m4) * T := by
    dsimp [k2, m4]
    exact _root_.LIDT.MIPStarRE.LDT.Test.four_mul_le_k2m4_mul (h := h) hTNN
  rw [show _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps σ =
      2 * σ + 2 * Real.sqrt (3 * eps + 2 * σ) +
        (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * (params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) by rfl]
  have hmdq_to_k2m4T' :
      (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * (params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) ≤ k2 * m4 * T := by
    calc
      (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * (params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)
        = (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) := by ring
      _ ≤ k2 * m4 * T := hmdq_to_k2m4T
  calc
    2 * σ + 2 * Real.sqrt (3 * eps + 2 * σ) +
        (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * (params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)
      ≤ (20000 * k2 * m4 * T + (4 * T + 199 * k2 * m4 * T)) + k2 * m4 * T :=
          add_le_add (add_le_add htwoσ hsqrtTerm) hmdq_to_k2m4T'
    _ = 20000 * k2 * m4 * T + 4 * T + 199 * k2 * m4 * T + k2 * m4 * T := by ring
    _ = (20000 * k2 * m4 * T + 4 * T) + (199 * k2 * m4 * T + k2 * m4 * T) := by ring
    _ ≤ (20000 * k2 * m4 * T + 4 * (k2 * m4) * T) +
          (199 * k2 * m4 * T + k2 * m4 * T) :=
        add_le_add (add_le_add le_rfl hfourT) le_rfl
    _ = 20204 * k2 * m4 * T := by ring
