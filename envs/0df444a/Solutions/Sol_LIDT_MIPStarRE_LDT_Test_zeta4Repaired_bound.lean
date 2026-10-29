-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.zeta4Repaired_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:12:25.531951+00:00
-- url     : https://prove2.me/submissions/df191580-f7be-4ad1-b0d8-9d69c0d9f04f

-- Generated proof for MIPStarRE.LDT.Test.zeta4Repaired_bound.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_cascadeSigma_tight_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_cascadeZeta1_bound_general
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_cascadeZeta1_bound_special
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_cascadeZeta3_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_rpow_Z1_factor_le
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_sqrt_scaled_stepEnvelope_le
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_stepEnvelope_rpow_eighth_le

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







/-- `mainFormalError` factors as `100000 · k² · m⁴ · mainFormalEnvelope`. -/
theorem mainFormalError_eq_envelope (params : Parameters) (k : ℕ) (eps : Error) :
    mainFormalError params k eps =
      100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        mainFormalEnvelope params k eps := rfl

/-- The envelope is nonnegative whenever `ε ≥ 0`. -/
theorem mainFormalEnvelope_nonneg (params : Parameters) (k : ℕ) (eps : Error)
    (heps : 0 ≤ eps) :
    0 ≤ mainFormalEnvelope params k eps := by
  unfold mainFormalEnvelope
  refine add_nonneg (add_nonneg (Real.rpow_nonneg heps _) ?_) (Real.exp_nonneg _)
  exact Real.rpow_nonneg (by positivity) _

















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

/-- The envelope is nonneg. -/
theorem envelope_nonneg : 0 ≤ mainFormalEnvelope params k eps :=
  mainFormalEnvelope_nonneg params k eps h.hepsNN







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

/-- `m ≤ m⁴`. -/
theorem m_le_m4 : (params.m : Error) ≤ ((params.m : Error) ^ (4 : ℕ)) := by
  have hm2_ge : (params.m : Error) ≤ ((params.m : Error) ^ (2 : ℕ)) := by
    have hm_nn : 0 ≤ (params.m : Error) := by linarith [h.hm]
    have : (params.m : Error) * 1 ≤ (params.m : Error) * (params.m : Error) :=
      mul_le_mul_of_nonneg_left h.hm hm_nn
    simpa [sq] using this
  exact hm2_ge.trans h.m2_le_m4

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



theorem mainFormalEnvelope_eq_stepEnvelope (params : Parameters) (k : ℕ) (eps : Error) :
    mainFormalEnvelope params k eps =
      stepEnvelope params k eps (40000 : Error) (2560000 : Error) := rfl

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

/-- A paper-local envelope with exponent `1/n` and decay scale `N` is absorbed
by `mainFormalEnvelope` whenever `n ≤ 40000` and `N ≤ 2560000`. -/
theorem stepEnvelope_le_mainFormalEnvelope {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n N : Error}
    (hnPos : 0 < n) (hn : n ≤ 40000) (hNPos : 0 < N) (hN : N ≤ 2560000) :
    stepEnvelope params k eps n N ≤ mainFormalEnvelope params k eps := by
  calc
    stepEnvelope params k eps n N ≤ stepEnvelope params k eps (40000 : Error) (2560000 : Error) :=
      stepEnvelope_le_stepEnvelope (h := h) (hn₁Pos := hnPos) (hn := hn)
        (hN₁Pos := hNPos) (hN := hN)
    _ = mainFormalEnvelope params k eps := by rw [mainFormalEnvelope_eq_stepEnvelope]





























theorem sqrt170244_le_413 : Real.sqrt (170244 : Error) ≤ 413 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num





theorem rpow20204_eighth_le_4 : Real.rpow (20204 : Error) (1 / (8 : Error)) ≤ 4 := by
  have hmono := Real.rpow_le_rpow (show 0 ≤ (20204 : Error) by norm_num)
    (by norm_num : (20204 : Error) ≤ (4 : Error) ^ (8 : ℕ)) (by positivity : 0 ≤ (1 / (8 : Error)))
  calc
    Real.rpow (20204 : Error) (1 / (8 : Error))
      ≤ Real.rpow ((4 : Error) ^ (8 : ℕ)) (1 / (8 : Error)) := hmono
    _ = Real.rpow (4 : Error) ((8 : Error) * (1 / (8 : Error))) := by
      symm
      exact Real.rpow_natCast_mul (by norm_num : 0 ≤ (4 : Error)) 8 (1 / (8 : Error))
    _ = (4 : Error) := by norm_num [Real.rpow_one]





theorem k2_rpow_eighth_le {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    Real.rpow ((k : Error) ^ (2 : ℕ)) (1 / (8 : Error)) ≤ (k : Error) := by
  calc
    Real.rpow ((k : Error) ^ (2 : ℕ)) (1 / (8 : Error))
      = Real.rpow (k : Error) ((2 : Error) * (1 / (8 : Error))) := by
        symm
        exact Real.rpow_natCast_mul (by positivity : 0 ≤ (k : Error)) 2 (1 / (8 : Error))
    _ = Real.rpow (k : Error) (1 / (4 : Error)) := by norm_num
    _ ≤ (k : Error) := by
      simpa using Real.rpow_le_self_of_one_le h.hk (by norm_num : (1 / (4 : Error)) ≤ 1)

theorem m4_rpow_eighth_le {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    Real.rpow ((params.m : Error) ^ (4 : ℕ)) (1 / (8 : Error)) ≤ (params.m : Error) := by
  calc
    Real.rpow ((params.m : Error) ^ (4 : ℕ)) (1 / (8 : Error))
      = Real.rpow (params.m : Error) ((4 : Error) * (1 / (8 : Error))) := by
        symm
        exact Real.rpow_natCast_mul (by positivity : 0 ≤ (params.m : Error)) 4 (1 / (8 : Error))
    _ = Real.rpow (params.m : Error) (1 / (2 : Error)) := by norm_num
    _ ≤ (params.m : Error) := by
      simpa using Real.rpow_le_self_of_one_le h.hm (by norm_num : (1 / (2 : Error)) ≤ 1)













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
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps) {ν σ ζ₁ ζ₂ ζ₃ : _root_.LIDT.MIPStarRE.LDT.Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
        Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))))
    (hσEq : σ = _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps σ)
    (hζ₂Eq : ζ₂ = _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta2 ζ₁)
    (hζ₃Eq : ζ₃ = _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta3 ζ₁ ζ₂) :
    _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta4Repaired σ ζ₁ ζ₃ ≤ _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError params k eps := by
  rw [hζ₃Eq, hζ₂Eq, hζ₁Eq, hσEq, _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError_eq_envelope]
  set σ0 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν
  set Z1 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps σ0
  set Z2 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta2 Z1
  set Z3 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta3 Z1 Z2
  set k2 : _root_.LIDT.MIPStarRE.LDT.Error := (k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)
  set m2 : _root_.LIDT.MIPStarRE.LDT.Error := (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)
  set m4 : _root_.LIDT.MIPStarRE.LDT.Error := (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)
  set E1024 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (1024 : _root_.LIDT.MIPStarRE.LDT.Error) (80000 : _root_.LIDT.MIPStarRE.LDT.Error)
  set E2048 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error)
  set E16384 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (16384 : _root_.LIDT.MIPStarRE.LDT.Error) (1280000 : _root_.LIDT.MIPStarRE.LDT.Error)
  set E32768 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (32768 : _root_.LIDT.MIPStarRE.LDT.Error) (2560000 : _root_.LIDT.MIPStarRE.LDT.Error)
  have hE2048NN : 0 ≤ E2048 := by
    simpa [E2048] using
      _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_nonneg (h := h) (n := (2048 : _root_.LIDT.MIPStarRE.LDT.Error)) (N := (160000 : _root_.LIDT.MIPStarRE.LDT.Error))
  have hE16384NN : 0 ≤ E16384 := by
    simpa [E16384] using
      _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_nonneg (h := h) (n := (16384 : _root_.LIDT.MIPStarRE.LDT.Error)) (N := (1280000 : _root_.LIDT.MIPStarRE.LDT.Error))
  have hE32768NN : 0 ≤ E32768 := by
    simpa [E32768] using
      _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_nonneg (h := h) (n := (32768 : _root_.LIDT.MIPStarRE.LDT.Error)) (N := (2560000 : _root_.LIDT.MIPStarRE.LDT.Error))
  have hσ : σ0 ≤ 10000 * k2 * m4 * E1024 := by
    simpa [σ0, k2, m4, E1024] using _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma_tight_bound (h := h) (ν := ν) hν
  have hσ' : σ0 ≤ 10000 * k2 * m4 * E32768 := by
    calc
      σ0 ≤ 10000 * k2 * m4 * E1024 := hσ
      _ ≤ 10000 * k2 * m4 * E32768 := by
        have hMono : E1024 ≤ E32768 := by
          simpa [E1024, E32768] using _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_le_stepEnvelope (h := h)
            (n₁ := (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) (n₂ := (32768 : _root_.LIDT.MIPStarRE.LDT.Error)) (N₁ := (80000 : _root_.LIDT.MIPStarRE.LDT.Error))
            (N₂ := (2560000 : _root_.LIDT.MIPStarRE.LDT.Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
            (hN₁Pos := by norm_num) (hN := by norm_num)
        exact mul_le_mul_of_nonneg_left hMono (by positivity)
  have hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048 := by
    simpa [σ0, Z1, k2, m4, E2048] using _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1_bound (h := h) (ν := ν) hν
  have hZ1NN : 0 ≤ Z1 := by
    simpa [σ0, Z1] using _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1_nonneg (h := h) (ν := ν) hνNN
  have hZ3 : Z3 ≤ 150000 * k2 * m4 * E16384 := by
    simpa [σ0, Z1, Z2, Z3, k2, m4, E16384] using _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta3_bound (h := h) (ν := ν) hνNN hν
  have hZ1Eighth : Real.rpow Z1 (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
      4 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * E16384 := by
    exact _root_.LIDT.MIPStarRE.LDT.Test.rpow_Z1_factor_le (params := params) (k := k)
      (hZ1NN := hZ1NN) (hZ1 := hZ1) (hrNN := by positivity)
      (hk2NN := by positivity) (hm4NN := by positivity) (hE2048NN := hE2048NN)
      (hA := by simpa using _root_.LIDT.MIPStarRE.LDT.Test.rpow20204_eighth_le_4)
      (hB := by simpa [k2] using _root_.LIDT.MIPStarRE.LDT.Test.k2_rpow_eighth_le (h := h))
      (hC := by simpa [m4] using _root_.LIDT.MIPStarRE.LDT.Test.m4_rpow_eighth_le (h := h))
      (hD := by simpa [E2048, E16384] using _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_rpow_eighth_le (h := h))
  have hZ1to16384 : Z1 ≤ 20204 * k2 * m4 * E16384 := by
    have hE2048_le : E2048 ≤ E16384 := by
      simpa [E2048, E16384] using _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_le_stepEnvelope (h := h)
        (n₁ := (2048 : _root_.LIDT.MIPStarRE.LDT.Error)) (n₂ := (16384 : _root_.LIDT.MIPStarRE.LDT.Error)) (N₁ := (160000 : _root_.LIDT.MIPStarRE.LDT.Error))
        (N₂ := (1280000 : _root_.LIDT.MIPStarRE.LDT.Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
        (hN₁Pos := by norm_num) (hN := by norm_num)
    exact hZ1.trans <| mul_le_mul_of_nonneg_left hE2048_le (by positivity)
  have hRepairTerm : 10 * Real.rpow Z1 (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ 40 * k2 * m4 * E16384 := by
    have hkm : (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ≤ k2 * m4 := by
      calc
        (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error)
          ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) := by
              exact mul_le_mul_of_nonneg_left h.m_le_m4 (by positivity)
        _ ≤ k2 * m4 := by
              exact mul_le_mul_of_nonneg_right h.k_le_k2 (by positivity)
    calc
      10 * Real.rpow Z1 (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))
          ≤ 10 * (4 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * E16384) := by
              gcongr
      _ = 40 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error)) * E16384 := by ring
      _ ≤ 40 * (k2 * m4) * E16384 := by
        have : 40 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ 40 * (k2 * m4) := by
          exact mul_le_mul_of_nonneg_left hkm (by norm_num : (0 : Error) ≤ 40)
        exact mul_le_mul_of_nonneg_right this hE16384NN
      _ = 40 * k2 * m4 * E16384 := by ring
  have hRepair : _root_.LIDT.MIPStarRE.LDT.Test.cascadeLine169RepairError Z1 ≤ 20244 * k2 * m4 * E16384 := by
    unfold _root_.LIDT.MIPStarRE.LDT.Test.cascadeLine169RepairError
    linarith
  have hsqrtTerm : 2 * Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Test.cascadeLine169RepairError Z1 + Z3 / 2)
      ≤ 826 * k2 * m4 * E32768 := by
    have hZ3half : Z3 / 2 ≤ 150000 * k2 * m4 * E16384 := by
      nlinarith [hZ3]
    have hinside : _root_.LIDT.MIPStarRE.LDT.Test.cascadeLine169RepairError Z1 + Z3 / 2 ≤
        170244 * k2 * m4 * E16384 := by
      linarith [hRepair, hZ3half]
    have hsqrtBound : Real.sqrt (170244 * k2 * m4 * E16384) ≤
        413 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E32768 := by
      calc
        Real.sqrt (170244 * k2 * m4 * E16384)
            ≤ Real.sqrt (170244 : _root_.LIDT.MIPStarRE.LDT.Error) * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E32768 := by
              simpa [k2, m2, m4, E16384, E32768,
                show (2 : _root_.LIDT.MIPStarRE.LDT.Error) * 16384 = 32768 by norm_num,
                show (2 : _root_.LIDT.MIPStarRE.LDT.Error) * 1280000 = 2560000 by norm_num] using
                _root_.LIDT.MIPStarRE.LDT.Test.sqrt_scaled_stepEnvelope_le (h := h)
                  (x := 170244 * k2 * m4 * E16384) (C := (170244 : _root_.LIDT.MIPStarRE.LDT.Error))
                  (hC := by norm_num) (hx := le_rfl) (hn := by norm_num) (hN := by norm_num)
        _ ≤ 413 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E32768 := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_right _root_.LIDT.MIPStarRE.LDT.Test.sqrt170244_le_413
                (show 0 ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E32768 by positivity [hE32768NN])
    have hkm2 : (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 ≤ k2 * m4 := by simpa [k2, m2, m4] using h.km2_le_k2m4
    have hkm2z : 413 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * m2 * E32768 ≤ 413 * k2 * m4 * E32768 := by
      have : 413 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * m2) ≤ 413 * (k2 * m4) := by
        exact mul_le_mul_of_nonneg_left hkm2 (by norm_num : (0 : Error) ≤ 413)
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right this hE32768NN
    have hsqrtInside : Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Test.cascadeLine169RepairError Z1 + Z3 / 2) ≤
        Real.sqrt (170244 * k2 * m4 * E16384) := Real.sqrt_le_sqrt hinside
    nlinarith [hsqrtInside, hsqrtBound, hkm2z]
  have hTightEnvelope :
      _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (32768 : _root_.LIDT.MIPStarRE.LDT.Error) (2560000 : _root_.LIDT.MIPStarRE.LDT.Error) ≤
        _root_.LIDT.MIPStarRE.LDT.Test.mainFormalEnvelope params k eps :=
    _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_le_mainFormalEnvelope (h := h) (n := (32768 : _root_.LIDT.MIPStarRE.LDT.Error)) (N := (2560000 : _root_.LIDT.MIPStarRE.LDT.Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ k2 * m4 := by positivity
  calc
    _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta4Repaired σ0 Z1 Z3
      = 2 * σ0 + 2 * Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Test.cascadeLine169RepairError Z1 + Z3 / 2) := by rfl
    _ ≤ 20000 * k2 * m4 * E32768 + 826 * k2 * m4 * E32768 := by
          nlinarith [hσ', hsqrtTerm]
    _ ≤ 40000 * k2 * m4 * E32768 := by
          nlinarith [hk2m4NN]
    _ ≤ 40000 * k2 * m4 * _root_.LIDT.MIPStarRE.LDT.Test.mainFormalEnvelope params k eps :=
          mul_le_mul_of_nonneg_left hTightEnvelope (by positivity)
    _ = (40000 * (k2 * m4)) * _root_.LIDT.MIPStarRE.LDT.Test.mainFormalEnvelope params k eps := by ring
    _ ≤ (100000 * (k2 * m4)) * _root_.LIDT.MIPStarRE.LDT.Test.mainFormalEnvelope params k eps :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num : (40000 : Error) ≤ 100000) hk2m4NN) hENN
    _ = _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError params k eps := by
          rw [_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError_eq_envelope]
          ring
