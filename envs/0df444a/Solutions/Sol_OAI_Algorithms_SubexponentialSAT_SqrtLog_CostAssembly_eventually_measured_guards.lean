-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_measured_guards
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:50:23.125047+00:00
-- url     : https://prove2.me/submissions/1df9d29a-3e8c-42a8-b5d0-a1c8a3cfc2e1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ081S075
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Asymptotic_eventually_residual_layout_guards
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafStatisticsProgram_arity_pos_of_free_pos

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Incidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite factor incidence bounds

Scopes are finite sets: a coordinate occurs at most once in any single factor,
while distinct factors may have equal scopes.  The results below count actual
incidences, bound the neighbors sharing a factor, and account for packing
Boolean variables into chunks followed by one unary validity factor per chunk.
-/

namespace SubexponentialSAT.Incidence

open scoped BigOperators

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]

omit [DecidableEq E] in
/-- Counting incidences by coordinates or by factors gives the same result. -/
theorem sum_degrees [Fintype V] (scope : E → Finset V) :
    ∑ v, degree scope v = ∑ e, (scope e).card := by
  simp_rw [degree_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp

end SubexponentialSAT.Incidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpExponentArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Growing-parameter exponent arithmetic

All factors in this module are actual real powers. The bounds expose the
growing parameters; they assert no program-running-time fact.
-/

namespace SubexponentialSAT.SubexpExponentArithmetic

noncomputable section
open Filter
open scoped Topology

theorem logb_lt_natLog2_add_one (n : ℕ) :
    Real.logb 2 (n : ℝ) < (Nat.log2 n : ℝ) + 1 := by
  have hf : ⌊Real.logb 2 (n : ℝ)⌋₊ = Nat.log2 n := by
    rw [Nat.log2_eq_log_two]
    exact Real.natFloor_logb_natCast 2 n
  simpa only [hf] using
    (Nat.lt_floor_add_one (Real.logb 2 (n : ℝ)))

end
end SubexponentialSAT.SubexpExponentArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRuntime
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform runtime assembly with growing layout parameters

Unlike the older fixed-width-exponent accounting, all layout parameters are
input-dependent here. `GrowingParameters.entries` exposes every argument of
the polynomial costs in Proposition 4.2 and the layout construction. The
analytic lemmas also pay for the variable-degree sunflower search.

Only the purely numerical work/trace infrastructure from `RuntimeAssembly`
is reused; none of its fixed-prime or exponent-0.9 estimates is used.
-/

namespace SubexponentialSAT.SubexpRuntime

open Filter
open scoped Topology

noncomputable section

/-- Any fixed power of log is eventually dominated by the input size, with
an arbitrary fixed positive coefficient and the source's shift by sixteen. -/
theorem eventually_logb_power_le (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℝ in atTop, C * (Real.logb 2 (n + 16)) ^ q ≤ n := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hp : 0 < (Real.log (2 : ℝ)) ^ q := pow_pos hl q
  have ht : Tendsto (fun n : ℝ => n + 16) atTop atTop :=
    tendsto_id.atTop_add tendsto_const_nhds
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := q)).bound
    (show 0 < (Real.log (2 : ℝ)) ^ q / (2 * C) by positivity)
  filter_upwards [ht.eventually hsmall, eventually_ge_atTop (16 : ℝ)] with n hb hn
  have hn0 : 0 ≤ n + 16 := by linarith
  have hlog0 : 0 ≤ Real.log (n + 16) := Real.log_nonneg (by linarith)
  have hb' : (Real.log (n + 16)) ^ q ≤
      (Real.log (2 : ℝ)) ^ q / (2 * C) * (n + 16) := by
    simpa only [Function.id_def, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlog0 q), abs_of_nonneg hn0] using hb
  have hmul : C * (Real.log (n + 16)) ^ q ≤
      (Real.log (2 : ℝ)) ^ q * ((n + 16) / 2) := by
    calc
      C * (Real.log (n + 16)) ^ q ≤
          C * ((Real.log (2 : ℝ)) ^ q / (2 * C) * (n + 16)) :=
        mul_le_mul_of_nonneg_left hb' hC.le
      _ = (Real.log (2 : ℝ)) ^ q * ((n + 16) / 2) := by
        field_simp
  calc
    C * (Real.logb 2 (n + 16)) ^ q =
        (C * (Real.log (n + 16)) ^ q) / (Real.log (2 : ℝ)) ^ q := by
      unfold Real.logb
      rw [div_pow]
      ring
    _ ≤ (n + 16) / 2 := (div_le_iff₀ hp).mpr (by nlinarith [hmul])
    _ ≤ n := by linarith

end
end SubexponentialSAT.SubexpRuntime

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticSchedule
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact, computable square-root-log scheduling. No algorithmic assertion is
hidden in these numerical lemmas. Small inputs may have schedule zero. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem w_pos (n : ℕ) : 0 < w n := by unfold w; omega

theorem le_s_iff (n a : ℕ) : a ≤ s n ↔ a ^ 2 * w n ^ 4 ≤ L n := by
  rw [s, Nat.le_div_iff_mul_le (pow_pos (w_pos n) 2), Nat.le_sqrt']
  ring_nf

theorem s_le_L (n : ℕ) : s n ≤ L n :=
  (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)

theorem four_le_logSize (n : ℕ) : 4 ≤ logSize n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < (n : ℝ) + 16)).mpr
  norm_num

theorem two_le_logLogSize (n : ℕ) : 2 ≤ logLogSize n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by have := four_le_logSize n; linarith : 0 < logSize n)).mpr
  norm_num
  exact four_le_logSize n

theorem logSize_lt_L (n : ℕ) : logSize n < (L n : ℝ) := by
  simpa [logSize, L, Nat.cast_add, Nat.cast_ofNat] using
    SubexpExponentArithmetic.logb_lt_natLog2_add_one (n + 16)

theorem L_le_logSize_add_one (n : ℕ) : (L n : ℝ) ≤ logSize n + 1 := by
  have h := Real.natLog_le_logb (n + 16) 2
  simpa [L, logSize, Nat.log2_eq_log_two, Nat.cast_add] using add_le_add_right h 1

theorem L_le_twice_logSize (n : ℕ) : (L n : ℝ) ≤ 2 * logSize n := by
  have := L_le_logSize_add_one n
  have := four_le_logSize n
  linarith

theorem w_le_twice_logLogSize (n : ℕ) : (w n : ℝ) ≤ 2 * logLogSize n := by
  have hp : (0 : ℝ) < logSize n := by have := four_le_logSize n; linarith
  have hL : (0 : ℝ) < L n := by exact_mod_cast L_pos n
  have hn := Real.natLog_le_logb (L n) 2
  have hlog : Real.logb 2 (L n : ℝ) ≤ 1 + logLogSize n := by
    calc
      Real.logb 2 (L n : ℝ) ≤ Real.logb 2 (2 * logSize n) :=
        Real.logb_le_logb_of_le (by norm_num) hL (L_le_twice_logSize n)
      _ = 1 + logLogSize n := by
        rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) hp.ne']
        norm_num [logLogSize]
  have hw : (w n : ℝ) ≤ Real.logb 2 (L n : ℝ) + 1 := by
    simpa [w, Nat.log2_eq_log_two] using add_le_add_right hn 1
  have := two_le_logLogSize n
  linarith

theorem logSize_tendsto : Tendsto logSize atTop atTop := by
  exact (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)

theorem eventually_le_s (a : ℕ) : ∀ᶠ n : ℕ in atTop, a ≤ s n := by
  have hb := logSize_tendsto.eventually
    (SubexpRuntime.eventually_logb_power_le 4
      (show (0 : ℝ) < ((a : ℝ) + 1) ^ 2 * 16 by positivity))
  filter_upwards [hb] with n hn
  have hw : (w n : ℝ) ≤ 2 * Real.logb 2 (logSize n + 16) := by
    have hm : logLogSize n ≤ Real.logb 2 (logSize n + 16) :=
      Real.logb_le_logb_of_le (by norm_num)
        (by have := four_le_logSize n; linarith) (by linarith)
    exact (w_le_twice_logLogSize n).trans (by linarith)
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ w n by positivity) hw 4
  have ha : (a : ℝ) ^ 2 * (w n : ℝ) ^ 4 ≤ (L n : ℝ) := by
    calc
      (a : ℝ) ^ 2 * (w n : ℝ) ^ 4 ≤
          ((a : ℝ) + 1) ^ 2 * (2 * Real.logb 2 (logSize n + 16)) ^ 4 := by
        apply mul_le_mul
        · nlinarith [Nat.cast_nonneg (α := ℝ) a]
        · exact hp
        · positivity
        · positivity
      _ = (((a : ℝ) + 1) ^ 2 * 16) * Real.logb 2 (logSize n + 16) ^ 4 := by ring_nf
      _ ≤ logSize n := hn
      _ ≤ (L n : ℝ) := (logSize_lt_L n).le
  exact (le_s_iff n a).mpr (by exact_mod_cast ha)

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticLayoutRate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem eventually_L_ge (a : ℕ) : ∀ᶠ n : ℕ in atTop, a ≤ L n := by
  filter_upwards [eventually_le_s a] with n hn
  exact hn.trans (s_le_L n)

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticResidual
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform transport from the original dimension to a residual dimension
between one half and all of it. No lower bound on arbitrary residuals is
assumed: callers must supply the displayed half-dimension condition. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem L_le_succ_of_half {n m : ℕ} (hnm : n ≤ 2 * m) : L n ≤ L m + 1 := by
  have harg : n + 16 ≤ (m + 16) * 2 := by omega
  have h := Nat.log_mono_right (b := 2) harg
  rw [Nat.log_mul_base (by norm_num : 1 < (2 : ℕ)) (by omega : m + 16 ≠ 0)] at h
  simpa [L, Nat.log2_eq_log_two, Nat.add_assoc] using Nat.add_le_add_right h 1

theorem L_le_twice_of_half {n m : ℕ} (hnm : n ≤ 2 * m) : L n ≤ 2 * L m := by
  have := L_le_succ_of_half hnm
  have := L_pos m
  omega

/-- Eventual assertions are uniform over every residual dimension in the
half interval; in particular the residual may depend on a branch. -/
theorem eventually_uniform_half {P : ℕ → Prop} (hP : ∀ᶠ m in atTop, P m) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ≤ 2 * m → P m := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hP
  filter_upwards [eventually_ge_atTop (2 * N)] with n hn m hnm
  exact hN m (by omega)

/-- A fixed polynomial bound in the original logarithm is still a fixed
polynomial bound in every half-size residual logarithm. -/
theorem eventually_residual_polynomial (C q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m b : ℕ, n ≤ 2 * m →
      b ≤ C * L n ^ q → b ≤ L m ^ (q + 1) := by
  filter_upwards [eventually_uniform_half (eventually_L_ge (C * 2 ^ q))] with n hn m b hnm hb
  have hC := hn m hnm
  calc
    b ≤ C * L n ^ q := hb
    _ ≤ C * (2 * L m) ^ q := by gcongr; exact L_le_twice_of_half hnm
    _ = (C * 2 ^ q) * L m ^ q := by rw [mul_pow]; ring
    _ ≤ L m * L m ^ q := Nat.mul_le_mul_right _ hC
    _ = _ := by rw [pow_succ]; ring

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyGuards
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform large-input success of the actual integer parameter guards.
The cutoff is selected before the produced input.  The nonempty-formula and
neutral-coverage premises are explicit semantic obligations of the caller. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open LeafParametersProgram

theorem eventually_parameter_guards (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Input,
      x.ambient = n → x.freeCount ≤ n → n ≤ 2*x.freeCount →
      0 < x.clauses → 0 < x.occurrence → 0 < x.arity →
      x.freeCount ≤ x.incidences →
      x.occurrence ≤ Asymptotic.L x.freeCount^q →
      x.arity ≤ Asymptotic.L x.freeCount^q → Guard x := by
  filter_upwards [Asymptotic.eventually_residual_layout_guards q,
    eventually_ge_atTop (2 : ℕ)] with n hn hnpos x hamb hfree hhalf hcl hb ha hM hbp hap
  obtain ⟨hQ,hR,hsmall,hlarge⟩ := hn x.freeCount x.arity x.occurrence hhalf hap hbp
  refine ⟨by omega,by simpa only [hamb] using hfree,hcl,hb,ha,hM,hQ,hR,?_,hsmall⟩
  calc
    4*(x.occurrence+x.arity)*(produce x).N^2*(produce x).epsilonDen^2 =
        4096*(x.occurrence+x.arity)*x.occurrence^2*
          Asymptotic.layoutR x.freeCount^2*Asymptotic.L x.freeCount^4*
          (Asymptotic.layoutR x.freeCount^(2*Asymptotic.layoutQ x.freeCount))^2 := by
      dsimp [produce]
      ring
    _ ≤ x.freeCount := hlarge
    _ ≤ x.incidences := hM

/-- Fixed ambient polylogarithmic scope bounds suffice for every retained-half
branch.  No choice of a branch or formula precedes the cutoff. -/
theorem eventually_parameter_guards_ambient (C q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Input,
      x.ambient = n → x.freeCount ≤ n → n ≤ 2*x.freeCount →
      0 < x.clauses → 0 < x.occurrence → 0 < x.arity →
      x.freeCount ≤ x.incidences →
      x.occurrence ≤ C*Asymptotic.L n^q →
      x.arity ≤ C*Asymptotic.L n^q → Guard x := by
  filter_upwards [eventually_parameter_guards (q+1),
    Asymptotic.eventually_residual_polynomial C q] with n hn hp x hamb hfree hhalf
      hcl hb ha hM hbp hap
  exact hn x hamb hfree hhalf hcl hb ha hM
    (hp x.freeCount x.occurrence hhalf hbp) (hp x.freeCount x.arity hhalf hap)

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsTotals
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed finite-sum and maximum specifications of the native variable scan. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram

theorem totals_free (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) (t : Totals) :
    (variableTotals scopes v mask t).free = t.free + scanSum (fun _ => 1) v mask := by
  induction mask generalizing v t with
  | nil => simp [variableTotals]
  | cons b bs ih =>
    cases b <;> simp [variableTotals, Totals.add, ih, Nat.add_assoc]

theorem totals_incidences (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) (t : Totals) :
    (variableTotals scopes v mask t).incidences =
      t.incidences + scanSum (fun i => max 1 (degree scopes i)) v mask := by
  induction mask generalizing v t with
  | nil => simp [variableTotals]
  | cons b bs ih =>
    cases b <;> simp [variableTotals, Totals.add, ih, Nat.add_assoc]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The runtime scan equals the statistics of the actual residual scope family,
with precisely one neutral singleton for each unused free coordinate. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram HighIncidence

theorem scanSum_eq_free_sum (f : ℕ → ℕ) (mask : List Bool) :
    scanSum f 0 mask = ∑ i : Free mask, f i.val.val := by
  unfold scanSum
  simp only [Nat.zero_add]
  calc
    _ = ∑ i ∈ (Finset.univ.filter fun i : Fin mask.length => i ∉ highMask mask), f i.val := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mem_highMask, List.get_eq_getElem]
      by_cases hb : mask[i.val] = true <;> simp [hb]
    _ = _ := Finset.sum_subtype _ (by intro i; simp) _

theorem free_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).free = Fintype.card (Free mask) := by
  rw [totals_free, scanSum_eq_free_sum]
  simp [zero]

theorem incidences_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).incidences = totalScope (completedScope scopes mask) := by
  rw [totals_incidences, scanSum_eq_free_sum]
  simp only [zero, Nat.zero_add]
  rw [totalScope, ← Incidence.sum_degrees]
  simp only [completed_degree]

theorem occurrence_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).occurrence =
      Finset.univ.sup (Incidence.degree (completedScope scopes mask)) := by
  apply Nat.le_antisymm
  · rw [totals_occurrence_le_iff]
    refine ⟨Nat.zero_le _, ?_⟩
    intro i hi
    simp only [List.get_eq_getElem] at hi
    let v : Free mask := ⟨i, by simp [hi]⟩
    simpa only [Nat.zero_add, completed_degree] using
      (Finset.le_sup (f := Incidence.degree (completedScope scopes mask)) (Finset.mem_univ v))
  · apply Finset.sup_le
    intro v _
    have h := (totals_occurrence_le_iff scopes 0 mask zero
      (variableTotals scopes 0 mask zero).occurrence).mp le_rfl
    simpa only [Nat.zero_add, completed_degree] using h.2 v.val (free_bit mask v)

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramPositivity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Elementary nondegeneracy conditions for the measured native statistics. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open scoped BigOperators
open LeafStatisticsSemantics

theorem free_le_ambient (scopes : List (List ℕ)) (mask : List Bool) :
    (measured scopes mask).free ≤ mask.length := by
  rw [measured, free_exact]
  simp

theorem free_le_incidences (scopes : List (List ℕ)) (mask : List Bool) :
    (measured scopes mask).free ≤ (measured scopes mask).incidences := by
  simp only [measured]
  rw [free_exact, incidences_exact, HighIncidence.totalScope, ← Incidence.sum_degrees]
  calc
    Fintype.card (Free mask) = ∑ _v : Free mask, (1 : ℕ) := by simp
    _ ≤ ∑ v : Free mask, Incidence.degree (completedScope scopes mask) v := by
      apply Finset.sum_le_sum
      intro v _
      rw [completed_degree]
      exact le_max_left 1 _

theorem occurrence_pos_of_free_pos (scopes : List (List ℕ)) (mask : List Bool)
    (hfree : 0 < (measured scopes mask).free) :
    0 < (measured scopes mask).occurrence := by
  have hc : 0 < Fintype.card (Free mask) := by simpa [measured, free_exact] using hfree
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hc
  rw [measured, occurrence_exact]
  have hd : 1 ≤ Incidence.degree (completedScope scopes mask) v := by
    rw [completed_degree]
    exact le_max_left 1 _
  exact lt_of_lt_of_le (by decide : 0 < 1)
    (hd.trans (Finset.le_sup (f := Incidence.degree (completedScope scopes mask)) (Finset.mem_univ v)))

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyProducedGuards
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Instantiate the uniform guard theorem with the actual measured scope
statistics.  Only the retained-half and scope-size estimates remain as
upstream obligations; positivity and neutral coverage are derived here. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open LeafStatisticsProgram LeafParametersProgram

theorem eventually_measured_guards_oai (C q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (scopes : List (List ℕ)) (mask : List Bool)
      (clauses width : ℕ),
      mask.length = n → n ≤ 2*(measured scopes mask).free →
      0 < clauses → (∀ row ∈ scopes, row.Nodup) →
      (measured scopes mask).occurrence ≤ C*Asymptotic.L n^q →
      measuredArity scopes mask ≤ C*Asymptotic.L n^q →
      Guard (measuredParameterInput scopes mask clauses width) := by
  filter_upwards [eventually_parameter_guards_ambient C q,
    eventually_ge_atTop (2 : ℕ)] with n hn hnpos scopes mask clauses width
      hlen hhalf hcl hnodup hB ha
  have hfree : 0 < (measured scopes mask).free := by omega
  exact hn (measuredParameterInput scopes mask clauses width) hlen
    ((free_le_ambient scopes mask).trans_eq hlen) hhalf hcl
    (occurrence_pos_of_free_pos scopes mask hfree)
    (arity_pos_of_free_pos scopes mask hnodup hfree)
    (free_le_incidences scopes mask) hB ha

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_measured_guards_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_measured_guards_oai
