-- Prove2me | solution 1 for OAI.EditApproximation.computed_localRandomDataQuery_table_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:30:11.213795+00:00
-- url     : https://prove2.me/submissions/40261c53-b13a-450c-a975-654b63ae45a3

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea002

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer-computed parameters

The logarithms and fourth roots in Section 2 are computed by natural bit
lengths and nested integer square roots. No real arithmetic oracle is
used to form the algorithm's parameters.
-/

namespace EditApproximation
















theorem inputSmallLog_bounds (N : ℕ) (hN : 0 < N) :
    heightExponent N ≤ inputSmallLog N ∧ inputSmallLog N < 2 * heightExponent N := by
  have hpos := heightExponent_pos N hN
  have hone : 1 ≤ heightExponent N := hpos
  have hrange := rejectionWord_range (heightExponent N) hpos
  simpa only [inputSmallLog, smallLogExponent, rejectionBitCount, max_eq_right hone] using hrange

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Depth of the computed interval tree

The branching factor is the power of two prescribed by the algorithm.
Ceiling logarithms count physical levels, including empty intervals.
-/

namespace EditApproximation

open Finset



theorem computed_branching_bounds (N : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) :
    2 ≤ (integerParameters N).M ∧
      inputSmallLog N ≤ 50 * (heightExponent N / 20) ∧
      heightExponent N / 20 ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hquot := Nat.mod_lt (heightExponent N) (by decide : 0 < 20)
  have hsplit := Nat.mod_add_div (heightExponent N) 20
  have hk : 1 ≤ heightExponent N / 20 := by omega
  have hpow : 2 ≤ 2 ^ (heightExponent N / 20) := by
    simpa using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hk
  have hexp : heightExponent N ≤ inputHeight N := by
    exact (Nat.lt_pow_self (by decide : 1 < 2)).le
  exact ⟨hpow, by omega, (Nat.div_le_self _ _).trans hexp⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGrid
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Direct enumeration of a local grid square

The algorithm enumerates bounded ranges of grid indices. It does not
scan the unrelated target positions. The completeness theorem includes
boundary states and intervals with equal endpoints.
-/

namespace EditApproximation



theorem localTargetStates_length_le {n g radius : ℕ} (hg : 0 < g)
    (q : TargetInterval n) :
    (localTargetStates n g radius q).length ≤ (2 * radius / g + 2) ^ 2 := by
  have hpoint (p : ℕ) :
      (gridPointsBetween g (p - radius) (p + radius)).length ≤ 2 * radius / g + 2 := by
    have hlength := gridPointsBetween_length_le g (p - radius) (p + radius) hg
    have hwidth : p + radius - (p - radius) ≤ 2 * radius := by omega
    exact hlength.trans (Nat.add_le_add_right (Nat.div_le_div_right hwidth) 2)
  have hlist := list_flatMap_length_le
    (gridPointsBetween g (q.lo - radius) (q.lo + radius))
    (fun lo => (gridPointsBetween g (q.hi - radius) (q.hi + radius)).filterMap
      fun hi => makeTargetState n lo hi)
    (2 * radius / g + 2) (by
      intro lo hlo
      exact (List.length_filterMap_le _ _).trans (hpoint q.hi))
  exact hlist.trans (by simpa only [pow_two] using
    (Nat.mul_le_mul_right (2 * radius / g + 2) (hpoint q.lo)))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GroupCells
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Whole rational cells are enumerated by bounded ranges of grid indices. -/

namespace EditApproximation



theorem cellGridPoints_length_le {side : ℚ} {g cell P : ℕ}
    (hside : 0 ≤ side) (hsize : side / g ≤ P) :
    (cellGridPoints side g cell).length ≤ P := by
  have hbase : 0 ≤ (cell : ℚ) * side / g :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hside) (Nat.cast_nonneg _)
  have hupper : ((cell : ℚ) + 1) * side / g ≤ (cell : ℚ) * side / g + P := by
    calc
      _ = (cell : ℚ) * side / g + side / g := by ring
      _ ≤ _ := add_le_add_right hsize _
  have hceil := Nat.ceil_le_ceil hupper
  rw [Nat.ceil_add_natCast hbase P] at hceil
  simp only [cellGridPoints, List.length_map, List.length_range']
  omega



theorem cellTargetStates_length_le {n g P : ℕ} {side : ℚ} (cell : ℕ × ℕ)
    (hside : 0 ≤ side) (hsize : side / g ≤ P) :
    (cellTargetStates n g side cell).length ≤ P ^ 2 := by
  have hfirst := cellGridPoints_length_le (cell := cell.1) hside hsize
  have hsecond := cellGridPoints_length_le (cell := cell.2) hside hsize
  have h := list_flatMap_length_le (cellGridPoints side g cell.1)
    (fun lo => (cellGridPoints side g cell.2).filterMap fun hi => makeTargetState n lo hi) P
    (fun lo _ => (List.length_filterMap_le _ _).trans hsecond)
  exact h.trans (by simpa only [pow_two] using Nat.mul_le_mul_right P hfirst)

theorem seedGridSpacing_covers_dyadic {b P : ℕ}
    (hb : ∃ e : ℕ, b = 2 ^ e) (hP : ∃ e : ℕ, P = 2 ^ e) :
    b ≤ P * seedGridSpacing b P := by
  obtain ⟨eb, rfl⟩ := hb
  obtain ⟨eP, rfl⟩ := hP
  by_cases horder : eP ≤ eb
  · rw [seedGridSpacing, Nat.pow_div horder (by decide : 0 < 2), max_eq_right Nat.one_le_two_pow,
      ← pow_add, Nat.add_sub_of_le horder]
  · have hle : 2 ^ eb ≤ 2 ^ eP := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    exact hle.trans (Nat.le_mul_of_pos_right _ (by unfold seedGridSpacing; omega))

theorem cellRepresentativeStates_length_le {n P F b : ℕ}
    (a : ℚ) (initial : TargetInterval n → ℚ) (theta : ℚ) (cell : ℕ × ℕ)
    (htheta : 0 ≤ theta ∧ theta ≤ 1)
    (hb : ∃ e : ℕ, b = 2 ^ e) (hP : ∃ e : ℕ, P = 2 ^ e) :
    (cellRepresentativeStates n P F b a initial theta cell).length ≤ (P + 1) ^ 2 := by
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hgr : (0 : ℚ) < seedGridSpacing b P := by exact_mod_cast hg
  have hcover : (b : ℚ) ≤ P * (seedGridSpacing b P : ℚ) := by
    exact_mod_cast seedGridSpacing_covers_dyadic hb hP
  have hsize : theta * b / seedGridSpacing b P ≤ (P : ℚ) := by
    apply (div_le_iff₀ hgr).2
    have h := mul_le_mul_of_nonneg_right htheta.2 (Nat.cast_nonneg (α := ℚ) b)
    simp only [one_mul] at h
    exact h.trans hcover
  unfold cellRepresentativeStates
  apply (List.length_filter_le _ _).trans
  exact (cellTargetStates_length_le (n := n) cell
    (mul_nonneg htheta.1 (Nat.cast_nonneg _)) hsize).trans
      (Nat.pow_le_pow_left (Nat.le_succ P) 2)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandGroupSampling
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Executable shared group estimates

All dyadic powers in the prescribed closed range are enumerated, including
negative exponents. A scale is evaluated exactly when its sample count
reaches the child count; otherwise one shared array of uniform labels is
used for every member of the group. The selected member is the first
minimizer in the fixed list order.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory



theorem integerClosedRange_mem (lo hi value : ℤ) :
    value ∈ integerClosedRange lo hi ↔ lo ≤ value ∧ value ≤ hi := by
  constructor
  · intro h
    obtain ⟨i, hi', hequal⟩ := List.mem_map.mp h
    have hrange := List.mem_range.mp hi'
    omega
  · rintro ⟨hlower, hupper⟩
    apply List.mem_map.mpr
    refine ⟨(value - lo).toNat, List.mem_range.mpr ?_, ?_⟩ <;> omega



theorem groupDyadicScales_mem {M b : ℕ} (hM : 0 < M) (hb : 0 < b)
    (F : ℚ) (hF : 0 < F) (exponent : ℤ) :
    (2 : ℚ) ^ exponent ∈ groupDyadicScales M b F ↔
      (b : ℚ) / M ≤ (2 : ℚ) ^ exponent ∧ (2 : ℚ) ^ exponent ≤ 64 * F * b := by
  have hlower : (0 : ℚ) < (b : ℚ) / M := by positivity
  have hupper : (0 : ℚ) < 64 * F * b := by positivity
  constructor
  · intro h
    obtain ⟨other, hother, hequal⟩ := List.mem_map.mp h
    have hsame : other = exponent :=
      zpow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num : (2 : ℚ) ≠ 1) hequal
    subst other
    have hrange := (integerClosedRange_mem _ _ _).mp hother
    exact ⟨(Int.le_zpow_iff_clog_le (by decide : 1 < 2) hlower).mpr hrange.1,
      (Int.zpow_le_iff_le_log (by decide : 1 < 2) hupper).mpr hrange.2⟩
  · rintro ⟨hlow, hhigh⟩
    apply List.mem_map.mpr
    refine ⟨exponent, (integerClosedRange_mem _ _ _).mpr ⟨?_, ?_⟩, rfl⟩
    · exact (Int.le_zpow_iff_clog_le (by decide : 1 < 2) hlower).mp hlow
    · exact (Int.zpow_le_iff_le_log (by decide : 1 < 2) hupper).mp hhigh

theorem groupDyadicScales_pos {M b : ℕ} {F h : ℚ}
    (hh : h ∈ groupDyadicScales M b F) : 0 < h := by
  obtain ⟨exponent, _, rfl⟩ := List.mem_map.mp hh
  positivity



theorem groupDyadicScales_length (M b : ℕ) (F : ℚ) :
    (groupDyadicScales M b F).length =
      (Int.log 2 (64 * F * b) - Int.clog 2 ((b : ℚ) / M) + 1).toNat := by
  simp only [groupDyadicScales, List.length_map, integerClosedRange, List.length_range]

theorem groupDyadicScales_length_dyadic (eM eb eF : ℕ) :
    (groupDyadicScales (2 ^ eM) (2 ^ eb) ((2 : ℚ) ^ eF)).length = 7 + eM + eF := by
  have hlower : ((2 ^ eb : ℕ) : ℚ) / (2 ^ eM : ℕ) = (2 : ℚ) ^ ((eb : ℤ) - eM) := by
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0),
      zpow_natCast, zpow_natCast]
  have hupper : (64 : ℚ) * (2 : ℚ) ^ eF * (2 ^ eb : ℕ) =
      (2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, zpow_natCast, pow_add, pow_add]
    norm_num
  have hlog : Int.log 2 ((2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ)) = ((6 + eF + eb : ℕ) : ℤ) := by
    simpa only [Nat.cast_ofNat] using Int.log_zpow (R := ℚ) (by decide : 1 < 2) ((6 + eF + eb : ℕ) : ℤ)
  have hclog : Int.clog 2 ((2 : ℚ) ^ ((eb : ℤ) - eM)) = (eb : ℤ) - eM := by
    simpa only [Nat.cast_ofNat] using Int.clog_zpow (R := ℚ) (by decide : 1 < 2) ((eb : ℤ) - eM)
  rw [groupDyadicScales_length, hlower, hupper, hlog, hclog]
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GroupSamplingWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The shared group samples cancel the reciprocal envelope factor in
the number of possible rounded child inputs, including exact evaluation. -/

namespace EditApproximation

theorem groupSampleCount_shared_work {M Q b : ℕ} {h : ℚ}
    (hM : 0 < M) (hQ : 1 ≤ Q) (hb : 0 < b) (hh : 0 < h)
    (hfloor : (b : ℚ) / M ≤ h) :
    (groupSampleCount M Q b h : ℚ) * (1 + b / h) ≤ 3 * Q * M := by
  have hMr : (0 : ℚ) < M := by exact_mod_cast hM
  have hQr : (1 : ℚ) ≤ Q := by exact_mod_cast hQ
  have hbr : (0 : ℚ) < b := by exact_mod_cast hb
  have hMh : (b : ℚ) ≤ M * h := by
    nlinarith only [(div_le_iff₀ hMr).mp hfloor]
  have hQproduct := mul_le_mul_of_nonneg_right hQr (show (0 : ℚ) ≤ M * h by positivity)
  have hx : (1 : ℚ) ≤ Q * M * h / b := by
    apply (le_div_iff₀ hbr).2
    nlinarith only [hMh, hQproduct]
  have hceil : (⌈(Q : ℚ) * M * h / b⌉₊ : ℚ) < (Q : ℚ) * M * h / b + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hkM : (groupSampleCount M Q b h : ℚ) ≤ M := by
    unfold groupSampleCount
    exact_mod_cast (min_le_left M ⌈(Q : ℚ) * M * h / b⌉₊)
  have hkceil : (groupSampleCount M Q b h : ℚ) ≤ ⌈(Q : ℚ) * M * h / b⌉₊ := by
    unfold groupSampleCount
    exact_mod_cast (min_le_right M ⌈(Q : ℚ) * M * h / b⌉₊)
  have hkX : (groupSampleCount M Q b h : ℚ) ≤ 2 * ((Q : ℚ) * M * h / b) := by
    linarith only [hkceil, hceil, hx]
  have hkb : (groupSampleCount M Q b h : ℚ) * b ≤ 2 * Q * M * h := by
    apply (le_div_iff₀ hbr).mp
    convert hkX using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hreciprocal : (groupSampleCount M Q b h : ℚ) * b / h ≤ 2 * Q * M :=
    (div_le_iff₀ hh).2 hkb
  have hQM := mul_le_mul_of_nonneg_right hQr hMr.le
  calc
    _ = (groupSampleCount M Q b h : ℚ) + (groupSampleCount M Q b h : ℚ) * b / h := by ring
    _ ≤ (M : ℚ) + 2 * Q * M := add_le_add hkM hreciprocal
    _ ≤ 3 * Q * M := by nlinarith only [hQM]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RoundedGroupStates
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Enumerating rounded endpoints with a length-gap guard costs only
one wide coordinate and one envelope coordinate. -/

namespace EditApproximation



theorem gridGapStates_length_le (n g anchor radius sourceLength gapRadius : ℕ) (hg : 0 < g) :
    (gridGapStates n g anchor radius sourceLength gapRadius).length ≤
      (2 * radius / g + 2) * (2 * gapRadius / g + 2) := by
  have hpoint (p rad : ℕ) : (gridPointsBetween g (p - rad) (p + rad)).length ≤ 2 * rad / g + 2 := by
    exact (gridPointsBetween_length_le g _ _ hg).trans
      (Nat.add_le_add_right (Nat.div_le_div_right (by omega : p + rad - (p - rad) ≤ 2 * rad)) 2)
  have h := list_flatMap_length_le (gridPointsBetween g (anchor - radius) (anchor + radius))
    (fun lo => (gridPointsBetween g (lo + sourceLength - gapRadius) (lo + sourceLength + gapRadius)).filterMap
      fun hi => makeTargetState n lo hi) (2 * gapRadius / g + 2)
    (fun lo _ => (List.length_filterMap_le _ _).trans (hpoint (lo + sourceLength) gapRadius))
  exact h.trans (Nat.mul_le_mul_right _ (hpoint anchor radius))

/-- The spacing dominates h/K and one. This includes the spacing-one
case for fractional envelopes. No success or accuracy event is needed. -/
theorem gridGapStates_rounded_count (n g anchor sourceLength b : ℕ) (h K : ℚ)
    (hg : 0 < g) (hh : 0 < h) (hK : 1 ≤ K) (hspacing : h ≤ K * g) :
    ((gridGapStates n g anchor (12 * b) sourceLength ⌈2 * h⌉₊).length : ℚ) ≤
      208 * K ^ 2 * (1 + b / h) := by
  have hgr : (0 : ℚ) < g := by exact_mod_cast hg
  have hg1 : (1 : ℚ) ≤ g := by exact_mod_cast hg
  have hKr : 0 ≤ K := le_trans zero_le_one hK
  have hb : (0 : ℚ) ≤ b := Nat.cast_nonneg _
  have hfirstDiv : ((24 * b / g : ℕ) : ℚ) ≤ 24 * K * b / h := by
    apply (Nat.cast_div_le (m := 24 * b) (n := g)).trans
    push_cast
    apply (div_le_div_iff₀ hgr hh).2
    have hm := mul_le_mul_of_nonneg_right hspacing (show (0 : ℚ) ≤ 24 * b by positivity)
    nlinarith only [hm]
  have hceil : (⌈2 * h⌉₊ : ℚ) < 2 * h + 1 := Nat.ceil_lt_add_one (by positivity)
  have hsecondDiv : ((2 * ⌈2 * h⌉₊ / g : ℕ) : ℚ) ≤ 4 * K + 2 := by
    apply (Nat.cast_div_le (m := 2 * ⌈2 * h⌉₊) (n := g)).trans
    push_cast
    apply (div_le_iff₀ hgr).2
    nlinarith only [hceil, hspacing, hg1]
  have hratio : 0 ≤ (b : ℚ) / h := div_nonneg hb hh.le
  have hfirst : (((2 * (12 * b) / g + 2 : ℕ) : ℚ)) ≤ 26 * K * (1 + b / h) := by
    have heq : 2 * (12 * b) = 24 * b := by omega
    rw [heq, Nat.cast_add, Nat.cast_ofNat]
    have hquotient : 24 * K * b / h = 24 * K * (b / h) := by ring
    rw [hquotient] at hfirstDiv
    have hKr' := mul_nonneg hKr hratio
    nlinarith only [hfirstDiv, hK, hKr']
  have hsecond : (((2 * ⌈2 * h⌉₊ / g + 2 : ℕ) : ℚ)) ≤ 8 * K := by
    rw [Nat.cast_add, Nat.cast_ofNat]
    linarith only [hsecondDiv, hK]
  have hlength : ((gridGapStates n g anchor (12 * b) sourceLength ⌈2 * h⌉₊).length : ℚ) ≤
      (((2 * (12 * b) / g + 2 : ℕ) : ℚ)) * (((2 * ⌈2 * h⌉₊ / g + 2 : ℕ) : ℚ)) := by
    exact_mod_cast gridGapStates_length_le n g anchor (12 * b) sourceLength ⌈2 * h⌉₊ hg
  apply hlength.trans
  calc
    _ ≤ (26 * K * (1 + b / h)) * (8 * K) :=
      mul_le_mul hfirst hsecond (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

theorem shared_rounded_inputs_bound {M Q b : ℕ} {h K states : ℚ}
    (hM : 0 < M) (hQ : 1 ≤ Q) (hb : 0 < b) (hh : 0 < h)
    (hfloor : (b : ℚ) / M ≤ h) (hstates : states ≤ 208 * K ^ 2 * (1 + b / h)) :
    (groupSampleCount M Q b h : ℚ) * states ≤ 624 * M * Q * K ^ 2 := by
  have hwork := groupSampleCount_shared_work hM hQ hb hh hfloor
  have hstateBound := mul_le_mul_of_nonneg_left hstates
    (Nat.cast_nonneg (α := ℚ) (groupSampleCount M Q b h))
  have hworkBound := mul_le_mul_of_nonneg_left hwork (by positivity : (0 : ℚ) ≤ 208 * K ^ 2)
  nlinarith only [hstateBound, hworkBound]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ActualRoundedGroupInputs
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Every actual unskipped rounded group input belongs to a common
small endpoint list determined by the cell, child and envelope label. -/

namespace EditApproximation



theorem groupRoundSpacing_envelope_bound (exponent : ℕ) (h : ℚ) :
    h ≤ (2 : ℚ) ^ exponent * groupRoundSpacing exponent h := by
  have hpow : (0 : ℚ) < (2 : ℚ) ^ exponent := by positivity
  have hceil : (2 : ℚ) ^ (-(exponent : ℤ)) * h ≤ (groupRoundSpacing exponent h : ℚ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  have hmul := mul_le_mul_of_nonneg_left hceil hpow.le
  rw [zpow_neg, zpow_natCast] at hmul
  simpa only [← mul_assoc, mul_inv_cancel₀ hpow.ne', one_mul] using hmul

theorem groupRoundedStateList_length {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b exponent : ℕ) (cell : ℕ × ℕ)
    (i : Fin M) (h : ℚ) (hh : 0 < h) :
    ((groupRoundedStateList source target parent b exponent cell i h).length : ℚ) ≤
      208 * ((2 : ℚ) ^ exponent) ^ 2 * (1 + b / h) := by
  exact gridGapStates_rounded_count _ _ _ _ b h ((2 : ℚ) ^ exponent)
    (groupRoundSpacing_pos exponent h) hh (one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2))
    (groupRoundSpacing_envelope_bound exponent h)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalCells
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Direct bounded-range enumeration of the cells meeting a query square. -/

namespace EditApproximation



theorem localCellCoordinates_length_le (side : ℚ) (hside : 0 < side)
    (p radius K : ℕ) (hbudget : 2 * (radius : ℚ) / side ≤ K) :
    (localCellCoordinates side p radius).length ≤ K + 2 := by
  let first := ⌊((p - radius : ℕ) : ℚ) / side⌋₊
  let last := ⌊((p + radius : ℕ) : ℚ) / side⌋₊
  have horder : first ≤ last := Nat.floor_le_floor (div_le_div_of_nonneg_right
    (by exact_mod_cast (show p - radius ≤ p + radius by omega)) hside.le)
  have hhi : (last : ℚ) ≤ ((p + radius : ℕ) : ℚ) / side :=
    Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hside.le)
  have hlo : ((p - radius : ℕ) : ℚ) / side < (first : ℚ) + 1 := Nat.lt_floor_add_one _
  have hwidth : ((p + radius : ℕ) : ℚ) - ((p - radius : ℕ) : ℚ) ≤ 2 * radius := by
    have h : p + radius - (p - radius) ≤ 2 * radius := by omega
    have hR : ((p + radius - (p - radius) : ℕ) : ℚ) ≤ ((2 * radius : ℕ) : ℚ) := by exact_mod_cast h
    simpa only [Nat.cast_sub (show p - radius ≤ p + radius by omega), Nat.cast_mul, Nat.cast_ofNat] using hR
  have hquotient : ((p + radius : ℕ) : ℚ) / side - ((p - radius : ℕ) : ℚ) / side ≤ K := by
    calc
      _ = (((p + radius : ℕ) : ℚ) - ((p - radius : ℕ) : ℚ)) / side := by ring
      _ ≤ (2 * radius) / side := div_le_div_of_nonneg_right hwidth hside.le
      _ ≤ K := hbudget
  have hcount : ((last + 1 - first : ℕ) : ℚ) < (K : ℚ) + 2 := by
    rw [Nat.cast_sub (by omega : first ≤ last + 1), Nat.cast_add, Nat.cast_one]
    linarith only [hhi, hlo, hquotient]
  have hcountN : last + 1 - first < K + 2 := by exact_mod_cast hcount
  exact (by simpa only [localCellCoordinates, List.length_range', first, last] using hcountN.le)



theorem localTargetCells_length_le {n : ℕ} (side : ℚ) (hside : 0 < side)
    (radius K : ℕ) (q : TargetInterval n) (hbudget : 2 * (radius : ℚ) / side ≤ K) :
    (localTargetCells side radius q).length ≤ (K + 2) ^ 2 := by
  have hfirst := localCellCoordinates_length_le side hside q.lo radius K hbudget
  have hsecond := localCellCoordinates_length_le side hside q.hi radius K hbudget
  have h := list_flatMap_length_le (localCellCoordinates side q.lo radius)
    (fun lo => (localCellCoordinates side q.hi radius).map fun hi => (lo, hi)) (K + 2)
    (fun lo _ => by simpa only [List.length_map] using hsecond)
  exact h.trans (by simpa only [pow_two] using Nat.mul_le_mul_right (K + 2) hfirst)

/-- Every retained query scale has only polynomially many nearby cells,
even when the initial seed is inaccurate. -/
theorem localTargetCells_query_length {n : ℕ} (F b exponent : ℕ)
    (q : TargetInterval n) (w : ℚ) (hF : 1 ≤ F) (hb : 1 ≤ b)
    (hw : 0 ≤ w) (hwindow : w / (16 * F) ≤ b) :
    (localTargetCells ((2 : ℚ) ^ (-(exponent : ℤ)) * b) ⌈w⌉₊ q).length ≤
      ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 := by
  have hFpos : (0 : ℚ) < F := by exact_mod_cast (by omega : 0 < F)
  have hbpos : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
  have hbR : (1 : ℚ) ≤ b := by exact_mod_cast hb
  have hside : 0 < (2 : ℚ) ^ (-(exponent : ℤ)) * b := by positivity
  apply localTargetCells_length_le _ hside _ ((32 * F + 2) * 2 ^ exponent) q
  apply (div_le_iff₀ hside).2
  have hwidth : w ≤ 16 * (F : ℚ) * b :=
    by nlinarith only [(div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hwindow]
  have hceil : (⌈w⌉₊ : ℚ) < w + 1 := Nat.ceil_lt_add_one hw
  have hcancel : (((32 * F + 2) * 2 ^ exponent : ℕ) : ℚ) *
      ((2 : ℚ) ^ (-(exponent : ℤ)) * b) = (32 * (F : ℚ) + 2) * b := by
    push_cast
    rw [zpow_neg, zpow_natCast]
    field_simp
  rw [hcancel]
  nlinarith only [hceil, hwidth, hbR]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DyadicQueryWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The query scale window has length controlled by the refinement
factor, independently of the number of dyadic scales below N. -/

namespace EditApproximation

open Finset



theorem dyadicQueryWindow_length_le (N C : ℕ) (w a F : ℚ)
    (ha : 1 ≤ a) (hF : 1 ≤ F)
    (hbudget : 128 * a * F ≤ (2 : ℚ) ^ C) :
    (dyadicQueryWindow N w a F).length ≤ C + 1 := by
  let keep : ℕ → Bool := fun e => decide (w / (16 * F) ≤ (2 ^ e : ℕ) ∧
    ((2 ^ e : ℕ) : ℚ) ≤ 8 * a * w)
  let indices := ((List.range (Nat.log 2 N + 1)).filter keep).toFinset
  have hlength : (dyadicQueryWindow N w a F).length = indices.card := by
    simp only [dyadicQueryWindow, dyadicScales, List.filter_map, List.length_map]
    exact (List.toFinset_card_of_nodup
      ((show (List.range (Nat.log 2 N + 1)).Nodup from List.nodup_range).filter keep)).symm
  rw [hlength]
  by_cases hnonempty : indices.Nonempty
  · let first := indices.min' hnonempty
    have hfirst : first ∈ indices := Finset.min'_mem _ _
    have hfirstKeep : w / (16 * F) ≤ (2 ^ first : ℕ) ∧ ((2 ^ first : ℕ) : ℚ) ≤ 8 * a * w :=
      of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hfirst)).2
    have hFpos : 0 < F := lt_of_lt_of_le zero_lt_one hF
    have hwfirst : w ≤ 16 * F * (2 ^ first : ℕ) := by
      nlinarith only [(div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hfirstKeep.1]
    have hsub : indices ⊆ Finset.Icc first (first + C) := by
      intro e he
      have hkeep : w / (16 * F) ≤ (2 ^ e : ℕ) ∧ ((2 ^ e : ℕ) : ℚ) ≤ 8 * a * w :=
        of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp he)).2
      have hmul := mul_le_mul_of_nonneg_left hwfirst (show 0 ≤ 8 * a by positivity)
      have hpower := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg (α := ℚ) (2 ^ first))
      have hbound : ((2 ^ e : ℕ) : ℚ) ≤ (2 : ℚ) ^ C * (2 ^ first : ℕ) := by
        nlinarith only [hkeep.2, hmul, hpower]
      have hboundN : 2 ^ e ≤ 2 ^ (first + C) := by
        have heq : (2 : ℚ) ^ C * (2 ^ first : ℕ) = ((2 ^ (first + C) : ℕ) : ℚ) := by
          push_cast
          rw [pow_add]
          ring
        rw [heq] at hbound
        exact_mod_cast hbound
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ he,
        (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hboundN⟩
    have hcard := Finset.card_le_card hsub
    have hinterval : (Finset.Icc first (first + C)).card = C + 1 := by rw [Nat.card_Icc]; omega
    rwa [hinterval] at hcard
  · simpa only [Finset.not_nonempty_iff_eq_empty.mp hnonempty, Finset.card_empty] using Nat.zero_le (C + 1)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SeedFactorSchedule
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The literal dyadic factor schedule stops at A<=F. Each active pass
replaces A by 4A/F and uses the integer factor a=A/F. -/

namespace EditApproximation





theorem computedSeed_initial_factor (N : ℕ) :
    (2 : ℚ) ^ computedSeedInitialExponent N =
      ((integerParameters N).initialFactor : ℚ) := by
  simp only [computedSeedInitialExponent, integerParameters, inputHeight, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_mul, Nat.mul_comm]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalQueryBudget
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal online loop is bounded by the applicable scale window,
which is polynomial in ell throughout the computed factor schedule. -/

namespace EditApproximation

open Finset

theorem refinement_query_window_length (N F initialExponent : ℕ) (A w : ℚ)
    (hF : 1 ≤ F) (hFbound : (F : ℚ) ≤ (2 : ℚ) ^ initialExponent)
    (hAbound : A ≤ (2 : ℚ) ^ initialExponent) :
    (dyadicQueryWindow N w (refinementFactor A F) F).length ≤ initialExponent + 8 := by
  have hFpos : (0 : ℚ) < F := by exact_mod_cast (by omega : 0 < F)
  have hfactor : refinementFactor A F ≤ (2 : ℚ) ^ initialExponent / F := by
    apply max_le
    · exact (le_div_iff₀ hFpos).2 (by simpa only [one_mul] using hFbound)
    · exact div_le_div_of_nonneg_right hAbound hFpos.le
  have hproduct := mul_le_mul_of_nonneg_right hfactor hFpos.le
  rw [div_mul_cancel₀ _ hFpos.ne'] at hproduct
  have hbudget : 128 * refinementFactor A F * F ≤ (2 : ℚ) ^ (initialExponent + 7) := by
    have h := mul_le_mul_of_nonneg_left hproduct (by norm_num : (0 : ℚ) ≤ 128)
    rw [pow_add]
    norm_num only [show (2 : ℚ) ^ 7 = 128 by norm_num]
    nlinarith only [h]
  simpa only [Nat.add_assoc, show (7 : ℕ) + 1 = 8 by rfl] using
    dyadicQueryWindow_length_le N (initialExponent + 7) w (refinementFactor A F) F
      (le_max_left _ _) (by exact_mod_cast hF) hbudget

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGroupBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded local cell loops on arbitrary initial seeds. -/

namespace EditApproximation

theorem localCellGroupActions_length {α : Type*} {M : ℕ} (source target : List α)
    (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (q : TargetInterval target.length)
    (hF : 1 ≤ F) (hw : 0 ≤ parentInitial q) :
    (localCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw q).length ≤
      (dyadicQueryWindow N (parentInitial q) a F).length *
        ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 := by
  unfold localCellGroupActions
  apply list_flatMap_length_le
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hbpos : 1 ≤ b := by
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hb).1
    exact Nat.one_le_two_pow
  exact (List.length_filterMap_le _ _).trans
    (localTargetCells_query_length F b exponent q (parentInitial q) hF hbpos hw hwindow.1)

theorem localCellGroupActions_length_refinement {α : Type*} {M : ℕ} (source target : List α)
    (parent : TargetInterval source.length) (N P F exponent Q initialExponent : ℕ) (tau A : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (q : TargetInterval target.length)
    (hF : 1 ≤ F) (hw : 0 ≤ parentInitial q)
    (hFbound : (F : ℚ) ≤ (2 : ℚ) ^ initialExponent)
    (hAbound : A ≤ (2 : ℚ) ^ initialExponent) :
    (localCellGroupActions source target parent N P F exponent Q tau (refinementFactor A F) parentInitial
      child initial current draw q).length ≤
      (initialExponent + 8) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 := by
  exact (localCellGroupActions_length source target parent N P F exponent Q tau (refinementFactor A F)
    parentInitial child initial current draw q hF hw).trans
    (Nat.mul_le_mul_right _ (refinement_query_window_length N F initialExponent A (parentInitial q)
      hF hFbound hAbound))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SharedGroupInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A pathwise finite cover for every shared group estimator's current
child inputs. Repeated samples and member uses are counted once. -/

namespace EditApproximation

open Finset



theorem groupQueriedChildLabels_card (M Q b : ℕ) (h : ℚ)
    (draw : Fin (groupSampleCount M Q b h) → Fin M) :
    (groupQueriedChildLabels M Q b h draw).card ≤ groupSampleCount M Q b h := by
  unfold groupQueriedChildLabels
  split_ifs with hexact
  · simpa only [Finset.card_univ, Fintype.card_fin, hexact] using le_rfl (a := M)
  · exact (Finset.card_image_le).trans_eq (by simp only [Finset.card_univ, Fintype.card_fin])



/-- One group and one envelope label use at most 624*M*Q*theta^-2
distinct current child inputs, on every seed and every sample outcome. -/
theorem groupCurrentInputCover_card {α : Type*} (source target : List α) {M b : ℕ}
    (parent : TargetInterval source.length) (exponent Q : ℕ) (cell : ℕ × ℕ) (h : ℚ)
    (hM : 0 < M) (hQ : 1 ≤ Q) (hb : 0 < b) (hh : 0 < h) (hfloor : (b : ℚ) / M ≤ h)
    (draw : Fin (groupSampleCount M Q b h) → Fin M) :
    ((groupCurrentInputCover source target parent b exponent Q cell h draw).card : ℚ) ≤
      624 * M * Q * ((2 : ℚ) ^ exponent) ^ 2 := by
  let labels := groupQueriedChildLabels M Q b h draw
  let C : ℚ := 208 * ((2 : ℚ) ^ exponent) ^ 2 * (1 + b / h)
  have hC : 0 ≤ C := by dsimp only [C] <;> positivity
  have hlength (i : Fin M) :
      ((groupRoundedStateList source target parent b exponent cell i h).length : ℚ) ≤ C :=
    groupRoundedStateList_length source target parent b exponent cell i h hh
  have hcardN : (groupCurrentInputCover source target parent b exponent Q cell h draw).card ≤
      ∑ i ∈ labels, (groupRoundedStateList source target parent b exponent cell i h).length := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro i _
    exact Finset.card_image_le.trans (List.toFinset_card_le _)
  have hcardR : ((groupCurrentInputCover source target parent b exponent Q cell h draw).card : ℚ) ≤
      ∑ i ∈ labels, ((groupRoundedStateList source target parent b exponent cell i h).length : ℚ) := by
    exact_mod_cast hcardN
  have hlabels : (labels.card : ℚ) ≤ groupSampleCount M Q b h := by
    exact_mod_cast groupQueriedChildLabels_card M Q b h draw
  calc
    _ ≤ ∑ i ∈ labels, ((groupRoundedStateList source target parent b exponent cell i h).length : ℚ) := hcardR
    _ ≤ ∑ _i ∈ labels, C := Finset.sum_le_sum (fun i _ => hlength i)
    _ = (labels.card : ℚ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (groupSampleCount M Q b h : ℚ) * C := mul_le_mul_of_nonneg_right hlabels hC
    _ ≤ _ := shared_rounded_inputs_bound hM hQ hb hh hfloor le_rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CurrentQueryInputs
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Distinct current-index inputs of the bounded query loops. The cover
includes all whole-cell shared estimates, selected cell actions, and
online actions; repeated uses do not add recursive calls. -/

namespace EditApproximation

open Finset

theorem groupDyadicScales_lower {M b F : ℕ} (hM : 0 < M) (hb : 0 < b)
    (hF : 0 < F) (h : ℚ) (hh : h ∈ groupDyadicScales M b F) :
    (b : ℚ) / M ≤ h := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hh
  exact ((groupDyadicScales_mem hM hb (F : ℚ) (by exact_mod_cast hF) e).mp
    (List.mem_map.mpr ⟨e, he, rfl⟩)).1



theorem localGroupQueryKeys_scale {n N F exponent : ℕ} {a : ℚ}
    {initial : TargetInterval n → ℚ} {q : TargetInterval n} {key : ℕ × (ℕ × ℕ)}
    (hkey : key ∈ localGroupQueryKeys N F exponent a initial q) :
    key.1 ∈ dyadicScales N := by
  obtain ⟨b, hb, hcell⟩ := List.mem_flatMap.mp hkey
  obtain ⟨cell, _, rfl⟩ := List.mem_map.mp hcell
  exact (List.mem_filter.mp hb).1

theorem localGroupQueryKeys_length {n : ℕ} (N F exponent : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n)
    (hF : 1 ≤ F) (hw : 0 ≤ initial q) :
    (localGroupQueryKeys N F exponent a initial q).length ≤
      (dyadicQueryWindow N (initial q) a F).length *
        ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 := by
  unfold localGroupQueryKeys
  apply list_flatMap_length_le
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hbpos : 1 ≤ b := by
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hb).1
    exact Nat.one_le_two_pow
  simpa only [List.length_map] using
    localTargetCells_query_length F b exponent q (initial q) hF hbpos hw hwindow.1



theorem querySharedInputCover_card {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N F exponent Q labels : ℕ) (a : ℚ)
    (initial : TargetInterval target.length → ℚ) (q : TargetInterval target.length)
    (draw : CellGroupDraws M F Q) (hM : 0 < M) (hF : 1 ≤ F) (hQ : 1 ≤ Q)
    (hlabels : ∀ b ∈ dyadicScales N, (groupDyadicScales M b F).length ≤ labels) :
    ((querySharedInputCover source target parent N F exponent Q a initial q draw).card : ℚ) ≤
      (localGroupQueryKeys N F exponent a initial q).length * labels *
        (624 * M * Q * ((2 : ℚ) ^ exponent) ^ 2) := by
  let keys := (localGroupQueryKeys N F exponent a initial q).toFinset
  let C : ℚ := 624 * M * Q * ((2 : ℚ) ^ exponent) ^ 2
  have hC : 0 ≤ C := by dsimp only [C] <;> positivity
  have hper (key : ℕ × (ℕ × ℕ)) (hk : key ∈ keys) :
      ((Finset.univ.biUnion fun scale : Fin (groupDyadicScales M key.1 F).length =>
        groupCurrentInputCover source target parent key.1 exponent Q key.2
          (groupDyadicScaleAt M key.1 F scale) (draw key.1 key.2 scale)).card : ℚ) ≤ labels * C := by
    have hb := localGroupQueryKeys_scale (List.mem_toFinset.mp hk)
    have hbpos : 0 < key.1 := by
      obtain ⟨e, _, he⟩ := List.mem_map.mp hb
      rw [← he]
      positivity
    have hcard := Finset.card_biUnion_le (s := (Finset.univ :
      Finset (Fin (groupDyadicScales M key.1 F).length)))
      (t := fun scale => groupCurrentInputCover source target parent key.1 exponent Q key.2
        (groupDyadicScaleAt M key.1 F scale) (draw key.1 key.2 scale))
    have hcardR : ((Finset.univ.biUnion fun scale : Fin (groupDyadicScales M key.1 F).length =>
        groupCurrentInputCover source target parent key.1 exponent Q key.2
          (groupDyadicScaleAt M key.1 F scale) (draw key.1 key.2 scale)).card : ℚ) ≤
        ∑ scale : Fin (groupDyadicScales M key.1 F).length,
        ((groupCurrentInputCover source target parent key.1 exponent Q key.2
          (groupDyadicScaleAt M key.1 F scale) (draw key.1 key.2 scale)).card : ℚ) := by
      exact_mod_cast hcard
    apply hcardR.trans
    have hscale (scale : Fin (groupDyadicScales M key.1 F).length) :=
      List.get_mem (groupDyadicScales M key.1 F) scale
    calc
      _ ≤ ∑ _scale : Fin (groupDyadicScales M key.1 F).length, C := by
        apply Finset.sum_le_sum
        intro scale _
        exact groupCurrentInputCover_card source target parent exponent Q key.2 _ hM hQ hbpos
          (groupDyadicScales_pos (hscale scale))
          (groupDyadicScales_lower hM hbpos (by omega) _ (hscale scale)) _
      _ = (groupDyadicScales M key.1 F).length * C := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ labels * C := mul_le_mul_of_nonneg_right (by exact_mod_cast hlabels key.1 hb) hC
  have hcard := Finset.card_biUnion_le (s := keys)
    (t := fun key => Finset.univ.biUnion fun scale : Fin (groupDyadicScales M key.1 F).length =>
      groupCurrentInputCover source target parent key.1 exponent Q key.2
        (groupDyadicScaleAt M key.1 F scale) (draw key.1 key.2 scale))
  have hcardR : ((querySharedInputCover source target parent N F exponent Q a initial q draw).card : ℚ) ≤
      ∑ key ∈ keys, ((Finset.univ.biUnion fun scale : Fin (groupDyadicScales M key.1 F).length =>
        groupCurrentInputCover source target parent key.1 exponent Q key.2
          (groupDyadicScaleAt M key.1 F scale) (draw key.1 key.2 scale)).card : ℚ) := by
    exact_mod_cast hcard
  calc
    _ ≤ ∑ key ∈ keys, ((Finset.univ.biUnion fun scale : Fin (groupDyadicScales M key.1 F).length =>
        groupCurrentInputCover source target parent key.1 exponent Q key.2
          (groupDyadicScaleAt M key.1 F scale) (draw key.1 key.2 scale)).card : ℚ) := hcardR
    _ ≤ ∑ _key ∈ keys, labels * C := Finset.sum_le_sum hper
    _ = (keys.card : ℚ) * (labels * C) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (localGroupQueryKeys N F exponent a initial q).length * (labels * C) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast List.toFinset_card_le _) (mul_nonneg (Nat.cast_nonneg _) hC)
    _ = _ := by ring



theorem actionCurrentInputCover_card {Parent Child : Type*} [DecidableEq Child] {M : ℕ}
    (actions : List (RationalBellmanAction Parent Child M)) :
    (actionCurrentInputCover actions).card ≤ actions.length * M := by
  unfold actionCurrentInputCover
  have hindices : (List.finRange actions.length).toFinset = (Finset.univ : Finset (Fin actions.length)) := by
    ext i
    simp
  rw [hindices]
  apply Finset.card_biUnion_le.trans
  apply (Finset.sum_le_sum (fun _ _ => Finset.card_image_le)).trans_eq
  simp only [Finset.card_univ, Fintype.card_fin, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

theorem currentQueryInputCover_card {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q labels : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (q : TargetInterval target.length)
    (online : List (PhysicalRationalAction M target.length))
    (hM : 0 < M) (hF : 1 ≤ F) (hQ : 1 ≤ Q)
    (hlabels : ∀ b ∈ dyadicScales N, (groupDyadicScales M b F).length ≤ labels) :
    ((currentQueryInputCover source target parent N P F exponent Q tau a parentInitial
      child initial current draw q online).card : ℚ) ≤
      (localGroupQueryKeys N F exponent a parentInitial q).length * labels *
        (624 * M * Q * ((2 : ℚ) ^ exponent) ^ 2) +
      (localCellGroupActions source target parent N P F exponent Q tau a parentInitial
        child initial current draw q).length * M + online.length * M := by
  have hcard := Finset.card_union_le
    (querySharedInputCover source target parent N F exponent Q a parentInitial q draw ∪
      actionCurrentInputCover (localCellGroupActions source target parent N P F exponent Q tau a parentInitial
        child initial current draw q)) (actionCurrentInputCover online)
  have hleft := Finset.card_union_le
    (querySharedInputCover source target parent N F exponent Q a parentInitial q draw)
    (actionCurrentInputCover (localCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw q))
  have hN := hcard.trans (Nat.add_le_add_right hleft _)
  have hR : ((currentQueryInputCover source target parent N P F exponent Q tau a parentInitial
      child initial current draw q online).card : ℚ) ≤
      (querySharedInputCover source target parent N F exponent Q a parentInitial q draw).card +
      (actionCurrentInputCover (localCellGroupActions source target parent N P F exponent Q tau a parentInitial
        child initial current draw q)).card + (actionCurrentInputCover online).card := by exact_mod_cast hN
  apply hR.trans
  exact add_le_add (add_le_add
    (querySharedInputCover_card source target parent N F exponent Q labels a parentInitial q draw hM hF hQ hlabels)
    (by exact_mod_cast (actionCurrentInputCover_card
      (localCellGroupActions source target parent N P F exponent Q tau a parentInitial child initial current draw q))))
    (by exact_mod_cast (actionCurrentInputCover_card online))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_WideEarlierInputs
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Wide enumeration gathers child states before scoring its Cartesian
action list. Its recursive input count depends on the coordinate lists,
rather than the exponentially larger number of complete actions. -/

namespace EditApproximation

open Finset

theorem wideEarlierChildStateList_length_le {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (hP : 0 < P) (i : Fin M) :
    (wideChildStateList parent r b P i).length ≤ (40 * P + 2) ^ 2 := by
  have hlocal := gridStateBox_length_le ny (seedGridSpacing b P) (10 * b)
    (r.lo + ((sourceChild parent i).lo - parent.lo))
    (r.lo + ((sourceChild parent i).hi - parent.lo))
    (by unfold seedGridSpacing; omega)
  apply hlocal.trans
  apply Nat.pow_le_pow_left
  simpa only [show 2 * (10 * b) = 20 * b by omega] using seedGridSpacing_radius_count b P hP



theorem wideEarlierInputCover_card {nx ny M : ℕ} (parent : TargetInterval nx) (P history : ℕ)
    (representatives : List (ℕ × TargetInterval ny)) (hP : 0 < P) :
    (wideEarlierInputCover (M := M) parent P history representatives).card ≤
      representatives.length * M * history * (40 * P + 2) ^ 2 := by
  have hstates (br : ℕ × TargetInterval ny) (i : Fin M) (t : ℕ) :
      (((wideChildStateList parent br.2 br.1 P i).toFinset).image fun r => (i, t, r)).card ≤
        (40 * P + 2) ^ 2 :=
    (Finset.card_image_le).trans ((List.toFinset_card_le _).trans
      (wideEarlierChildStateList_length_le parent br.2 br.1 P hP i))
  have hhistory (br : ℕ × TargetInterval ny) (i : Fin M) :
      ((Finset.range history).biUnion fun t =>
        ((wideChildStateList parent br.2 br.1 P i).toFinset).image fun r => (i, t, r)).card ≤
        history * (40 * P + 2) ^ 2 := by
    exact Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum fun t _ => hstates br i t).trans_eq (by simp))
  have hchildren (br : ℕ × TargetInterval ny) :
      (Finset.univ.biUnion fun i : Fin M =>
        (Finset.range history).biUnion fun t =>
          ((wideChildStateList parent br.2 br.1 P i).toFinset).image fun r => (i, t, r)).card ≤
        M * (history * (40 * P + 2) ^ 2) := by
    exact Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum fun i _ => hhistory br i).trans_eq (by simp))
  unfold wideEarlierInputCover
  calc
    _ ≤ ∑ br ∈ representatives.toFinset, M * (history * (40 * P + 2) ^ 2) :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun br _ => hchildren br)
    _ = representatives.toFinset.card * (M * (history * (40 * P + 2) ^ 2)) := by simp
    _ ≤ representatives.length * (M * (history * (40 * P + 2) ^ 2)) :=
      Nat.mul_le_mul_right _ (List.toFinset_card_le representatives)
    _ = _ := by ring

theorem localRefinementRepresentatives_length {n : ℕ} (N P F : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (hP : 0 < P) (hF : 1 ≤ F) :
    (localRefinementRepresentatives N P F a initial q).length ≤
      (dyadicQueryWindow N (initial q) a F).length * (64 * F * P + 2) ^ 2 := by
  unfold localRefinementRepresentatives
  apply list_flatMap_length_le
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hceil : ⌈initial q⌉₊ ≤ 16 * F * b := by
    apply Nat.ceil_le.mpr
    have hFpos : (0 : ℚ) < F := Nat.cast_pos.mpr (by omega)
    have h := (div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hwindow.1
    push_cast
    nlinarith only [h]
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hcover : b ≤ 2 * P * seedGridSpacing b P := by
    have hquot : b / P ≤ seedGridSpacing b P := le_max_right _ _
    have hdiv := Nat.lt_mul_div_succ b hP
    nlinarith only [hquot, hdiv, hg]
  have hcount : 2 * ⌈initial q⌉₊ / seedGridSpacing b P + 2 ≤ 64 * F * P + 2 := by
    have hprod : 2 * ⌈initial q⌉₊ ≤ 64 * F * P * seedGridSpacing b P := by
      nlinarith only [hceil, Nat.mul_le_mul_left (32 * F) hcover]
    have hdiv := Nat.div_mul_le_self (2 * ⌈initial q⌉₊) (seedGridSpacing b P)
    have hquot : 2 * ⌈initial q⌉₊ / seedGridSpacing b P ≤ 64 * F * P := by
      nlinarith only [hprod, hdiv, hg]
    exact Nat.add_le_add_right hquot 2
  have hlocal := localTargetStates_length_le (radius := ⌈initial q⌉₊) hg q
  simpa only [List.length_map] using
    (List.length_filter_le _ _).trans (hlocal.trans (Nat.pow_le_pow_left hcount 2))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryEarlierInputs
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryScaleDispatchWithWork_value _root_.OAI.EditApproximation.queryScalePresentWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! All wide-coordinate requests needed for one local query can be gathered
from bounded representative lists, including complete requested cells and
the rounded online center at every applicable scale. -/

namespace EditApproximation

open Finset



theorem queryEarlierRepresentatives_length {n : ℕ} (N P F exponent : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (hP : ∃ e : ℕ, P = 2 ^ e)
    (hF : 1 ≤ F) (hw : 0 ≤ initial q) :
    (queryEarlierRepresentatives N P F exponent a initial q).length ≤
      (dyadicQueryWindow N (initial q) a F).length *
        ((64 * F * P + 2) ^ 2 +
          ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 * (P + 1) ^ 2 + 1) := by
  have hPpos : 0 < P := by obtain ⟨e, rfl⟩ := hP; positivity
  have hlocal := localRefinementRepresentatives_length N P F a initial q hPpos hF
  have hcells := localGroupQueryKeys_length N F exponent a initial q hF hw
  have hmembers : ((localGroupQueryKeys N F exponent a initial q).flatMap fun key =>
      (cellRepresentativeStates n P F key.1 a initial ((2 : ℚ) ^ (-(exponent : ℤ))) key.2).map
        fun r => (key.1, r)).length ≤
      (localGroupQueryKeys N F exponent a initial q).length * (P + 1) ^ 2 := by
    apply list_flatMap_length_le
    intro key hkey
    have hscale := localGroupQueryKeys_scale hkey
    obtain ⟨e, _, heq⟩ := List.mem_map.mp hscale
    simpa only [List.length_map] using cellRepresentativeStates_length_le a initial
      ((2 : ℚ) ^ (-(exponent : ℤ))) key.2
      ⟨by positivity, zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega)⟩
      ⟨e, heq.symm⟩ hP
  unfold queryEarlierRepresentatives
  simp only [List.length_append, List.length_map]
  nlinarith only [hlocal, hmembers, Nat.mul_le_mul_right ((P + 1) ^ 2) hcells]



theorem queryEarlierInputCover_card {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F exponent history : ℕ) (a : ℚ)
    (initial : TargetInterval ny → ℚ) (q : TargetInterval ny) (hP : ∃ e : ℕ, P = 2 ^ e)
    (hF : 1 ≤ F) (hw : 0 ≤ initial q) :
    (queryEarlierInputCover (M := M) parent N P F exponent history a initial q).card ≤
      (dyadicQueryWindow N (initial q) a F).length *
        ((64 * F * P + 2) ^ 2 +
          ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 * (P + 1) ^ 2 + 1) *
        M * history * (40 * P + 2) ^ 2 := by
  have hPpos : 0 < P := by obtain ⟨e, rfl⟩ := hP; positivity
  apply (wideEarlierInputCover_card parent P history _ hPpos).trans
  exact Nat.mul_le_mul_right ((40 * P + 2) ^ 2) (Nat.mul_le_mul_right history
    (Nat.mul_le_mul_right M (queryEarlierRepresentatives_length N P F exponent a initial q hP hF hw)))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedGroupNumerical
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Computed parameters discharge the group scale-count and H^-4 tail bounds. -/

namespace EditApproximation

theorem computed_group_scale_count (N eb : ℕ) (hN : 0 < N) (hell : 8 ≤ inputSmallLog N) :
    (groupDyadicScales (integerParameters N).M (2 ^ eb) (inputSmallLog N)).length ≤
      2 * inputSmallLog N := by
  have hlogs := (inputSmallLog_bounds N hN).1
  have hsmall : smallLogExponent N ≤ inputSmallLog N :=
    (smallLogExponent N).lt_two_pow_self.le
  have hdiv := Nat.div_le_div_right (c := 20) hlogs
  change (groupDyadicScales (2 ^ (heightExponent N / 20)) (2 ^ eb)
    ((2 ^ smallLogExponent N : ℕ) : ℚ)).length ≤ _
  rw [Nat.cast_pow, Nat.cast_ofNat, groupDyadicScales_length_dyadic]
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCurrentQueryBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryScaleDispatchWithWork_value _root_.OAI.EditApproximation.queryScalePresentWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial same-index call budget after substituting the
computed window, cell, scale-label, sampling and rounding parameters. -/

namespace EditApproximation

theorem localCurrentBudget_poly (ell M window cells labels : ℕ) (hell : 4 ≤ ell)
    (hwindow : window ≤ 2 * ell ^ 2) (hcells : cells ≤ 1296 * ell ^ 82)
    (hlabels : labels ≤ 2 * ell) :
    localCurrentBudget window cells labels M (ell ^ 80) (ell ^ 40) ≤ M * ell ^ 256 := by
  have hfirst := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul hwindow hcells) hlabels)
    (le_rfl (a := 624 * M * ell ^ 80 * (ell ^ 40) ^ 2))
  have hsecond := Nat.mul_le_mul_right M (Nat.mul_le_mul hwindow hcells)
  have hthird := Nat.mul_le_mul_right M hwindow
  have h84 : ell ^ 84 ≤ ell ^ 245 := pow_le_pow_right₀ (by omega : 1 ≤ ell) (by decide : 84 ≤ 245)
  have h2 : ell ^ 2 ≤ ell ^ 245 := pow_le_pow_right₀ (by omega : 1 ≤ ell) (by decide : 2 ≤ 245)
  have hsecond' : 2 * ell ^ 2 * (1296 * ell ^ 82) * M ≤ 2592 * M * ell ^ 245 := by
    calc
      _ = 2592 * M * ell ^ 84 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h84
  have hthird' : 2 * ell ^ 2 * M ≤ 2 * M * ell ^ 245 := by
    calc
      _ = 2 * M * ell ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h2
  have hsum : localCurrentBudget window cells labels M (ell ^ 80) (ell ^ 40) ≤
      3237410 * M * ell ^ 245 := by
    apply (Nat.add_le_add (Nat.add_le_add hfirst (hsecond.trans hsecond'))
      (hthird.trans hthird')).trans_eq
    ring
  have hconstant : 3237410 ≤ ell ^ 11 := by
    apply (show 3237410 ≤ (4 : ℕ) ^ 11 by norm_num).trans
    exact Nat.pow_le_pow_left hell 11
  calc
    _ ≤ 3237410 * M * ell ^ 245 := hsum
    _ ≤ ell ^ 11 * M * ell ^ 245 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right M hconstant)
    _ = M * ell ^ 256 := by ring

theorem computed_window_exponent_bound (N : ℕ) (hN : 0 < N) (hell : 8 ≤ inputSmallLog N) :
    computedSeedInitialExponent N + 8 ≤ 2 * inputSmallLog N ^ 2 := by
  have hh := (inputSmallLog_bounds N hN).1
  have hp : coarseExponent (inputSmallLog N) ≤ inputSmallLog N :=
    (Nat.sqrt_le_self _).trans ((Nat.sqrt_le_self _).trans (Nat.log_le_self _ _))
  have hmul := Nat.mul_le_mul (Nat.add_le_add_right hp 4) hh
  unfold computedSeedInitialExponent
  have hslack : 4 * inputSmallLog N + 8 ≤ inputSmallLog N ^ 2 := by nlinarith
  nlinarith only [hmul, hslack]

theorem computed_local_cell_budget (N : ℕ) (hell : 1 ≤ inputSmallLog N) :
    ((32 * inputSmallLog N + 2) * 2 ^ (40 * smallLogExponent N) + 2) ^ 2 ≤
      1296 * inputSmallLog N ^ 82 := by
  have hpower : 2 ^ (40 * smallLogExponent N) = inputSmallLog N ^ 40 := by
    unfold inputSmallLog
    rw [← pow_mul, Nat.mul_comm]
  rw [hpower]
  have hinner : (32 * inputSmallLog N + 2) * inputSmallLog N ^ 40 + 2 ≤
      36 * inputSmallLog N ^ 41 := by
    have ha := Nat.mul_le_mul_right (inputSmallLog N ^ 40) (show 32 * inputSmallLog N + 2 ≤
      34 * inputSmallLog N by omega)
    have hb : 2 ≤ 2 * inputSmallLog N ^ 41 := Nat.mul_le_mul_left 2 (one_le_pow₀ hell)
    calc
      _ ≤ 34 * inputSmallLog N * inputSmallLog N ^ 40 + 2 := Nat.add_le_add_right ha _
      _ ≤ 34 * inputSmallLog N * inputSmallLog N ^ 40 + 2 * inputSmallLog N ^ 41 :=
        Nat.add_le_add_left hb _
      _ = _ := by ring
  calc
    _ ≤ (36 * inputSmallLog N ^ 41) ^ 2 := Nat.pow_le_pow_left hinner 2
    _ = _ := by ring

theorem computed_refinement_window (N : ℕ) (hN : 0 < N) (hell : 8 ≤ inputSmallLog N)
    (A w : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ)) :
    (dyadicQueryWindow N w (refinementFactor A (inputSmallLog N)) (inputSmallLog N)).length ≤
      computedSeedInitialExponent N + 8 := by
  have hh := inputSmallLog_bounds N hN
  have hf : smallLogExponent N ≤ inputSmallLog N := (smallLogExponent N).lt_two_pow_self.le
  have he0 : smallLogExponent N ≤ computedSeedInitialExponent N := by
    have hfour := Nat.mul_le_mul_right (heightExponent N)
      (show 4 ≤ coarseExponent (inputSmallLog N) + 4 by omega)
    unfold computedSeedInitialExponent
    nlinarith only [hh.2, hf, hfour]
  apply refinement_query_window_length N (inputSmallLog N) (computedSeedInitialExponent N) A w (by omega)
  · simpa only [inputSmallLog, Nat.cast_pow, Nat.cast_ofNat] using
      pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) he0
  · exact hA.trans_eq (computedSeed_initial_factor N).symm

/-- The actual finite local shared/selected/online input cover is bounded
by M*ell^256 on every seed. The online-loop length premise is the literal
one-action-per-applicable-scale property proved for the physical program. -/
theorem computed_currentQueryInputCover_card {α : Type*} (source target : List α)
    (N P : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (parent : TargetInterval source.length) (A tau : ℚ)
    (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin (integerParameters N).M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws (integerParameters N).M (inputSmallLog N) (inputSmallLog N ^ 80))
    (q : TargetInterval target.length) (hw : 0 ≤ parentInitial q)
    (online : List (PhysicalRationalAction (integerParameters N).M target.length))
    (honline : online.length ≤
      (dyadicQueryWindow N (parentInitial q) (refinementFactor A (inputSmallLog N)) (inputSmallLog N)).length) :
    (currentQueryInputCover source target parent N P (inputSmallLog N) (40 * smallLogExponent N)
      (inputSmallLog N ^ 80) tau (refinementFactor A (inputSmallLog N)) parentInitial
      child initial current draw q online).card ≤ (integerParameters N).M * inputSmallLog N ^ 256 := by
  let ell := inputSmallLog N
  let M := (integerParameters N).M
  let W := computedSeedInitialExponent N + 8
  let C := ((32 * ell + 2) * 2 ^ (40 * smallLogExponent N) + 2) ^ 2
  have hell8 : 8 ≤ ell := by omega
  have hM : 0 < M := by have h := (computed_branching_bounds N hN hell).1; omega
  have hlabels (b : ℕ) (hb : b ∈ dyadicScales N) : (groupDyadicScales M b ell).length ≤ 2 * ell := by
    obtain ⟨eb, _, rfl⟩ := List.mem_map.mp hb
    exact computed_group_scale_count N eb hN hell8
  have hwindow := computed_refinement_window N hN hell8 A (parentInitial q) hA
  have hkeys : (localGroupQueryKeys N ell (40 * smallLogExponent N)
      (refinementFactor A ell) parentInitial q).length ≤ W * C :=
    (localGroupQueryKeys_length N ell (40 * smallLogExponent N) (refinementFactor A ell)
      parentInitial q (by omega) hw).trans (Nat.mul_le_mul_right C hwindow)
  have hgroups := localCellGroupActions_length_refinement source target parent N P ell
    (40 * smallLogExponent N) (ell ^ 80) (computedSeedInitialExponent N) tau A
    parentInitial child initial current draw q (by omega) hw
  have hraw := currentQueryInputCover_card source target parent N P ell (40 * smallLogExponent N)
    (ell ^ 80) (2 * ell) tau (refinementFactor A ell) parentInitial child initial current draw q online
    hM (by omega) (one_le_pow₀ (by omega)) hlabels
  have hrawN : (currentQueryInputCover source target parent N P ell (40 * smallLogExponent N)
      (ell ^ 80) tau (refinementFactor A ell) parentInitial child initial current draw q online).card ≤
      (localGroupQueryKeys N ell (40 * smallLogExponent N) (refinementFactor A ell) parentInitial q).length *
        (2 * ell) * (624 * M * ell ^ 80 * (2 ^ (40 * smallLogExponent N)) ^ 2) +
      (localCellGroupActions source target parent N P ell (40 * smallLogExponent N) (ell ^ 80) tau
        (refinementFactor A ell) parentInitial child initial current draw q).length * M + online.length * M := by
    exact_mod_cast hraw
  have hFpower : (ell : ℚ) ≤ (2 : ℚ) ^ computedSeedInitialExponent N := by
    have hh := inputSmallLog_bounds N hN
    have hf : smallLogExponent N ≤ ell := (smallLogExponent N).lt_two_pow_self.le
    have hfour := Nat.mul_le_mul_right (heightExponent N)
      (show 4 ≤ coarseExponent ell + 4 by omega)
    have he : smallLogExponent N ≤ computedSeedInitialExponent N := by
      unfold computedSeedInitialExponent
      nlinarith only [hh.2, hf, hfour]
    simpa only [ell, inputSmallLog, Nat.cast_pow, Nat.cast_ofNat] using
      pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) he
  have hAbound : A ≤ (2 : ℚ) ^ computedSeedInitialExponent N := hA.trans_eq (computedSeed_initial_factor N).symm
  have hg : (localCellGroupActions source target parent N P ell (40 * smallLogExponent N) (ell ^ 80) tau
      (refinementFactor A ell) parentInitial child initial current draw q).length ≤ W * C :=
    hgroups hFpower hAbound
  have hbudget : (currentQueryInputCover source target parent N P ell (40 * smallLogExponent N)
      (ell ^ 80) tau (refinementFactor A ell) parentInitial child initial current draw q online).card ≤
      localCurrentBudget W C (2 * ell) M (ell ^ 80) (2 ^ (40 * smallLogExponent N)) := by
    exact hrawN.trans (Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right (2 * ell) hkeys))
      (Nat.mul_le_mul_right M hg)) (Nat.mul_le_mul_right M (honline.trans hwindow)))
  have hpower : 2 ^ (40 * smallLogExponent N) = ell ^ 40 := by
    dsimp only [ell]
    unfold inputSmallLog
    rw [← pow_mul, Nat.mul_comm]
  rw [hpower] at hbudget
  exact hbudget.trans (localCurrentBudget_poly ell M W C (2 * ell)
    ((by decide : 4 ≤ (8 : ℕ)).trans hell8)
    (computed_window_exponent_bound N hN hell8)
    (computed_local_cell_budget N ((by decide : 1 ≤ (8 : ℕ)).trans hell8)) le_rfl)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_EarlierInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit wide-history cover fits the polynomial earlier-input
budget used in the dependency-path count. -/

namespace EditApproximation

theorem queryEarlierInputCover_le_budget {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F exponent history window cells : ℕ) (a : ℚ)
    (initial : TargetInterval ny → ℚ) (q : TargetInterval ny)
    (hP : ∃ e : ℕ, P = 2 ^ e) (hF : 1 ≤ F) (hw : 0 ≤ initial q)
    (hwindow : (dyadicQueryWindow N (initial q) a F).length ≤ window)
    (hcells : ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ≤ cells) :
    (queryEarlierInputCover (M := M) parent N P F exponent history a initial q).card ≤
      localEarlierBudget window cells M P F history := by
  have hmembers : (64 * F * P + 2) ^ 2 +
      ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 * (P + 1) ^ 2 + 1 ≤
      (64 * F * P + 2) ^ 2 + cells * (P + 1) ^ 2 + 1 :=
    Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hcells) _) _
  exact (queryEarlierInputCover_card parent N P F exponent history a initial q hP hF hw).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right history
      (Nat.mul_le_mul_right M (Nat.mul_le_mul hwindow hmembers))))

theorem localEarlierBudget_poly (H p window cells M P F history : ℕ)
    (hH : 64 ≤ H) (hPpos : 1 ≤ P) (hP : P ≤ H ^ (p + 20))
    (hwindow : window ≤ H ^ 3) (hcells : cells ≤ H ^ 84)
    (hM : M ≤ H) (hF : F ≤ H) (hhistory : history ≤ H ^ 2) :
    localEarlierBudget window cells M P F history ≤ H ^ (256 * (p + 1)) := by
  have hHone : 1 ≤ H := by omega
  have h64 : 64 * F ≤ H ^ 2 := by
    calc
      _ ≤ H * H := Nat.mul_le_mul hH hF
      _ = H ^ 2 := by ring
  have hfirstBase : 64 * F * P + 2 ≤ H ^ 3 * P := by
    have hm := Nat.mul_le_mul_right P h64
    have hp : 2 ≤ H ^ 2 * P := by
      have hlarge : 2 ≤ H ^ 2 := (by norm_num : 2 ≤ (64 : ℕ) ^ 2).trans
        (Nat.pow_le_pow_left hH 2)
      exact hlarge.trans (Nat.le_mul_of_pos_right _ hPpos)
    have hh : 2 * H ^ 2 ≤ H ^ 3 := by
      calc
        _ ≤ H * H ^ 2 := Nat.mul_le_mul_right _ (by omega : 2 ≤ H)
        _ = H ^ 3 := by ring
    nlinarith only [hm, hp, Nat.mul_le_mul_right P hh]
  have hfirst : (64 * F * P + 2) ^ 2 ≤ H ^ 86 * P ^ 2 := by
    calc
      _ ≤ (H ^ 3 * P) ^ 2 := Nat.pow_le_pow_left hfirstBase 2
      _ = H ^ 6 * P ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (pow_le_pow_right₀ hHone (by omega : 6 ≤ 86))
  have hPadd : P + 1 ≤ H * P := by nlinarith
  have hsecond : cells * (P + 1) ^ 2 ≤ H ^ 86 * P ^ 2 := by
    calc
      _ ≤ H ^ 84 * (H * P) ^ 2 := Nat.mul_le_mul hcells (Nat.pow_le_pow_left hPadd 2)
      _ = _ := by ring
  have hone : 1 ≤ H ^ 86 * P ^ 2 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul (one_le_pow₀ hHone (n := 86)) (one_le_pow₀ hPpos (n := 2))
  have hsum : (64 * F * P + 2) ^ 2 + cells * (P + 1) ^ 2 + 1 ≤ H ^ 88 * P ^ 2 := by
    have hh : 3 * H ^ 86 ≤ H ^ 88 := by
      calc
        _ ≤ H ^ 2 * H ^ 86 := Nat.mul_le_mul_right _
          ((by norm_num : 3 ≤ (64 : ℕ) ^ 2).trans (Nat.pow_le_pow_left hH 2))
        _ = _ := by ring
    nlinarith only [hfirst, hsecond, hone, Nat.mul_le_mul_right (P ^ 2) hh]
  have hwideBase : 40 * P + 2 ≤ H ^ 2 * P := by
    have hh : 42 ≤ H ^ 2 := (by norm_num : 42 ≤ (64 : ℕ) ^ 2).trans
      (Nat.pow_le_pow_left hH 2)
    nlinarith only [Nat.mul_le_mul_right P hh, hPpos]
  have hwide : (40 * P + 2) ^ 2 ≤ H ^ 4 * P ^ 2 := by
    calc
      _ ≤ (H ^ 2 * P) ^ 2 := Nat.pow_le_pow_left hwideBase 2
      _ = _ := by ring
  calc
    localEarlierBudget window cells M P F history ≤
        H ^ 3 * (H ^ 88 * P ^ 2) * H * H ^ 2 * (H ^ 4 * P ^ 2) := by
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
        (Nat.mul_le_mul hwindow hsum) hM) hhistory) hwide
    _ = H ^ 98 * P ^ 4 := by ring
    _ ≤ H ^ 98 * (H ^ (p + 20)) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP 4)
    _ = H ^ (98 + (p + 20) * 4) := by rw [← pow_mul, ← pow_add]
    _ ≤ H ^ (256 * (p + 1)) := pow_le_pow_right₀ hHone (by omega)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GatheredLocalStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The current-index part of a local step can be evaluated in two
stages: gather the shared sampled inputs, select the whole-cell actions,
then gather their actual costs and the online action costs. -/

namespace EditApproximation

open Finset

theorem orderedInputs_length {ι : Type*} [DecidableEq ι] (encode : ι → ℕ)
    (hinjective : Function.Injective encode) (inputs : Finset ι) :
    (orderedInputs encode hinjective inputs).length = inputs.card := by
  let _ : LinearOrder ι := LinearOrder.lift' encode hinjective
  exact Finset.length_sort (r := (· ≤ ·))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_InitialInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local initial cone uses a bounded number of preceding-seed
queries on every clamped seed, independently of an accuracy event. -/

namespace EditApproximation

theorem localTargetStates_length_from_scale {n : ℕ} (P b radius C : ℕ)
    (q : TargetInterval n) (hP : 0 < P) (hradius : radius ≤ C * b) :
    (localTargetStates n (seedGridSpacing b P) radius q).length ≤ (4 * C * P + 2) ^ 2 := by
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hcover : b ≤ 2 * P * seedGridSpacing b P := by
    have hquot : b / P ≤ seedGridSpacing b P := le_max_right _ _
    have hdiv := Nat.lt_mul_div_succ b hP
    nlinarith only [hquot, hdiv, hg]
  have hprod : 2 * radius ≤ 4 * C * P * seedGridSpacing b P := by
    nlinarith only [hradius, Nat.mul_le_mul_left (2 * C) hcover]
  have hcount : 2 * radius / seedGridSpacing b P ≤ 4 * C * P := by
    have hdivision := Nat.div_mul_le_self (2 * radius) (seedGridSpacing b P)
    nlinarith only [hdivision, hprod, hg]
  exact (localTargetStates_length_le hg q).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right hcount 2) 2)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalOnlineProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Direct online queries use one rounded center per allowed scale. The
integer argument denotes the accepted output of the exact rejection sampler;
reduction modulo the requested range merely makes the finite rule total. -/

namespace EditApproximation

open Finset





theorem localOnlineCandidates_length {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (tau a eta kappa : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (q : TargetInterval target.length) :
    (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial children t integer q).length ≤
      (dyadicQueryWindow N (parentInitial q) a F).length :=
  List.length_filterMap_le _ _

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteQueryWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact read costs for the finite query combinators used in warmup
and refinement. In particular, a collected value is computed once and
is reused by the continuation's local arithmetic. -/

namespace EditApproximation.FiniteQuery

theorem cost_bind {ι : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (program : FiniteQuery ι) (next : ℚ → FiniteQuery ι) :
    (bind program next).cost oracle weight = program.cost oracle weight +
      (next (program.value oracle)).cost oracle weight := by
  induction program with
  | done result => simp only [bind, cost, value, Nat.zero_add]
  | read key continuation ih =>
    simp only [bind, cost, value, ih, Nat.add_assoc]

theorem cost_collect {ι κ : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (reader : κ → FiniteQuery ι) (keys : List κ) (next : List ℚ → FiniteQuery ι) :
    (collect reader keys next).cost oracle weight =
      (keys.map fun key => (reader key).cost oracle weight).sum +
      (next (keys.map fun key => (reader key).value oracle)).cost oracle weight := by
  induction keys generalizing next with
  | nil => simp only [collect, List.map_nil, List.sum_nil, Nat.zero_add]
  | cons key keys ih =>
    simp only [collect, cost_bind, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedBandSpacing
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The input-computed dyadic parameters discharge all spacing and basic rounding premises. -/

namespace EditApproximation

theorem computed_P_dyadic (N : ℕ) :
    (integerParameters N).P =
      2 ^ (heightExponent N * (coarseExponent (inputSmallLog N) + 20)) := by
  change (2 ^ heightExponent N) ^ (coarseExponent (inputSmallLog N) + 20) = _
  rw [pow_mul]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalOnlineSourceQuery
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Online ranges are computed from already gathered band data. The
following query reads only the scale/center pairs for the current entry,
then evaluates the existing local step with the returned integers. -/

namespace EditApproximation



section Query

variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (draw : CellGroupDraws M F Q) (q : TargetInterval target.length)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)



theorem localOnlineSourceStepQuery_cost (oracle : ι → ℚ) (weight : ι → ℕ) :
    (localOnlineSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw q readInteger readEarlier readCurrent).cost oracle weight =
    let keys := localOnlineSourceKeys N P F a parentInitial q
    let reader := fun key => readInteger key
      (keyedOnlineSourceRange source target parent P exponent H tau child key)
    (keys.map fun key => (reader key).cost oracle weight).sum +
      (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
        parentInitial child initial draw
        (fun b r => ⌊finiteAnswerTable keys (keys.map fun key => (reader key).value oracle) (b, r)⌋₊)
        q readEarlier readCurrent).cost oracle weight := by
  unfold localOnlineSourceStepQuery
  rw [FiniteQuery.cost_collect]

end Query

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalRefinementQueryWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal three-stage query plan has the earlier-cover cost plus
at most twice the current-cover cost. This counts its executed readers,
including overlap between its two current gathers. -/

namespace EditApproximation

section Step

variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (weight : ι → ℕ)
  (earlier : PhysicalChildTables M target.length)
  (current : Fin M → TargetInterval target.length → ℚ)
  (ht : 0 < t)
  (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
  (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2)

include ht hreadEarlier hreadCurrent

theorem localRefinementStepQuery_cost :
    (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw integer q readEarlier readCurrent).cost oracle weight =
    ((orderedInputs historyInputCode (historyInputCode_injective M target.length)
      (queryEarlierInputCover parent N P F exponent t a parentInitial q)).map
        (fun input => (readEarlier input).cost oracle weight)).sum +
    ((orderedInputs childInputCode (childInputCode_injective M target.length)
      (querySharedInputCover source target parent N F exponent Q a parentInitial q draw)).map
        (fun input => (readCurrent input).cost oracle weight)).sum +
    ((orderedInputs childInputCode (childInputCode_injective M target.length)
      (actionCurrentInputCover
        (localCellGroupActions source target parent N P F exponent Q tau a
          parentInitial child initial current draw q) ∪
        actionCurrentInputCover
          (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
            parentInitial child initial earlier (t - 1) integer q))).map
        (fun input => (readCurrent input).cost oracle weight)).sum := by
  let earlierCover := queryEarlierInputCover (M := M) parent N P F exponent t a parentInitial q
  let earlierKeys := orderedInputs historyInputCode (historyInputCode_injective M target.length) earlierCover
  let cachedEarlier := fun i s r => finiteAnswerTable earlierKeys
    (earlierKeys.map fun input => earlier input.1 input.2.1 input.2.2) (i, s, r)
  have hearlier : ∀ i s r, (i, s, r) ∈ earlierCover → cachedEarlier i s r = earlier i s r := by
    intro i s r hr
    exact finiteAnswerTable_map earlierKeys _ _
      ((mem_orderedInputs historyInputCode (historyInputCode_injective M target.length) earlierCover _).2 hr)
  have honline := localOnlineCandidates_congr_earlier_cover source target parent N P F exponent H t
    tau a eta kappa parentInitial child initial cachedEarlier earlier (t - 1) integer q (by omega) hearlier
  let shared := querySharedInputCover source target parent N F exponent Q a parentInitial q draw
  let sharedKeys := orderedInputs childInputCode (childInputCode_injective M target.length) shared
  let sharedCurrent := fun i r => finiteAnswerTable sharedKeys
    (sharedKeys.map fun input => current input.1 input.2) (i, r)
  have hshared : ∀ input ∈ shared, sharedCurrent input.1 input.2 = current input.1 input.2 := by
    intro input hi
    exact finiteAnswerTable_map sharedKeys _ input
      ((mem_orderedInputs childInputCode (childInputCode_injective M target.length) shared input).2 hi)
  have hselected := localCellGroupActions_congr_cover source target parent N P F exponent Q tau a
    parentInitial child initial sharedCurrent current draw q hshared
  unfold localRefinementStepQuery
  rw [FiniteQuery.cost_collect]
  simp only [hreadEarlier]
  change _ + (FiniteQuery.collect readCurrent sharedKeys _).cost oracle weight = _
  rw [FiniteQuery.cost_collect]
  simp only [hreadCurrent]
  change _ + (_ + (FiniteQuery.collect readCurrent
    (orderedInputs childInputCode (childInputCode_injective M target.length)
      (actionCurrentInputCover (localCellGroupActions source target parent N P F exponent Q tau a
        parentInitial child initial sharedCurrent draw q) ∪
        actionCurrentInputCover (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
          parentInitial child initial cachedEarlier (t - 1) integer q))) _).cost oracle weight) = _
  rw [hselected, honline, FiniteQuery.cost_collect]
  simp only [FiniteQuery.cost, Nat.add_zero, Nat.add_assoc]
  rfl

theorem localRefinementStepQuery_cost_le (earlierCost currentCost : ℕ)
    (hcostEarlier : ∀ input, (readEarlier input).cost oracle weight ≤ earlierCost)
    (hcostCurrent : ∀ input, (readCurrent input).cost oracle weight ≤ currentCost) :
    (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw integer q readEarlier readCurrent).cost oracle weight ≤
    (queryEarlierInputCover (M := M) parent N P F exponent t a parentInitial q).card * earlierCost +
      2 * (currentQueryInputCover source target parent N P F exponent Q tau a parentInitial
        child initial current draw q
        (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
          parentInitial child initial earlier (t - 1) integer q)).card * currentCost := by
  rw [localRefinementStepQuery_cost source target parent N P F exponent H Q tau a eta kappa delta t
    parentInitial child initial draw integer q readEarlier readCurrent oracle weight earlier current
    ht hreadEarlier hreadCurrent]
  let online := localOnlineCandidates source target parent N P F exponent H tau a eta kappa
    parentInitial child initial earlier (t - 1) integer q
  let groups := localCellGroupActions source target parent N P F exponent Q tau a
    parentInitial child initial current draw q
  let shared := querySharedInputCover source target parent N F exponent Q a parentInitial q draw
  let needed := actionCurrentInputCover groups ∪ actionCurrentInputCover online
  let cover := currentQueryInputCover source target parent N P F exponent Q tau a parentInitial
    child initial current draw q online
  have hshared : shared.card ≤ cover.card := Finset.card_le_card (by
    intro input hi
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hi))
  have hneeded : needed.card ≤ cover.card := Finset.card_le_card (by
    intro input hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
    · exact Finset.mem_union_right _ hi)
  have bound {β : Type} [DecidableEq β] (code : β → ℕ) (hinj : Function.Injective code)
      (inputs : Finset β) (cost : β → ℕ) (B : ℕ) (hcost : ∀ x, cost x ≤ B) :
      ((orderedInputs code hinj inputs).map cost).sum ≤ inputs.card * B := by
    calc
      _ ≤ ((orderedInputs code hinj inputs).map (fun _ => B)).sum :=
        List.sum_le_sum (fun x _ => hcost x)
      _ = inputs.card * B := by simp only [List.map_const', List.sum_replicate,
        smul_eq_mul, orderedInputs_length]
  have he := bound (β := Fin M × ℕ × TargetInterval target.length)
    historyInputCode (historyInputCode_injective M target.length)
    (queryEarlierInputCover (M := M) parent N P F exponent t a parentInitial q)
    (fun input => (readEarlier input).cost oracle weight) earlierCost hcostEarlier
  have hs := bound childInputCode (childInputCode_injective M target.length) shared
    (fun input => (readCurrent input).cost oracle weight) currentCost hcostCurrent
  have hn := bound childInputCode (childInputCode_injective M target.length) needed
    (fun input => (readCurrent input).cost oracle weight) currentCost hcostCurrent
  have hs' := Nat.mul_le_mul_right currentCost hshared
  have hn' := Nat.mul_le_mul_right currentCost hneeded
  change _ ≤ _ + 2 * cover.card * currentCost
  nlinarith only [he, hs, hn, hs', hn']

end Step

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RefinementDataQueryWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Read counts for the full adaptive data query. Weighting reads permits
the same theorem to count current-index and earlier-index dependencies
separately. The bounds count executed readers, including repeated reads
across successive gathering stages. -/

namespace EditApproximation

theorem list_map_sum_le_constant {ι : Type*} (inputs : List ι) (cost : ι → ℕ) (bound : ℕ)
    (hcost : ∀ input, cost input ≤ bound) :
    (inputs.map cost).sum ≤ inputs.length * bound := by
  calc
    _ ≤ (inputs.map fun _ => bound).sum := List.sum_le_sum (fun input _ => hcost input)
    _ = _ := by simp

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalRandomTableCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Random source reads have zero table charge. Uniform bounds for the
remaining local step therefore lift through the actual source collectors,
including the adaptive data queries. -/

namespace EditApproximation

section Step

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (weight : ι → ℕ) (stepBudget : ℕ)
  (hgroup : ∀ key, (readGroup key).cost oracle weight = 0)
  (honline : ∀ key range, (readInteger key range).cost oracle weight = 0)
  (hstep : ∀ draw integer,
    (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw integer q readEarlier readCurrent).cost oracle weight ≤ stepBudget)

include hgroup honline hstep in
 theorem localRandomSourceStepQuery_table_cost_le :
    (localRandomSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial q readGroup readInteger readEarlier readCurrent).cost oracle weight ≤ stepBudget := by
  unfold localRandomSourceStepQuery
  rw [FiniteQuery.cost_collect]
  simp only [hgroup, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_zero, Nat.zero_add]
  rw [localOnlineSourceStepQuery_cost]
  dsimp only
  simp only [honline, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_zero, Nat.zero_add]
  exact hstep _ _

end Step

section Band

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (weight : ι → ℕ)
  (massBudget initialBudget stepBudget : ℕ)
  (hmass : ∀ key, (readMass key).cost oracle weight ≤ massBudget)
  (hinitial : ∀ key, (readInitial key).cost oracle weight ≤ initialBudget)
  (hgroup : ∀ key, (readGroup key).cost oracle weight = 0)
  (honline : ∀ key range, (readInteger key range).cost oracle weight = 0)
  (hstep : ∀ child initial draw integer,
    (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw integer q readEarlier readCurrent).cost oracle weight ≤ stepBudget)

include hmass hinitial hgroup honline hstep in
 theorem localRandomBandDataQuery_table_cost_le :
    (localRandomBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent).cost oracle weight ≤
    (refinementBandInputList (M := M) parent N P F exponent a parentInitial q).length *
      (massBudget + initialBudget) + stepBudget := by
  let keys := refinementBandInputList (M := M) parent N P F exponent a parentInitial q
  let mass := fun i r => finiteAnswerTable keys (keys.map fun input => (readMass input).value oracle) (i, r)
  let initial' := fun i r => finiteAnswerTable keys (keys.map fun input => (readInitial input).value oracle) (i, r)
  have hm := list_map_sum_le_constant keys (fun input => (readMass input).cost oracle weight) massBudget hmass
  have hi := list_map_sum_le_constant keys (fun input => (readInitial input).cost oracle weight) initialBudget hinitial
  have hs := localRandomSourceStepQuery_table_cost_le source target parent N P F exponent H Q
    tau a eta kappa delta t parentInitial mass initial' readGroup readInteger q readEarlier readCurrent
    oracle weight stepBudget hgroup honline (hstep mass initial')
  unfold localRandomBandDataQuery
  rw [FiniteQuery.cost_collect, FiniteQuery.cost_collect]
  change _ + (_ + (localRandomSourceStepQuery source target parent N P F exponent H Q
    tau a eta kappa delta t parentInitial mass initial' q readGroup readInteger readEarlier readCurrent).cost
      oracle weight) ≤ keys.length * (massBudget + initialBudget) + stepBudget
  nlinarith only [hm, hi, hs]

end Band

section Data

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (readParent : TargetInterval target.length → FiniteQuery ι)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (weight : ι → ℕ)
  (parentBudget massBudget initialBudget bandBudget stepBudget : ℕ)
  (hparent : ∀ r, (readParent r).cost oracle weight ≤ parentBudget)
  (hmass : ∀ key, (readMass key).cost oracle weight ≤ massBudget)
  (hinitial : ∀ key, (readInitial key).cost oracle weight ≤ initialBudget)
  (hgroup : ∀ key, (readGroup key).cost oracle weight = 0)
  (honline : ∀ key range, (readInteger key range).cost oracle weight = 0)
  (hband : ∀ parentInitial : TargetInterval target.length → ℚ,
    parentInitial q = (readParent q).value oracle →
    (refinementBandInputList (M := M) parent N P F exponent a parentInitial q).length *
      (massBudget + initialBudget) ≤ bandBudget)
  (hstep : ∀ parentInitial : TargetInterval target.length → ℚ,
    parentInitial q = (readParent q).value oracle → ∀ child initial draw integer,
    (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw integer q readEarlier readCurrent).cost oracle weight ≤ stepBudget)

include hparent hmass hinitial hgroup honline hband hstep in
 theorem localRandomDataQuery_table_cost_le :
    (localRandomDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      readParent readMass readInitial readGroup readInteger q readEarlier readCurrent).cost oracle weight ≤
      (1 + (refinementInitialSupport N P F exponent a ((readParent q).value oracle) q).length) *
        parentBudget + bandBudget + stepBudget := by
  let keys := refinementInitialSupport N P F exponent a ((readParent q).value oracle) q
  let cached := finiteAnswerTable keys (keys.map fun r => (readParent r).value oracle)
  have hq : cached q = (readParent q).value oracle :=
    finiteAnswerTable_map keys _ q (refinementInitialSupport_query N P F exponent a _ q)
  have hlast := localRandomBandDataQuery_table_cost_le source target parent N P F exponent H Q
    tau a eta kappa delta t cached readMass readInitial readGroup readInteger q readEarlier readCurrent
    oracle weight massBudget initialBudget stepBudget hmass hinitial hgroup honline (hstep cached hq)
  have hlast' := hlast.trans (Nat.add_le_add_right (hband cached hq) stepBudget)
  have hfirst := hparent q
  have hsum := list_map_sum_le_constant keys (fun r => (readParent r).cost oracle weight) parentBudget hparent
  unfold localRandomDataQuery
  rw [FiniteQuery.cost_bind, FiniteQuery.cost_collect]
  change _ + (_ + (localRandomBandDataQuery source target parent N P F exponent H Q
    tau a eta kappa delta t cached readMass readInitial readGroup readInteger q readEarlier readCurrent).cost
      oracle weight) ≤ _
  change _ ≤ (1 + keys.length) * parentBudget + bandBudget + stepBudget
  nlinarith only [hfirst, hsum, hlast']

end Data

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RefinementSupportBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryScaleDispatchWithWork_value _root_.OAI.EditApproximation.queryScalePresentWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cardinality of the actual raw initial-data and band-data lists. The
counts apply before any good-seed event and include rejected candidates. -/

namespace EditApproximation

theorem list_eraseDups_length_le {α : Type*} [BEq α] (items : List α) :
    items.eraseDups.length ≤ items.length := by
  cases items with
  | nil => exact le_rfl
  | cons first rest =>
    rw [List.eraseDups_cons, List.length_cons, List.length_cons]
    exact Nat.succ_le_succ ((list_eraseDups_length_le _).trans (List.length_filter_le _ _))
termination_by items.length
decreasing_by
  have h := List.length_filter_le (fun b => !b == first) rest
  simp only [List.length_cons]
  omega

theorem rawRefinementCenters_length {n : ℕ} (N P F : ℕ) (a value : ℚ)
    (q : TargetInterval n) (hP : 0 < P) (hF : 1 ≤ F) :
    (rawRefinementCenters N P F a value q).length ≤
      (dyadicQueryWindow N value a F).length * (64 * F * P + 2) ^ 2 := by
  apply (list_eraseDups_length_le _).trans
  apply list_flatMap_length_le
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hceil : ⌈value⌉₊ ≤ 16 * F * b := by
    apply Nat.ceil_le.mpr
    have h := (div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hwindow.1
    push_cast
    nlinarith only [h]
  simpa only [show 4 * (16 * F) * P = 64 * F * P by ring] using
    localTargetStates_length_from_scale P b ⌈value⌉₊ (16 * F) q hP hceil

theorem cellTargetStates_length_dyadic {n P b : ℕ} (theta : ℚ) (cell : ℕ × ℕ)
    (htheta : 0 ≤ theta ∧ theta ≤ 1)
    (hb : ∃ e : ℕ, b = 2 ^ e) (hP : ∃ e : ℕ, P = 2 ^ e) :
    (cellTargetStates n (seedGridSpacing b P) (theta * b) cell).length ≤ (P + 1) ^ 2 := by
  have hg : (0 : ℚ) < seedGridSpacing b P := by
    exact_mod_cast (show 0 < seedGridSpacing b P by unfold seedGridSpacing; omega)
  have hcover : (b : ℚ) ≤ P * (seedGridSpacing b P : ℚ) := by
    exact_mod_cast seedGridSpacing_covers_dyadic hb hP
  have hsize : theta * b / seedGridSpacing b P ≤ (P : ℚ) := by
    apply (div_le_iff₀ hg).2
    have hsmall : theta * b ≤ (b : ℚ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right htheta.2 (Nat.cast_nonneg b)
    exact hsmall.trans hcover
  exact (cellTargetStates_length_le cell
    (mul_nonneg htheta.1 (Nat.cast_nonneg b)) hsize).trans
    (Nat.pow_le_pow_left (Nat.le_succ P) 2)

theorem refinementInitialSupport_length {n : ℕ} (N P F exponent : ℕ) (a value : ℚ)
    (q : TargetInterval n) (hP : ∃ e : ℕ, P = 2 ^ e) (hF : 1 ≤ F) (hw : 0 ≤ value) :
    (refinementInitialSupport N P F exponent a value q).length ≤
      1 + (dyadicQueryWindow N value a F).length *
        ((64 * F * P + 2) ^ 2 + ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 * (P + 1) ^ 2 + 1) := by
  have hPpos : 0 < P := by obtain ⟨e, rfl⟩ := hP; positivity
  have hlocal := rawRefinementCenters_length N P F a value q hPpos hF
  have hcells := localGroupQueryKeys_length N F exponent a (fun _ => value) q hF hw
  have hmembers : ((localGroupQueryKeys N F exponent a (fun _ => value) q).flatMap fun key =>
      cellTargetStates n (seedGridSpacing key.1 P) ((2 : ℚ) ^ (-(exponent : ℤ)) * key.1) key.2).length ≤
      (localGroupQueryKeys N F exponent a (fun _ => value) q).length * (P + 1) ^ 2 := by
    apply list_flatMap_length_le
    intro key hk
    have hscale := localGroupQueryKeys_scale hk
    obtain ⟨e, _, heq⟩ := List.mem_map.mp hscale
    exact cellTargetStates_length_dyadic _ key.2
      ⟨by positivity, zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega)⟩
      ⟨e, heq.symm⟩ hP
  unfold refinementInitialSupport
  simp only [List.length_cons, List.length_append, List.length_map]
  nlinarith only [hlocal, hmembers, Nat.mul_le_mul_right ((P + 1) ^ 2) hcells]

theorem wideWarmupInputs_length {nx ny M : ℕ} (parent : TargetInterval nx) (P : ℕ)
    (representatives : List (ℕ × TargetInterval ny)) (hP : 0 < P) :
    (wideWarmupInputs (M := M) parent P representatives).length ≤
      representatives.length * M * (40 * P + 2) ^ 2 := by
  apply (list_eraseDups_length_le _).trans
  have h : (representatives.flatMap fun br => (List.finRange M).flatMap fun i =>
      (wideChildStateList parent br.2 br.1 P i).map fun r => (i, r)).length ≤
      representatives.length * (M * (40 * P + 2) ^ 2) := by
    apply list_flatMap_length_le
    intro br hbr
    have hi : ((List.finRange M).flatMap fun i =>
        (wideChildStateList parent br.2 br.1 P i).map fun r => (i, r)).length ≤
        (List.finRange M).length * (40 * P + 2) ^ 2 := by
      apply list_flatMap_length_le
      intro i hi
      simpa only [List.length_map] using wideEarlierChildStateList_length_le parent br.2 br.1 P hP i
    simpa only [List.length_finRange] using hi
  exact h.trans_eq (by ring)

theorem refinementBandInputList_length {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F exponent : ℕ) (a : ℚ) (initial : TargetInterval ny → ℚ) (q : TargetInterval ny)
    (hP : ∃ e : ℕ, P = 2 ^ e) (hF : 1 ≤ F) (hw : 0 ≤ initial q) :
    (refinementBandInputList (M := M) parent N P F exponent a initial q).length ≤
      (dyadicQueryWindow N (initial q) a F).length *
        ((64 * F * P + 2) ^ 2 + ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 * (P + 1) ^ 2 + 1) *
        M * (40 * P + 2) ^ 2 := by
  have hPpos : 0 < P := by obtain ⟨e, rfl⟩ := hP; positivity
  exact (wideWarmupInputs_length parent P _ hPpos).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right M
      (queryEarlierRepresentatives_length N P F exponent a initial q hP hF hw)))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedEarlierInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual earlier-input cover satisfies the polynomial branching
budget at every seed, after substituting the computed time and grid
parameters. -/

namespace EditApproximation

theorem computed_smallLog_le_height (N : ℕ) : inputSmallLog N ≤ inputHeight N := by
  have hf : smallLogExponent N ≤ heightExponent N := by
    unfold smallLogExponent
    apply Nat.clog_le_of_le_pow
    exact max_le Nat.one_le_two_pow (heightExponent N).lt_two_pow_self.le
  exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hf

theorem computed_history_budget_le_height_sq (N : ℕ) (hH : 4 ≤ inputHeight N) :
    (integerParameters N).T + (integerParameters N).S + 1 ≤ inputHeight N ^ 2 := by
  have hT : (integerParameters N).T ≤ 2 * inputHeight N := by
    change 2 ^ ((3 * heightExponent N + 3) / 4) ≤ 2 * 2 ^ heightExponent N
    calc
      _ ≤ 2 ^ (heightExponent N + 1) :=
        pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (by omega)
      _ = _ := by rw [pow_succ]; ring
  have hS : (integerParameters N).S ≤ inputHeight N := Nat.div_le_self _ _
  nlinarith only [hT, hS, hH]

theorem computed_window_le_height_cube (N : ℕ) (hN : 0 < N)
    (hell : 8 ≤ inputSmallLog N) (hH : 2 ≤ inputHeight N) :
    computedSeedInitialExponent N + 8 ≤ inputHeight N ^ 3 := by
  calc
    _ ≤ 2 * inputSmallLog N ^ 2 := computed_window_exponent_bound N hN hell
    _ ≤ inputHeight N * inputHeight N ^ 2 :=
      Nat.mul_le_mul hH (Nat.pow_le_pow_left (computed_smallLog_le_height N) 2)
    _ = _ := by ring

theorem computed_cell_budget_le_height_pow (N : ℕ) (hH : 64 ≤ inputHeight N) :
    ((32 * inputSmallLog N + 2) * 2 ^ (40 * smallLogExponent N) + 2) ^ 2 ≤
      inputHeight N ^ 84 := by
  have hconstant : 1296 ≤ inputHeight N ^ 2 :=
    (by norm_num : 1296 ≤ (64 : ℕ) ^ 2).trans (Nat.pow_le_pow_left hH 2)
  calc
    _ ≤ 1296 * inputSmallLog N ^ 82 :=
      computed_local_cell_budget N Nat.one_le_two_pow
    _ ≤ inputHeight N ^ 2 * inputHeight N ^ 82 :=
      Nat.mul_le_mul hconstant (Nat.pow_le_pow_left (computed_smallLog_le_height N) 82)
    _ = _ := by ring

/-- Every literal earlier-input request lies in a cover of cardinality
`H^(256(p+1))`. The only value premise is nonnegativity of the actual
initial query value; no good-seed event is required. -/
theorem computed_queryEarlierInputCover_card {nx ny : ℕ}
    (parent : TargetInterval nx) (N P : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hPeq : P = (integerParameters N).P)
    (A : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
    (initial : TargetInterval ny → ℚ) (q : TargetInterval ny) (hw : 0 ≤ initial q) :
    (queryEarlierInputCover (M := (integerParameters N).M) parent N P (inputSmallLog N)
      (40 * smallLogExponent N) ((integerParameters N).T + (integerParameters N).S + 1)
      (refinementFactor A (inputSmallLog N)) initial q).card ≤
      inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1)) := by
  let W := computedSeedInitialExponent N + 8
  let C := ((32 * inputSmallLog N + 2) * 2 ^ (40 * smallLogExponent N) + 2) ^ 2
  have hF : inputSmallLog N ≤ inputHeight N := computed_smallLog_le_height N
  have hH : 64 ≤ inputHeight N := (by omega : 64 ≤ inputSmallLog N).trans hF
  have hPpos : 1 ≤ P := by
    rw [hPeq]
    exact one_le_pow₀ Nat.one_le_two_pow
  have hPpower : P ≤ inputHeight N ^ (coarseExponent (inputSmallLog N) + 20) := by
    rw [hPeq]
    exact le_rfl
  have hM : (integerParameters N).M ≤ inputHeight N :=
    pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (Nat.div_le_self _ _)
  have hbudget := queryEarlierInputCover_le_budget (M := (integerParameters N).M)
    parent N P (inputSmallLog N) (40 * smallLogExponent N)
    ((integerParameters N).T + (integerParameters N).S + 1) W C
    (refinementFactor A (inputSmallLog N)) initial q
    ⟨_, hPeq.trans (computed_P_dyadic N)⟩ (by omega) hw
    (computed_refinement_window N hN (by omega) A (initial q) hA) le_rfl
  exact hbudget.trans (localEarlierBudget_poly (inputHeight N)
    (coarseExponent (inputSmallLog N)) W C (integerParameters N).M P (inputSmallLog N)
    ((integerParameters N).T + (integerParameters N).S + 1)
    hH hPpos hPpower (computed_window_le_height_cube N hN (by omega) (by omega))
    (computed_cell_budget_le_height_pow N hH) hM hF
    (computed_history_budget_le_height_sq N (by omega)))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedEarlierHistory
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A query gathers only its preceding history, rather than allocating
the full time range used to bound that history's cardinality. -/

namespace EditApproximation

theorem wideEarlierInputCover_mono_history {nx ny M : ℕ} (parent : TargetInterval nx)
    (P small large : ℕ) (representatives : List (ℕ × TargetInterval ny)) (h : small ≤ large) :
    wideEarlierInputCover (M := M) parent P small representatives ⊆
      wideEarlierInputCover parent P large representatives := by
  intro input hinput
  obtain ⟨br, hbr, hinput⟩ := Finset.mem_biUnion.mp hinput
  obtain ⟨i, hi, hinput⟩ := Finset.mem_biUnion.mp hinput
  obtain ⟨t, ht, hinput⟩ := Finset.mem_biUnion.mp hinput
  exact Finset.mem_biUnion.mpr ⟨br, hbr, Finset.mem_biUnion.mpr ⟨i, hi,
    Finset.mem_biUnion.mpr ⟨t, (Finset.mem_range.mpr ((Finset.mem_range.mp ht).trans_le h)), hinput⟩⟩⟩

theorem computed_queryEarlierHistory_card {nx ny : ℕ}
    (parent : TargetInterval nx) (N P history : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hPeq : P = (integerParameters N).P)
    (hhistory : history ≤ (integerParameters N).T + (integerParameters N).S + 1)
    (A : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
    (initial : TargetInterval ny → ℚ) (q : TargetInterval ny) (hw : 0 ≤ initial q) :
    (queryEarlierInputCover (M := (integerParameters N).M) parent N P (inputSmallLog N)
      (40 * smallLogExponent N) history (refinementFactor A (inputSmallLog N)) initial q).card ≤
      inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1)) := by
  apply (Finset.card_le_card (wideEarlierInputCover_mono_history parent P history
    ((integerParameters N).T + (integerParameters N).S + 1) _ hhistory)).trans
  exact computed_queryEarlierInputCover_card parent N P hN hell hPeq A hA initial q hw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedRefinementReadBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual refinement query, including the reads used to construct
its initial and mass data, satisfies the two dependency branching budgets.
Only nonnegativity of the actual initial query value is used. -/

namespace EditApproximation

theorem computed_data_support_budget {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P T : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (hM : M = (integerParameters N).M) (hP : P = (integerParameters N).P)
    (hT : T = (integerParameters N).T)
    (A : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
    (initial : TargetInterval ny → ℚ) (q : TargetInterval ny) (hw : 0 ≤ initial q) :
    (refinementInitialSupport N P (inputSmallLog N) (40 * smallLogExponent N)
      (refinementFactor A (inputSmallLog N)) (initial q) q).length ≤
        1 + inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1)) ∧
    (refinementBandInputList (M := M) parent N P (inputSmallLog N) (40 * smallLogExponent N)
      (refinementFactor A (inputSmallLog N)) initial q).length * (T + 1) ≤
        inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1)) := by
  let H := inputHeight N
  let ell := inputSmallLog N
  let W := (dyadicQueryWindow N (initial q) (refinementFactor A ell) ell).length
  let C := ((32 * ell + 2) * 2 ^ (40 * smallLogExponent N) + 2) ^ 2
  let R := (64 * ell * P + 2) ^ 2 + C * (P + 1) ^ 2 + 1
  let history := (integerParameters N).T + (integerParameters N).S + 1
  let budget := localEarlierBudget W C M P ell history
  have hF : ell ≤ H := computed_smallLog_le_height N
  have hH : 64 ≤ H := (by omega : 64 ≤ ell).trans hF
  have hPpos : 1 ≤ P := by rw [hP]; exact one_le_pow₀ Nat.one_le_two_pow
  have hPpower : P ≤ H ^ (coarseExponent ell + 20) := by rw [hP]; exact le_rfl
  have hMpos : 0 < M := by
    rw [hM]
    change 0 < 2 ^ _
    exact Nat.two_pow_pos _
  have hMbound : M ≤ H := by
    rw [hM]
    exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (Nat.div_le_self _ _)
  have hW : W ≤ H ^ 3 :=
    (computed_refinement_window N hN (by omega) A (initial q) hA).trans
      (computed_window_le_height_cube N hN (by omega) (by omega))
  have hbudget : budget ≤ H ^ (256 * (coarseExponent ell + 1)) :=
    localEarlierBudget_poly H (coarseExponent ell) W C M P ell history hH hPpos hPpower hW
      (computed_cell_budget_le_height_pow N hH) hMbound hF
      (computed_history_budget_le_height_sq N (by omega))
  have hhistory : T + 1 ≤ history := by dsimp only [history]; omega
  have hwide : 0 < (40 * P + 2) ^ 2 := by positivity
  have hfactor : 0 < M * history * (40 * P + 2) ^ 2 := by positivity
  have hraw : W * R ≤ budget := by
    have h := Nat.le_mul_of_pos_right (W * R) hfactor
    exact h.trans_eq (by dsimp only [budget, localEarlierBudget, R] <;> ring)
  have hband : W * R * M * (40 * P + 2) ^ 2 * (T + 1) ≤ budget := by
    apply (Nat.mul_le_mul_left (W * R * M * (40 * P + 2) ^ 2) hhistory).trans_eq
    dsimp only [budget, localEarlierBudget, R]
    ring
  have hdyadic : ∃ e : ℕ, P = 2 ^ e := ⟨_, hP.trans (computed_P_dyadic N)⟩
  constructor
  · exact (refinementInitialSupport_length N P ell (40 * smallLogExponent N)
      (refinementFactor A ell) (initial q) q hdyadic (by omega) hw).trans
      (Nat.add_le_add_left (hraw.trans hbudget) 1)
  · exact (Nat.mul_le_mul_right (T + 1)
      (refinementBandInputList_length parent N P ell (40 * smallLogExponent N)
        (refinementFactor A ell) initial q hdyadic (by omega) hw)).trans (hband.trans hbudget)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedRandomTableCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source-aware query satisfies the same table branching budgets.
Its group/online values may be arbitrary: only source-free table costs
and nonnegativity of the actual initial value are needed here. -/

namespace EditApproximation

 theorem computed_localRandomDataQuery_table_cost_oai {ι α : Type*} (source target : List α)
    {M : ℕ} [NeZero M] (parent : TargetInterval source.length) (N P H T t : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hM : M = (integerParameters N).M)
    (hP : P = (integerParameters N).P) (hT : T = (integerParameters N).T)
    (ht : 0 < t) (htime : t ≤ (integerParameters N).S)
    (A tau eta kappa delta : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
    (readParent : TargetInterval target.length → FiniteQuery ι)
    (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
    (readGroup : GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery ι)
    (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
    (q : TargetInterval target.length)
    (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
    (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
    (oracle : ι → ℚ) (weight : ι → ℕ) (dataCost earlierCost currentCost : ℕ)
    (hparent : ∀ r, (readParent r).cost oracle weight ≤ dataCost)
    (hmass : ∀ key, (readMass key).cost oracle weight ≤ T * dataCost)
    (hinitial : ∀ key, (readInitial key).cost oracle weight ≤ dataCost)
    (hgroup : ∀ key, (readGroup key).cost oracle weight = 0)
    (honline : ∀ key range, (readInteger key range).cost oracle weight = 0)
    (hearlier : ∀ key, (readEarlier key).cost oracle weight ≤ earlierCost)
    (hcurrent : ∀ key, (readCurrent key).cost oracle weight ≤ currentCost)
    (hw : 0 ≤ (readParent q).value oracle) :
    let B := inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1))
    (localRandomDataQuery source target parent N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) tau (refinementFactor A (inputSmallLog N)) eta kappa delta t
      readParent readMass readInitial readGroup readInteger q readEarlier readCurrent).cost oracle weight ≤
        (2 + 2 * B) * dataCost + B * earlierCost +
          (2 * M * inputSmallLog N ^ 256) * currentCost := by
  dsimp only
  let B := inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1))
  let actual := fun r => (readParent r).value oracle
  have hdata := computed_data_support_budget parent N P T hN hell hM hP hT A hA actual q hw
  have hband (parentInitial : TargetInterval target.length → ℚ) (hq : parentInitial q = actual q) :
      (refinementBandInputList (M := M) parent N P (inputSmallLog N) (40 * smallLogExponent N)
        (refinementFactor A (inputSmallLog N)) parentInitial q).length *
        (T * dataCost + dataCost) ≤ B * dataCost := by
    have hb := (computed_data_support_budget parent N P T hN hell hM hP hT A hA
      parentInitial q (by rw [hq]; exact hw)).2
    convert Nat.mul_le_mul_right dataCost hb using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hstep (parentInitial : TargetInterval target.length → ℚ) (hq : parentInitial q = actual q)
      (child initial : Fin M → TargetInterval target.length → ℚ)
      (draw : CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
      (integer : ℕ → TargetInterval target.length → ℕ) :
      (localRefinementStepQuery source target parent N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) tau (refinementFactor A (inputSmallLog N)) eta kappa delta t
        parentInitial child initial draw integer q readEarlier readCurrent).cost oracle weight ≤
          B * earlierCost + (2 * M * inputSmallLog N ^ 256) * currentCost := by
    let earlier := fun i s r => (readEarlier (i, s, r)).value oracle
    let current := fun i r => (readCurrent (i, r)).value oracle
    have he := computed_queryEarlierHistory_card parent N P t hN hell hP (by omega) A hA
      parentInitial q (by rw [hq]; exact hw)
    rw [← hM] at he
    have hc : (currentQueryInputCover source target parent N P (inputSmallLog N)
        (40 * smallLogExponent N) (inputSmallLog N ^ 80) tau
        (refinementFactor A (inputSmallLog N)) parentInitial child initial current draw q
        (localOnlineCandidates source target parent N P (inputSmallLog N) (40 * smallLogExponent N)
          H tau (refinementFactor A (inputSmallLog N)) eta kappa parentInitial child initial earlier
          (t - 1) integer q)).card ≤ M * inputSmallLog N ^ 256 := by
      subst M
      exact computed_currentQueryInputCover_card source target N P hN hell parent A tau hA
        parentInitial child initial current draw q (by rw [hq]; exact hw) _
        (localOnlineCandidates_length source target parent N P (inputSmallLog N)
          (40 * smallLogExponent N) H tau (refinementFactor A (inputSmallLog N)) eta kappa
          parentInitial child initial earlier (t - 1) integer q)
    have hs := localRefinementStepQuery_cost_le source target parent N P (inputSmallLog N)
      (40 * smallLogExponent N) H (inputSmallLog N ^ 80) tau
      (refinementFactor A (inputSmallLog N)) eta kappa delta t parentInitial child initial draw integer q
      readEarlier readCurrent oracle weight earlier current ht (fun _ => rfl) (fun _ => rfl)
      earlierCost currentCost hearlier hcurrent
    apply hs.trans
    apply Nat.add_le_add (Nat.mul_le_mul_right earlierCost he)
    convert Nat.mul_le_mul_right currentCost (Nat.mul_le_mul_left 2 hc) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have h := localRandomDataQuery_table_cost_le source target parent N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) tau
    (refinementFactor A (inputSmallLog N)) eta kappa delta t readParent readMass readInitial
    readGroup readInteger q readEarlier readCurrent oracle weight dataCost (T * dataCost) dataCost
    (B * dataCost) (B * earlierCost + (2 * M * inputSmallLog N ^ 256) * currentCost)
    hparent hmass hinitial hgroup honline hband hstep
  have hi := Nat.mul_le_mul_right dataCost (Nat.add_le_add_left hdata.1 1)
  dsimp only [B, actual] at h hi ⊢
  nlinarith only [h, hi]

end EditApproximation

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.EditApproximation.computed_localRandomDataQuery_table_cost_oai.{u_1, u_2} := @OAI.EditApproximation.computed_localRandomDataQuery_table_cost_oai.{u_1, u_2}
