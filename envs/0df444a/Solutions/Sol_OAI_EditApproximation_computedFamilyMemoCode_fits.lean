-- Prove2me | solution 1 for OAI.EditApproximation.computedFamilyMemoCode_fits
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:22:22.277647+00:00
-- url     : https://prove2.me/submissions/9557a427-9740-4779-b49c-b5547e8b489b

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Geometric
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea002
import Theorems.Thm_OAI_EditApproximation_computedSeedPassCount_le_height
import Theorems.Thm_OAI_EditApproximation_computed_physicalFamilyCode_bound

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
















theorem inputHeight_covers_length (N : ℕ) : N + 2 ≤ 2 ^ inputHeight N := by
  have hlog := Nat.le_pow_clog (by decide : 1 < 2) (N + 2)
  have hheight := Nat.le_pow_clog (by decide : 1 < 2) (Nat.clog 2 (N + 2))
  exact hlog.trans (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hheight)

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



theorem intervalTreeDepth_power_le (M nx : ℕ) (hM : 2 ≤ M) :
    M ^ intervalTreeDepth M nx ≤ M * max 1 nx := by
  by_cases hx : max 1 nx = 1
  · have hz : Nat.clog M 1 = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact (Nat.clog_le_iff_le_pow hM).2 (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [intervalTreeDepth, hx, hz, pow_zero, mul_one] using
      (by omega : 1 ≤ M)
  · have hx1 : 1 < max 1 nx := by omega
    have hdepth := Nat.clog_pos hM hx1
    have hpred := Nat.pow_pred_clog_lt_self hM hx1
    unfold intervalTreeDepth
    rw [← Nat.succ_pred_eq_of_pos hdepth,
      pow_succ]
    nlinarith

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

theorem computed_tree_depth_bound (N nx : ℕ) (hN : 0 < N) (hnx : nx ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    intervalTreeDepth (integerParameters N).M nx * inputSmallLog N ≤ 100 * inputHeight N := by
  let k := heightExponent N / 20
  have hbranch := computed_branching_bounds N hN hell
  have hbound : max 1 nx ≤ 2 ^ inputHeight N := by
    apply max_le Nat.one_le_two_pow
    exact hnx.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
  have hlog : Nat.clog 2 (max 1 nx) ≤ inputHeight N :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hbound
  have hdepth : intervalTreeDepth (integerParameters N).M nx =
      (Nat.clog 2 (max 1 nx) + (k - 1)) / k := by
    exact Nat.clog_pow_left 2 k (max 1 nx)
  have hproduct := Nat.div_mul_le_self (Nat.clog 2 (max 1 nx) + (k - 1)) k
  rw [← hdepth] at hproduct
  have hscale := Nat.mul_le_mul_left
    (intervalTreeDepth (integerParameters N).M nx) hbranch.2.1
  change intervalTreeDepth (integerParameters N).M nx * inputSmallLog N ≤
    intervalTreeDepth (integerParameters N).M nx * (50 * k) at hscale
  have hkH : k ≤ inputHeight N := hbranch.2.2
  have hsub : k - 1 ≤ k := Nat.sub_le _ _
  nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalInputEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fixed-width binary keys for gathered child states. The encoding uses
mixed radix arithmetic on the child label and the two state endpoints. -/

namespace EditApproximation

theorem childInputCode_bound {M n : ℕ} (input : Fin M × TargetInterval n) :
    childInputCode input < M * (n + 1) ^ 2 := by
  have hlow := input.2.ordered.trans input.2.valid
  have hhigh := input.2.valid
  have hlabel := input.1.isLt
  have hM : 0 < M := by omega
  have hinner : input.2.lo + (n + 1) * input.2.hi < (n + 1) ^ 2 := by
    nlinarith only [hlow, hhigh]
  unfold childInputCode
  nlinarith only [hlabel, Nat.mul_le_mul_left M (Nat.succ_le_of_lt hinner)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalNodeEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Computable base-M node labels and mixed-radix table-entry keys.
Equal source intervals at different physical nodes keep distinct keys. -/

namespace EditApproximation



theorem treeLayerCode_bound (M d : ℕ) (path : TreeLayer M d) :
    treeLayerCode M d path < M ^ d := by
  induction d with
  | zero => exact Nat.zero_lt_one
  | succ d ih =>
    have hp := ih path.1
    have hi := path.2.isLt
    change path.2.val + M * treeLayerCode M d path.1 < M ^ (d + 1)
    rw [pow_succ]
    nlinarith only [hi, Nat.mul_le_mul_left M (Nat.succ_le_of_lt hp)]



theorem physicalNode_layer_bound {M J : ℕ} (hM : 1 ≤ M) (node : PhysicalNode M J) :
    treeLayerCode M node.1.val node.2 < M ^ J :=
  (treeLayerCode_bound M node.1.val node.2).trans_le
    (pow_le_pow_right₀ hM (Nat.le_of_lt_succ node.1.isLt))

theorem physicalNodeCode_bound {M J : ℕ} (hM : 1 ≤ M) (node : PhysicalNode M J) :
    physicalNodeCode node < M ^ J * (J + 1) := by
  have hpath := physicalNode_layer_bound hM node
  have hdepth := node.1.isLt
  unfold physicalNodeCode
  nlinarith only [hpath, Nat.mul_le_mul_left (M ^ J) (Nat.succ_le_of_lt hdepth)]



theorem physicalEntryCode_bound {M J n : ℕ} (hM : 1 ≤ M) (state : PhysicalEntry M J n) :
    physicalEntryCode state < (n + 1) ^ 2 * (M ^ J * (J + 1)) := by
  have hstate : childInputCode ((0 : Fin 1), state.2) < (n + 1) ^ 2 := by
    simpa only [Nat.one_mul] using childInputCode_bound ((0 : Fin 1), state.2)
  have hnode := physicalNodeCode_bound hM state.1
  unfold physicalEntryCode
  nlinarith only [hstate, Nat.mul_le_mul_left ((n + 1) ^ 2) (Nat.succ_le_of_lt hnode)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRequestEncoding
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fixed-width keys for the bounded physical cache. Their construction
uses only the request's coordinates, without enumerating table entries. -/

namespace EditApproximation
namespace PhysicalTableRequest





theorem code_bound {M J n : ℕ} (hM : 1 ≤ M) (passes copies T S : ℕ)
    (request : PhysicalTableRequest M J n) (hrequest : Bounded passes copies T S request) :
    code copies T S request < capacity M J n passes copies T S := by
  have he := physicalEntryCode_bound hM (request.node, request.state)
  change physicalEntryCode (request.node, request.state) < entryCapacity M J n at he
  have hinner : physicalEntryCode (request.node, request.state) +
      entryCapacity M J n * request.pass < entryCapacity M J n * passes := by
    nlinarith only [he, Nat.mul_le_mul_left (entryCapacity M J n) (Nat.succ_le_of_lt hrequest.1)]
  have hmiddle : request.copy + copies *
      (physicalEntryCode (request.node, request.state) + entryCapacity M J n * request.pass) <
        copies * (entryCapacity M J n * passes) := by
    nlinarith only [hrequest.2.1, Nat.mul_le_mul_left copies (Nat.succ_le_of_lt hinner)]
  unfold code capacity
  nlinarith only [hrequest.2.2, Nat.mul_le_mul_left (T + S + 1) (Nat.succ_le_of_lt hmiddle)]

end PhysicalTableRequest
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedPhysicalRequest
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Coarse seed computations are explicit cache requests, alongside the
bounded warmup/refinement requests. Their rank is below every table request,
so first exposure of a same-node coarse entry is a genuine leaf of the lazy program. -/

namespace EditApproximation



namespace ChargedPhysicalRequest









 theorem code_bound {M J ny passes copies T S : ℕ} (hM : 1 ≤ M)
    (request : ChargedPhysicalRequest M J ny passes copies T S) :
    code request < capacity M J ny passes copies T S := by
  cases request with
  | inl entry =>
    have h := physicalEntryCode_bound hM entry
    change physicalEntryCode entry < PhysicalTableRequest.entryCapacity M J ny at h
    simp only [code, capacity]
    omega
  | inr request =>
    have h := PhysicalTableRequest.code_bound hM passes copies T S request.val request.property
    simp only [code, capacity]
    omega

 theorem code_fits {M J ny passes copies T S : ℕ} (hM : 1 ≤ M)
    (request : ChargedPhysicalRequest M J ny passes copies T S) :
    code request < 2 ^ bits M J ny passes copies T S :=
  (code_bound hM request).trans_le
    ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide : 1 < 2) _))

end ChargedPhysicalRequest

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedEarlierInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRequestBits
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cache key width is linear in the input height, once the actual
pass and copy bounds are substituted. The numerical capacity is only a
bound: no array of that capacity is allocated. -/

namespace EditApproximation

theorem computed_entryCapacity_bound (N nx ny : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N) :
    PhysicalTableRequest.entryCapacity (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny ≤ 2 ^ (5 * inputHeight N) := by
  let H := inputHeight N
  let M := (integerParameters N).M
  let J := intervalTreeDepth M nx
  have hM : M ≤ H := pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (Nat.div_le_self _ _)
  have hMH : M ≤ 2 ^ H := hM.trans (Nat.lt_two_pow_self.le)
  have hnx' : max 1 nx ≤ 2 ^ H := max_le Nat.one_le_two_pow
    (hnx.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N)))
  have htree : M ^ J ≤ 2 ^ (2 * H) := by
    calc
      _ ≤ M * max 1 nx := intervalTreeDepth_power_le M nx (computed_branching_bounds N hN hell).1
      _ ≤ 2 ^ H * 2 ^ H := Nat.mul_le_mul hMH hnx'
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hJ : J ≤ H := by
    have hj := computed_tree_depth_bound N nx hN hnx hell
    change J * inputSmallLog N ≤ 100 * H at hj
    nlinarith only [hj, hell]
  have hJ' : J + 1 ≤ 2 ^ H := (Nat.add_le_add_right hJ 1).trans (Nat.lt_two_pow_self)
  have hny' : ny + 1 ≤ 2 ^ H := (by omega : ny + 1 ≤ N + 2).trans (inputHeight_covers_length N)
  unfold PhysicalTableRequest.entryCapacity
  calc
    (ny + 1) ^ 2 * (M ^ J * (J + 1)) ≤ (2 ^ H) ^ 2 * (2 ^ (2 * H) * 2 ^ H) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hny' 2) (Nat.mul_le_mul htree hJ')
    _ = 2 ^ (5 * H) := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega

theorem computed_request_bits_le (N nx ny passes copies : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N)
    (hpasses : passes ≤ inputHeight N ^ 2) (hcopies : copies ≤ inputHeight N ^ 2) :
    PhysicalTableRequest.bits (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny passes copies
      (integerParameters N).T (integerParameters N).S ≤ 11 * inputHeight N + 1 := by
  let H := inputHeight N
  have hH : 4 ≤ H := (by omega : 4 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hHpow : H ^ 2 ≤ 2 ^ (2 * H) := by
    calc
      _ ≤ (2 ^ H) ^ 2 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hstride := (computed_history_budget_le_height_sq N hH).trans hHpow
  have hentry := computed_entryCapacity_bound N nx ny hN hell hnx hny
  have hcapacity : PhysicalTableRequest.capacity (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny passes copies
      (integerParameters N).T (integerParameters N).S ≤ 2 ^ (11 * H) := by
    unfold PhysicalTableRequest.capacity
    calc
      _ ≤ 2 ^ (2 * H) * (2 ^ (2 * H) * (2 ^ (5 * H) * 2 ^ (2 * H))) :=
        Nat.mul_le_mul hstride
          (Nat.mul_le_mul (hcopies.trans hHpow) (Nat.mul_le_mul hentry (hpasses.trans hHpow)))
      _ = _ := by rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  unfold PhysicalTableRequest.bits
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2
  calc
    _ ≤ 2 ^ (11 * H) + 2 ^ (11 * H) := Nat.add_le_add hcapacity Nat.one_le_two_pow
    _ = _ := by
      change 2 ^ (11 * H) + 2 ^ (11 * H) = 2 ^ (11 * H + 1)
      rw [pow_succ]
      omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRequestSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial retained-cache bound for every execution. The estimate
uses only fixed-width key insertion and computed parameter sizes, and
therefore does not depend on an approximation success event. -/

namespace EditApproximation

theorem computed_charged_request_bits_le (N nx ny passes copies : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N)
    (hpasses : passes ≤ inputHeight N ^ 2) (hcopies : copies ≤ inputHeight N ^ 2) :
    ChargedPhysicalRequest.bits (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny passes copies
      (integerParameters N).T (integerParameters N).S ≤ 11 * inputHeight N + 3 := by
  let H := inputHeight N
  have hentry := computed_entryCapacity_bound N nx ny hN hell hnx hny
  have hbits := computed_request_bits_le N nx ny passes copies hN hell hnx hny hpasses hcopies
  have htable : PhysicalTableRequest.capacity (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny passes copies
      (integerParameters N).T (integerParameters N).S + 1 ≤ 2 ^ (11 * H + 1) := by
    exact (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mp hbits
  have hentry' : PhysicalTableRequest.entryCapacity (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny ≤ 2 ^ (11 * H + 1) :=
    hentry.trans (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega))
  unfold ChargedPhysicalRequest.bits
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).2
  unfold ChargedPhysicalRequest.capacity
  have hp : 2 ^ (11 * H + 3) = 4 * 2 ^ (11 * H + 1) := by
    rw [show 11 * H + 3 = (11 * H + 1) + 2 by omega, pow_add]
    norm_num
    omega
  change 2 * (_ + _) + 1 ≤ 2 ^ (11 * H + 3)
  rw [hp]
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedFamilyEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem mixedCode_lt_two_pow {σ κ : Type*} (sourceCode : σ → ℕ) (tableCode : κ → ℕ)
    (b : ℕ) (hs : ∀ source, sourceCode source < 2 ^ b)
    (ht : ∀ table, tableCode table < 2 ^ b) (key : Sum σ κ) :
    SourceRanked.keyCode sourceCode tableCode key < 2 ^ (b + 1) := by
  rw [pow_succ]
  cases key with
  | inl source => have h := hs source; change 2 * _ < _; omega
  | inr table => have h := ht table; change 2 * _ + 1 < _; omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedFamilyMemoCode
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation







 theorem computedFamilyMemoCode_fits_oai (source target : List ℕ) (N R : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
    (hR : R ≤ inputHeight N ^ 2)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (key : Sum (ComputedFamilyScalarKey source target N R) (ComputedFamilyTableKey source target N)) :
    computedFamilyMemoCode source target N R key < 2 ^ (16384 * inputHeight N + 5) := by
  have hM : 1 ≤ (integerParameters N).M := (by omega : 1 ≤ 2).trans
    (computed_branching_bounds N hN (by omega)).1
  have hH : 2 ≤ inputHeight N := (by omega : 2 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hpass : computedSeedPassCount N + 1 ≤ inputHeight N ^ 2 := by
    have h := computedSeedPassCount_le_height N hN hell
    nlinarith only [h, hH]
  apply mixedCode_lt_two_pow _ _ (16384 * inputHeight N + 4)
  · intro scalar
    exact computed_physicalFamilyCode_bound N source.length target.length R hN hell
      (by omega) (by omega) hR hB target rfl scalar
  · intro table
    have hb := computed_charged_request_bits_le N source.length target.length
      (computedSeedPassCount N + 1) (inputHeight N ^ 2) hN (by omega) (by omega) (by omega)
      hpass le_rfl
    exact (ChargedPhysicalRequest.code_fits hM table).trans_le
      (Nat.pow_le_pow_right (by decide) (hb.trans (by omega)))

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.computedFamilyMemoCode_fits_oai := @OAI.EditApproximation.computedFamilyMemoCode_fits_oai
