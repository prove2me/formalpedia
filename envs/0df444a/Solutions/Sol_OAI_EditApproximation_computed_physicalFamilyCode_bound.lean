-- Prove2me | solution 1 for OAI.EditApproximation.computed_physicalFamilyCode_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:22:17.958319+00:00
-- url     : https://prove2.me/submissions/2ad6eeb5-dabc-4dff-98d9-bf558b4c83d0

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
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea000
import Definitions.Def_OAIQ361V3Ea001
import Theorems.Thm_OAI_EditApproximation_computedSeedPassCount_le_height

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandGroupSampling
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedGroupNumerical
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedEarlierInputBudget
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalInputEncoding
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRequestBits
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedWarmupReadBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial earlier-edge bound for the complete charged warmup
query. It includes all preceding-pass copy reads and pass-zero coarse
reads used by its initial cones. -/

namespace EditApproximation

theorem computed_dyadicScales_length (N : ℕ) (hH : 2 ≤ inputHeight N) :
    (dyadicScales N).length ≤ inputHeight N ^ 2 := by
  have hlog : Nat.log 2 N ≤ inputHeight N := by
    apply (Nat.log_le_clog 2 N).trans
    apply (Nat.clog_mono_right 2 (Nat.le_add_right N 2)).trans
    exact Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (Nat.clog 2 (N + 2))
  simp only [dyadicScales, List.length_map, List.length_range]
  nlinarith only [hlog, hH]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalScalarCodeBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete coordinate pairing has constant-factor bit overhead. The
addresses are computed from coordinates, without enumerating a key space. -/

namespace EditApproximation

 theorem natPair_lt_two_pow {a b k : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    Nat.pair a b < 2 ^ (2 * k) := by
  calc
    _ < (max a b + 1) ^ 2 := Nat.pair_lt_max_add_one_sq a b
    _ ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ = _ := by rw [← pow_mul]; congr 1; omega

 theorem natPair_lt_two_pow_scaled {a b k d : ℕ} (ha : a < 2 ^ k)
    (hb : b < 2 ^ (d * k)) (hd : 1 ≤ d) : Nat.pair a b < 2 ^ ((2 * d) * k) := by
  have hk : k ≤ d * k := by simpa only [one_mul] using Nat.mul_le_mul_right k hd
  have h := natPair_lt_two_pow (ha.trans_le (Nat.pow_le_pow_right (by decide) hk)) hb
  simpa only [Nat.mul_assoc] using h

 theorem physicalScalarCode_bound {M J N n exponent F Q R B : ℕ} (k : ℕ)
    (hnode : ∀ node : PhysicalNode M J, physicalNodeCode node < 2 ^ k)
    (hentry : ∀ entry : PhysicalEntry M J n, physicalEntryCode entry < 2 ^ k)
    (hscale : (dyadicScales N).length ≤ 2 ^ k)
    (hcell : n * 2 ^ exponent + 1 ≤ 2 ^ k)
    (hrange : B + 1 ≤ 2 ^ k) (htime : R ≤ 2 ^ k) (hM : M ≤ 2 ^ k)
    (hlabels : ∀ scale : Fin (dyadicScales N).length,
      (groupDyadicScales M ((dyadicScales N).get scale) F).length ≤ 2 ^ k)
    (key : PhysicalScalarKey M J N n exponent F Q R B) :
    physicalScalarCode key < 2 ^ (64 * k + 1) := by
  rcases key with ⟨key, index⟩
  cases key with
  | inl online =>
    have h0 := natPair_lt_two_pow (online.2.val.isLt.trans_le hrange) (index.isLt.trans_le htime)
    have h1 := natPair_lt_two_pow_scaled (online.1.2.1.isLt.trans_le hscale) h0 (by decide : 1 ≤ 2)
    have h2 := natPair_lt_two_pow_scaled (hentry (online.1.1.val, online.1.2.2)) h1 (by decide : 1 ≤ 4)
    have h2' : Nat.pair (physicalEntryCode (online.1.1.val, online.1.2.2))
        (Nat.pair online.1.2.1.val (Nat.pair online.2.val.val index.val)) < 2 ^ (64 * k) :=
      h2.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    change 2 * _ < _
    rw [pow_succ]
    omega
  | inr group =>
    have h0 := natPair_lt_two_pow
      (index.2.1.isLt.trans_le (hlabels group.2.1))
      (index.2.2.isLt.trans_le ((min_le_left _ _).trans hM))
    have h1 := natPair_lt_two_pow_scaled (index.1.isLt.trans_le htime) h0 (by decide : 1 ≤ 2)
    have h2 := natPair_lt_two_pow_scaled (group.2.2.2.isLt.trans_le hcell) h1 (by decide : 1 ≤ 4)
    have h3 := natPair_lt_two_pow_scaled (group.2.2.1.isLt.trans_le hcell) h2 (by decide : 1 ≤ 8)
    have h4 := natPair_lt_two_pow_scaled (group.2.1.isLt.trans_le hscale) h3 (by decide : 1 ≤ 16)
    have h5 := natPair_lt_two_pow_scaled (hnode group.1.val) h4 (by decide : 1 ≤ 32)
    norm_num only at h5
    change 2 * _ + 1 < _
    rw [pow_succ]
    omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

section Encoding

variable {α : Type*} {M J R : ℕ} (target : List α) (N P F exponent H Q passes copies : ℕ)

local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P F exponent H Q passes copies



 theorem physicalFamilyCode_bound (k : ℕ)
    (hpass : passes + 1 ≤ 2 ^ k) (hcopy : copies + 1 ≤ 2 ^ k)
    (hscalar : ∀ key : PhysicalScalarKey M J N target.length exponent F Q R
        (localOnlineMassBound M P H), physicalScalarCode key < 2 ^ (64 * k + 1))
    (key : Key) : physicalFamilyCode target N P F exponent H Q passes copies key <
      2 ^ (256 * k + 4) := by
  have hk : k ≤ 64 * k + 1 := by omega
  have hp := key.1.isLt.trans_le (hpass.trans (Nat.pow_le_pow_right (by decide) hk))
  have hc := key.2.1.isLt.trans_le (hcopy.trans (Nat.pow_le_pow_right (by decide) hk))
  have hi := natPair_lt_two_pow hc (hscalar key.2.2)
  have ho := natPair_lt_two_pow_scaled hp hi (by decide : 1 ≤ 2)
  change Nat.pair _ (Nat.pair _ _) < _
  convert ho using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  omega

end Encoding

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedScalarCodeBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem computed_physicalScalarCode_bound (N nx ny R : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N)
    (hR : R ≤ inputHeight N ^ 2)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (key : PhysicalScalarKey (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) N ny (40 * smallLogExponent N)
      (inputSmallLog N) (inputSmallLog N ^ 80) R
      (localOnlineMassBound (integerParameters N).M (integerParameters N).P (inputHeight N))) :
    physicalScalarCode key < 2 ^ (64 * (64 * inputHeight N) + 1) := by
  let H := inputHeight N
  let M := (integerParameters N).M
  let J := intervalTreeDepth M nx
  have hMH : M ≤ H := Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
  have hMpos : 1 ≤ M := (by omega : 1 ≤ 2).trans (computed_branching_bounds N hN hell).1
  have hH : 64 ≤ H := (by omega : 64 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hlift (e : ℕ) (he : e ≤ 64 * H) : 2 ^ e ≤ 2 ^ (64 * H) :=
    Nat.pow_le_pow_right (by decide) he
  have hHpow : H ^ 2 ≤ 2 ^ (2 * H) := by
    calc
      _ ≤ (2 ^ H) ^ 2 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hentry : ∀ entry : PhysicalEntry M J ny, physicalEntryCode entry < 2 ^ (64 * H) := by
    intro entry
    exact ((physicalEntryCode_bound hMpos entry).trans_le
      (computed_entryCapacity_bound N nx ny hN hell hnx hny)).trans_le (hlift (5 * H) (by omega))
  have hnode : ∀ node : PhysicalNode M J, physicalNodeCode node < 2 ^ (64 * H) := by
    intro node
    have hb : M ^ J * (J + 1) ≤ 2 ^ (5 * H) := by
      simpa only [PhysicalTableRequest.entryCapacity, zero_add, one_pow, one_mul] using
        computed_entryCapacity_bound N nx 0 hN hell hnx (Nat.zero_le N)
    exact ((physicalNodeCode_bound hMpos node).trans_le hb).trans_le (hlift (5 * H) (by omega))
  have hsmall : smallLogExponent N ≤ H :=
    (Nat.lt_two_pow_self.le : smallLogExponent N ≤ 2 ^ smallLogExponent N).trans
      (computed_smallLog_le_height N)
  have hcell : ny * 2 ^ (40 * smallLogExponent N) + 1 ≤ 2 ^ (64 * H) := by
    have hn : ny ≤ 2 ^ H := hny.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
    have he : 2 ^ (40 * smallLogExponent N) ≤ 2 ^ (40 * H) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 40 hsmall)
    calc
      _ ≤ 2 ^ H * 2 ^ (40 * H) + 1 := Nat.add_le_add_right (Nat.mul_le_mul hn he) 1
      _ = 2 ^ (41 * H) + 1 := by rw [← pow_add]; congr 2; omega
      _ ≤ 2 ^ (41 * H) + 2 ^ (41 * H) := Nat.add_le_add_left Nat.one_le_two_pow _
      _ = 2 ^ (41 * H + 1) := by rw [pow_succ]; omega
      _ ≤ _ := hlift _ (by omega)
  apply physicalScalarCode_bound (64 * H) hnode hentry
  · exact (computed_dyadicScales_length N (by omega)).trans (hHpow.trans (hlift _ (by omega)))
  · exact hcell
  · have hb := Nat.lt_size_self (localOnlineMassBound M (integerParameters N).P H)
    exact (Nat.succ_le_of_lt hb).trans
      ((Nat.pow_le_pow_right (by decide) hB).trans (hlift H (by omega)))
  · exact hR.trans (hHpow.trans (hlift _ (by omega)))
  · exact hMH.trans (Nat.lt_two_pow_self.le.trans (hlift H (by omega)))
  · intro scale
    have hs := List.get_mem (dyadicScales N) scale
    obtain ⟨eb, _, heq⟩ := List.mem_map.mp hs
    have hc : (groupDyadicScales M ((dyadicScales N).get scale) (inputSmallLog N)).length ≤
        2 * inputSmallLog N := by
      rw [← heq]
      exact computed_group_scale_count N eb hN (by omega)
    have htwo : 2 * inputSmallLog N ≤ 2 ^ (H + 1) := by
      have hp := Nat.mul_le_mul_left 2 ((computed_smallLog_le_height N).trans Nat.lt_two_pow_self.le)
      simpa only [pow_succ, Nat.mul_comm] using hp
    exact hc.trans (htwo.trans (hlift _ (by omega)))

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

 theorem computed_physicalFamilyCode_bound_oai (N nx ny R : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N)
    (hR : R ≤ inputHeight N ^ 2)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (target : List ℕ) (htarget : target.length = ny)
    (key : PhysicalFamilyScalarKey (M := (integerParameters N).M)
      (J := intervalTreeDepth (integerParameters N).M nx) (R := R)
      target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
      (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2)) :
    physicalFamilyCode target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
      (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2) key <
      2 ^ (16384 * inputHeight N + 4) := by
  let H := inputHeight N
  have hH : 2 ≤ H := (by omega : 2 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hlift {e : ℕ} (he : e ≤ 64 * H) : 2 ^ e ≤ 2 ^ (64 * H) :=
    Nat.pow_le_pow_right (by decide) he
  have hp : computedSeedPassCount N + 1 ≤ 2 ^ (64 * H) :=
    ((Nat.add_le_add_right (computedSeedPassCount_le_height N hN hell) 1).trans
      (Nat.lt_two_pow_self : H < 2 ^ H)).trans (hlift (by omega))
  have hc : H ^ 2 + 1 ≤ 2 ^ (64 * H) := by
    have hh : H ^ 2 ≤ 2 ^ (2 * H) := by
      calc
        _ ≤ (2 ^ H) ^ 2 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
        _ = _ := by rw [← pow_mul]; congr 1; omega
    calc
      _ ≤ 2 ^ (2 * H) + 2 ^ (2 * H) := Nat.add_le_add hh Nat.one_le_two_pow
      _ = 2 ^ (2 * H + 1) := by rw [pow_succ]; omega
      _ ≤ _ := hlift (by omega)
  have hscalar (scalar : PhysicalScalarKey (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) N target.length (40 * smallLogExponent N)
      (inputSmallLog N) (inputSmallLog N ^ 80) R
      (localOnlineMassBound (integerParameters N).M (integerParameters N).P H)) :
      physicalScalarCode scalar < 2 ^ (64 * (64 * H) + 1) :=
    computed_physicalScalarCode_bound N nx target.length R hN (by omega) hnx
      (by omega) hR hB scalar
  have h := physicalFamilyCode_bound (M := (integerParameters N).M)
    (J := intervalTreeDepth (integerParameters N).M nx) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N) H
      (inputSmallLog N ^ 80) (computedSeedPassCount N) (H ^ 2) (64 * H) hp hc hscalar key
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  omega

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.computed_physicalFamilyCode_bound_oai := @OAI.EditApproximation.computed_physicalFamilyCode_bound_oai
